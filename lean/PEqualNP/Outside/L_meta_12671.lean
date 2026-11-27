import Mathlib
import PEqualNP.Defs

-- The NatRun certificate engine is copied from L-meta-10450
-- (from L-meta-927 via L-meta-9142, Apache-2.0); the tables for this function were generated for this step.
-- Pendant-arm argument adapted from L-meta-9324 and L-meta-9129.
namespace PEqualNP.Outside.L_meta_12671

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_split (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_split gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_split gs w
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

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

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

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
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
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
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
    obtain ⟨t, ht, _⟩ := wiresFrom_split r.1.toList w'
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

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
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

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

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

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

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

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''


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

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

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
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

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
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
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

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
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
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
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
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
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
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
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
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
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
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
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

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
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
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
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

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
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
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
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

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 32 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 13 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT PT : ℕ → ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k (Sgen k cap xs PT) NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      have hS0 : Sgen k cap xs PT cap 0 = xs := by simp [Sgen, StGen]
      rw [← hS0] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)


def fT : BFn 6 := fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def rowsT : List ℕ := [1, 1, 1, 2, 2, 4, 4, 9, 9, 9, 9, 10, 10, 10, 12, 12, 17, 17, 17, 17, 18, 18, 18, 20, 20, 24, 24, 28, 28, 28, 32, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56, 3, 5, 33, 3, 6, 5, 6, 11, 13, 25, 41, 11, 14, 26, 13, 14, 19, 21, 25, 49, 19, 22, 26, 21, 22, 25, 26, 29, 30, 60, 33, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def xsT : List ℕ := [0x24c9aca9f4faf00000000f0787, 0x4b9759571b8d90387180703818, 0x9d3a739a2d1721c3863980c060, 0xf23f83e44ff80e03f83e00ff80, 0xffe403fff2200ffc003fff0000, 0xfffffe0080404fffffc0000000]
def NNT : ℕ → ℕ
  | 2 => 1
  | 3 => 68
  | 4 => 449
  | 5 => 1104
  | 6 => 675
  | 7 => 53
  | 8 => 1
  | _ => 0
def HTT : ℕ → ℕ
  | 2 => 0xe6e8bd84
  | 3 => 0xff27a6d5fdb8098bfd9c67b5fbd66094f7b487f8f67783f8f0de213cf0dd936dedd6d905ec755f7fe81353b5e1f73d1ee11b0389df9ddef3dcdff589d7b4592fd59226a7d2290effccf154b9ca37b7aac71dfaf8c6fa14beb21830ecb1e29fd2b07e7b2fae9a4621add04295acea9e3ca94be663a873dbcea4dbba67a211d4c69e1177a78e0fd8828c24d9948b9edefa8a144b987eeb36ba74990109704cfdd86c47d8d8636123ae61ee68b45ed3ddb25d2475095cc94b3b58252c1657d1ca034d06f75a442c11ba427c7ac33a2c745e34274cae3385b2412fabe71f2ec5ea71267871f7251a25fa22b1464f1e9d66e11dd5a7d119040425190376561882fccb0d272e6909198edd06a0078d03927a27
  | 4 => 0xff1df432fdffdb66fdeb1157fd29474ffccb549cfcca2525fc374d16fc011a9dfb9e9afafb65d8cefac729a1f9a1a904f7ce0e70f754f7a4f75469d5f6e34d99f6a20843f59996f1f5593d10f539b985f50f7deef492a2f6f3f2459ef3bde21cf3637acbf335681bf30a8794f2a6d0bcf27bd01bf1c9373ff1557592f11a269af0de213cf0dd936df09eeb50f0499d98efdf30b0ef218068ee35e81bededbf7bed7fceeced079541eca4fd51ec644e64ec27154cebb5bfb9eb9a9beceb7e0dcfeb2e0139eb22ca54eb223c85eaa2cc20e8d08932e8b34c06e783df19e702d1a6e544e47ae530f9e7e4000945e3a0eae7e1136ededfd3923cdf16cab5de735837dcd8757adcb9d58adb6c4986db582bcddb4a1e3ada8ae379d9ea12b1d9748884d952be58d9180a75d90b7522d816f71ad7f081afd7627e36d7317258d70b9ab7d64623cdd5b14056d4f3fbd4d337a24fd1a23a97cfc76c4acec651bbce1b5ba2cdb704becdaf9d0acd4c47a4cd1d85b4cce99b0aca4b26e3ca462edbc9ea8cc1c9d44bcec85ee143c823bab4c66ddb7ac51c9d31c500949ec4257bb9c38fdcd5c30a70dbc275345bc22e9b63c22e0d94c2059731c1c61927c194f40ac13a0c07c0c0dd67c094ea07bfd53204bfa1d86dbf5a6c3fbf321588bf3187b9bf165305be156e2abe04c2a4bdcf318abd7583ebbd155d27bc17a71ebbd26103bb5ba32ab9d34608b95cf0cab8d72ff4b8a5b6d4b7adaf58b6b2dd88b6a0d5a8b659762fb5e3bd19b39792cfb3613a4db34cc477b2a03749b2053d38b1821dd7b17f99a5b1707089b131007db1177cc8b01ca49aaf3a43d6ae5fe547ae3e744eae185fbdadcdf286ad5dadbbad268342ad2028dfacd12533ac90bf5cabd3e4beab11bf6baa856204a99d7b9da97c57b3a888ab2ea82b1ff5a6bb609fa699be43a5620fb8a504be7da446715fa3abb314a39da121a39bd574a385cc0ca2e23a47a2a15ab4a246c4ffa211d4c6a1c0b4269fd5ebd29fb4aadd9c805cce9c567dde9aefd6ee9ae48df79a4068ac996876b79955fc2297e277f09734895b972adbe896e4b1f896d30ad096be3d69959d2be8953fd48194f208ee945f33c59419fe599415cbb19042b7a18fe910eb8d44003b8d28db928cfb7ee98c4db9708b11ec768a91913e896656b988408caa881acb788794802085da0e18851febd883e74baf83ae01da83ab1b9982db6d13829cb688818b4164814aaaef80ed42e280c11cd1806619697ffdb8827fb0e6bf7e3a193e7da66c157d9420447d4ef8db7c628b887c34aaf67bf3326b7b77be3d7b6096827aa1ced77a62293e79c11ea679865b00796191ad78bff74078346a90772950647728e7de75ba6e237584170c7572968d75162f0474d0fc2074002f7073ff177b73e5081f73cc1cd572c9f40a726525cd71b62b6571a59e87713aaeb9708dcdca7065c9126fb4e77e6f6f65ec6f05189c6e6018ef6dc106a86d7749046d234cc76c9816536c5259996bdaea076bb52e596ba3b6ba6b300dd06afff2206a8941826a67f83b698d83b768653f1c67c32e07668f91d666709a4d63d7abe061ee68b461b26f0b61ac42a2608fe354603e04865ff4e8945feba8df5e3e49245e3dbb555dd8b4015d8d80ec5d1a04cb5cda5d925c3311cc5ba109b65b386e615ae659fd5a4ec03559dab8a259c7ec4c58c75ffe56f5023d5665f6f1564e5eb0564559e655ea09c65350807652c189f5529399555283c04251e33de750a47ad74fa0896c4f788c064e73774b4dc6183f4d948b3f4c649d384bfcd8cc4bda4c8c4bd934974b29bc0b4a7a003d49f7572a49df062c486971c2462ad8a946190616456ae1174461c5034407bfa042da5f3542da0f3c42d6acb9419e75aa4167a0d3411b634b40da073040578da54013de663e4ab7693c76168b3bb1c8fc3ab6008c398c8c27384d20e1378d15393622bd87361866403617d87135c9acd4357fe9e234394173334b85d93228dd5131da7a6b3180b08630425d003032daee2fb1d0592fabe71f2f969b6e2f433b3d2f0e524f2eb268ef2ced140a2bbb58eb2b4bbe442ac6a8dc29f0903729c9fc4327ed85e027c28515277aa68826fd51d72655488d2565bf9824f0080e244df05a24073f8523987c50238dc549231a1fa722664d6d21825d6d1ff3f1591fc1f9ef1e4c3b9a1e47601e1e0df61f1df0a3481cf0921d1c6e22ba1c3be21f1c18941f1c1806501b895db41afff2fd1accb3a51a40893519ef1a2819eddfe819938b2f165bcb0416428adf1635948e15a5b1d5149b40f7149b409b13eca44e13dde88b13d7bbab1386f6bd1353e4221338424c11ff139f119bf6b3108da47a0f6732550f26beab0ea630d80dd0c8f60dbc0f550d16ddf50cfb6dca0cc58a7f0c37040a0c2b36e50c135e8f0c07e3bd0bc633500acbd988091f1c220891744e076afc9e06a0078d064f2eec05533cfa042dd400039cb4cf035802ac0322d7b202ed70a70239c51e019db0d3019a6b6d00e4b0a5
  | 5 => 0xffe4800dff9f742cff559257ff3392c5fec811b7fe803ad3fe69c969fe65add7fe1bf41bfe039c23fdf915c5fdf29ef5fd624696fd355daafcdb07ddfcca2525fbdb1aa7fb93bb2efb840725fb5580c1fb1e0218fae0bf0cfa8cbf07fa7d603bfa3c38caf9d1d25bf9197895f8f945a3f8d1d7cef8870976f87765b6f8240de8f7e93c8bf7c66dc2f7c60d1ef77391c8f7174459f70ece3df6ffe56ef6f27d8af6b9dea4f6af4970f66b457cf65f4ce9f6560718f5d95fa4f5ce9acff378b94df3637acbf35e2d92f351df30f3083785f2fefd8cf2bf5335f2a912d7f2a6d0bcf294bbfcf1d71e19f1cb045bf1c9373ff0ba41b4f0858db5f066264defdf30b0efbfa703eedca098eed7c09cee35e81bee2440b9edbd98aeed8c5c41ed7fceecec27154cec0ca617ebd40342ebb2515eeb3e796beb0d78f9ea8fd666e9f61eefe980b65ee953e744e933c1e4e8e08230e8dfddf9e8d61a73e8c0110be89912c6e8594c49e8235ddee7c47804e7c338ebe78109fee75219fce744bd85e6ce09ace67cff77e64e3318e5f681dae5e4df99e5d32a7ce51030d1e4d11836e492eabfe44785cde4179e5ce415f9e2e3edd1bee34dbc9ce3172cd7e2e82236e2b35663e2ac6aa9e29155f5e2783d5ae1c39530e1baa1cde19bdcafe187b49ee183a625e11e2ff7e0c2fdd1e078b8d4e03a8bffdfef8f25df818381df76b4acdf6ef789df065549dea6adb1de8c2ee5ddfabbd5ddfa13f2ddf19ed0ddcb900eddbb269cdd9f237add8e83abdd6bc7c0dd1cbcefdcb3e401dc6ece5adc6520e7dc2a13d0dc0d4fcfdbd5c8e2dbcec8aedb9c4214db98bc47db3de251dad713cedaa1e944da89577dda7a1980da66ba87da4a495cd9fefa8dd9ec9161d9a436ebd9748884d8a940b6d89cba33d8774d47d7efd8eed733d89cd70b9ab7d685bb94d65ccfbfd643e685d61a12fdd5ad22d2d5937da4d57cfca0d50453ffd4eec15bd4bfbe51d4b524f9d4a32333d48f63cad4813cfcd4588b4dd3b9319cd3afe764d35b09aed27e453ad235c3e8d1e12d96d0467b58cfda506ecfd1db57cfcbd63dcf8a4899ce8aba6bce56134ace484640ce2f0eecce2898aecd36db67cd118b80cce99b0acc8ec522cc7d5db0cbfce116cb1e1971cb1c298ecb145317cb08e5d1cad94600ca5a30d7ca2b27d2c9d84e42c9cf21b0c9a10201c9175ab6c8e56098c89712d6c880c71bc823ee79c823bab4c805c369c7d9fcf4c6c8b47cc6c58663c684efeec67a1a3bc61f00d5c5a05e68c569f2dfc537fd81c4eb2bbec4e4c86dc3b68a67c3745e3dc3582d87c33c9d40c32cebb8c2e0b114c2b66222c26efc39c25041f5c1b76f17c16eeff5c12d776ac0fac508c0bd1789c0490882c01d2b8bbfdc13d6bf9c6e3dbf53c5fbbf39562fbed04913bebf07f9beb8a4c7bea744e1be7d66d0be36a1babe3324fcbdf817e5bdc6fa87bdad4798bda6d988bd6eaf8fbcc23ab1bcb6a26abc98a9e1bc89dc67bc639563bc632cddbc17a71ebbf1bb78bbd3c338bb523833bb4ac5aabb26d58ebb1c5832baef4f66bac8befebaacdb8cba90056aba7b0998ba6b7311ba507403ba0b411fb9e6f96bb99a8e28b975f9cbb94aac42b93cc67fb9395c7ab8881b92b84fe728b81d0f8bb814a91bb8043909b7c55cbeb7b4e5a6b7adaf58b6f57feeb6f409a1b6f07064b694e581b674f3b8b649508ab5e3bd19b5cc041cb5a5ad2ab56eccd0b532842fb4ef2c7db4e71f73b4a9aaebb43f5d9bb40ce53fb3f483a7b3cc83cfb39a5deeb3841359b3765f30b2b18e03b2922736b277dc2ab270d89eb25dc72eb240d7a3b217f06bb1d917a9b1c7959db17e5407b148326cb0ddfbb9b0d898ceb0a6b729b06a52cfb0516a63b03a371fb02ff1daafc38681af19797caee874b8aed8b561aeccceddadd72966adc3babead8501e0ad7957a5ad6d9ac0ad15cef9ad0ed454accb1c53aca74ad7ac939937ac53dfefac4a1622ac40eb0eac28d8ccabd3c900abaadf4caba59b84ab93bb1eab4580b7ab382116aadbaf13aa9a9f0fa9fb0e57a9eb5ddea9d0f29aa99c50a2a8e0def3a8848e4fa88037eca84888b7a82278b9a7fab093a7c87cd0a7b79cf6a6ed3ddaa6ecb40aa6e687a1a6d01d3ea6b2311ba6430066a622635ca5ca2853a5784985a55f8f03a50aac28a4f70a3ea48fbec3a47f3054a4561b3ba3d6fe32a3c3c682a3531f80a312f900a2f646aaa2464a39a23c7117a21687c5a1f1e957a1dff06ca162722aa12c6639a0afceb5a0712ff2a050a1e2a049fc85a038ee4ba024289ea00b6efe9f8905349f14fda19f02314b9efb73729e5437579e0466e89d51f6d39d440ffb9c9840ed9c63158a9c2f473c9c19f2a49c0952f59bf6ffa79ba823599ba7f2349b81fc7b9b5325f39b3d8f569b244ec59aef5a5c9ae5ce939ae48df79a7ada80997434db9903d04698b1bbe2988ac575986083f49823259e98180bbd97efd6d09734895b9719bd019692c1e39677af009601f3fb95dfda5f95c4080995854a569580f6a49579b0f094e802fc9494e257944053a593d1428093adbc4a93005d3e92fda0e592ced03e9292c663926a22869256b56791c116879190cfd091371dcb91137996909391f89064010a8fc8b7758fbdcbfb8faf48898f8f02c28f70513a8f43eaf58f319c298f1e0c658eff5f728ec7fecb8ebca90b8e6f029d8e236da68da3b6c18d9c4b668d8fb56d8c0acffd8bea4a3a8ba15e528b2f5b728a91913e8a6b9b6a89df236e899c0a02899af20d894492108942049f892a4338885c948b885841988814543b880fc43387e7df9787da0a92877f5d24872f917a8719dff286b2c4c086acd032869a8fe78655a84a8601a3a485ec1d7785893313856b9170855f1efc855374c1854e23658486f28f84599d568441a7e28437b165842dfd0b8401d2dc83ae01da8384fc68836eec50834cf22b833642fc830d8f2782fa055a82d45c3b829cb68882798b8f81c57afa81766dbe814aacfa812531b4809bccb2805eab6b80141c007f69d78f7f4e8f007ee45eba7ec6d1267eb7114b7e3735237e23537d7da66c157cf2c87c7caeacac7c96db567c7a5f827bde13967b77be3d7ae1fc7e7a553f1b79adea29797386727904393878f07b6a78e4651078cefe1d78a5de567864dc2277632250775576317732408276baf58576642ee9755072c875162f0474d0fc2074d0e06d747e89f57456d7437448974e73ee1f6c73ecadee73c0ee03736c790673623f1a731ecc4472d451cf72c9f40a727e35557269480e7227590971a1f8227086b5cf703aa1107000eddb6fe7954e6fb4e77e6f192eca6f0441426eba1ed66e8eb97d6e14821a6dfd95116de745746d9f00c36d7749046d5f67726d095c6b6cfcca146cfcb3da6ca213b16c37b7a36c3796d66c35081e6c09465a6c01d1836bd044686bad876e6b79d33a6b5f4cdb6b4f5c346ab9991d6a7d43f56a2a4d0d6988355969852a47697524e1693882436921eaa868c80a48688503826882f09b681d1e5467e068a267c32e0767a0926c678ca1336743111c671404236706b90d66ff47a966d97c8e66bca26c66b982bf666bbefc65de4c5b65887da7654dcbbe652e365864c6ff0564734cbb63ea109663e4ed19638680996381a51d632ae847631bb7f9631247fd625d28ba622ad71c61ac7e9d61a867b961984af261895c186176271e61750f29611eaf2c60c5969d603a37fc600c148c5ffd59575ff4e8945fd79d2e5f7ace345f767f0c5f1a451d5f18ea935f09ae965ecdd02e5e5258215e4be09c5e43b6dc5d63502f5d5b2d4c5d044b815cf7b3535c610fab5be20b655bda8bfe5b61a8815b52daee5b209da45adff6d45ad422765a4ec0355a48c52d5a0a1e4059e36a4259a39a3258e5858a58c9ff3f58c75ffe5875e9ce5872874b581da74757bab242576146de5739589e56d63bb256d1905a568f27a2562f282f55d9790255c7e97955bd71ce559e6beb55052e0155014fd35493694d5488c9c85480ebaf5322be99530c0916530b0df552d3032252bc199a52b51966525122f4524c33935235b2c95201f62651ffcf7e51abe4c15198b324518c5c3a51714909514da38e514228bc5100784f50f0aad4501a17b25017f03a50061e874fed193f4f38b0224f2f934d4f1b5b714ec28fc94e73774b4da0c04b4d948b3f4ce95b714cd9aa6d4c9ad2dd4c80ef724c1def154c1b48714bfd4b9f4bfa60614bf29d554bda4c8c4b9b0b1f4b8973eb4b7a771f4b29bc0b4b29789a4aef34ca4a7469f64a737a9a49fe8c3249e51af849cbb289497cb1e74975ff4f496818ff4950e5a44933a3774929d56748bd3f5e48b820634880801d4827b5a647d934574779316f477654fd47740a1d471edd0b470e3f3146d4b06c46c6f6e5463a65db461ef5a44603bf2a45791ddf456e652344f4f26a44e535ef44c18dd1443b050c441a6e314385225e436a23504344ac1e432979504324f06c42da0f3c4293b6394288ee9c4275bd6f425f531c420599a042046a2941a271e14171921a416827654167a0d3415bd48c411de85640d7f34840abbaf7401853ff4003628f3f6ed0d63f66be4f3f5cdf613edbee083e4ab7693e3fdb703e08dbca3da6ac303da514ce3d8960723d5854693d4ed4043d1eb8543d0853743c8f3ca83c8eaed93c8df6d63c5377983c517bbd3c1d929d3be1daea3bcb3d503b16f5523af2c6f63aec65193aa1a5333a34900a3a1b971e399053e8398c8c273972680e392c8aa23922ec7839113c92389fb3b937e631a837d776733779a45936f0d8b336af6d5e368fba96365a52c2361866403617d8713617225335d9305435b68dfb3583e29c35666145351975b434de689d345bc56c340eeef733bbb668336c803332f57d3b32cc840932c3743432ba13f0329fb7b0325ccaba325649b6324f12f83241da453228dd5131e77a6931df425531ae49e13189a1ca316448f231615a50314dd37e30fb42df305d0f58305c81892ffeba112fdd11242fa1cc332f93c1f52f3637e02f0e524f2eabfb412eabad762e7f8e452e6944be2e65780c2e48dce02e3d649d2e1e03062e13d38b2e0ace362dfa23642d0fefa82cdb6cef2c6d86692bf97ed62b9f3a5c2b8fd2fc2b64c75e2b0593032afb83132ab40e602aad203e2a30598329e9fc962979c31d2973963d296f2d9929529d9828a2b481288fc9ce284301292804980827a74706279ffe6e279cf2f8277aa688276de6a4276014e1271b544a26a7497b268b90c026297f0c261ef8ae2606c59c25eb290b25d9f7632598becd2566ec2e254e9bea2542ac63237ba5cd22c951e622b9490422664d6d2211ef7021daf0ac21d546d221b19542213f5b7e2118f45420fe067b20def08820c3ed8120b1ebd220a68e8a20a4f5bb2099bda4209585fd20923d7f206031ea1febf0071fc5287d1f7295ed1eaecd881e9dedae1e9aa5f11e7d9d551e7154111de1439f1d513c1e1d48823f1d2ac6b31d261c0b1d03aa221cc76b971cbf530b1c8e5ab71c45dfbb1c3be21f1c1750321be87f8b1b7da9021b1ec93a1b19a3931b0b26381afff2fd1acef5c01a909ee61a4fda8b1a397038197db05719705afe1945f60318f3dd3e18beb24418ba41cf18ab709e189505a417f5551c17f2711b17b2c5081787fb9c1761882f164a23a2162ac63c1501b14e14dbef7814d25a761498741914490abf140ea1561348b150133379d412ede6e811a04a84112e038810308762101a65b80fc3fc610fbb951f0f9425100f856be70f8073df0f6732550f24d1c50f018a370f0172e80ea2e2600d98b9a90d5dffb80d1b82290d1a04840cf471250c9eabb50c6d68b60c61aa880c3bdccb0c2a6ca60c1a50d00bfa29f20bec613e0ba8207e0b65978b0af163170add064e0a79d4cc0a55aae80a1b938e09a9890e098866fd094a814c0927f09a07e0807307af795f0768e06707685298073fdc3506da41c706b3bb5e06b211ce069540e506520acc064f2eec061781b905fb226b05e901da05c506630599e03c05963bc40591aaa9058950cd057f456b05624f390527223f050f770804f7c2e304dc1d7104aefb670450980903ef303e0379577802dfb01f02b18d8002460d9a018e728a018787d8018628ae0151ec22014db359010ca60700e4df4800ac2b7c0095e82e007cd19d004fab9e
  | 6 => 0xffca4a69ff213e6afed4d327feb03ecafe65add7fe0b5793fe039c23fdf915c5fdc26091fd57548afd4eee1afcffa1bdfcbd3905fbcf2a80fb1e0218fadff229fac17ab0faa911cffa6cc92efa216472f9472a3ef9197895f8be5858f8b0a42ff85cbe71f7c60d1ef7b22129f7ab1d9df77b1ca2f752356af701da9cf6b89906f59c1435f58baf62f56a36d9f453be7bf40713dcf2fdffbdf2a912d7f2a7dfbff2491953f1cdde36f18e24eef11d462df0858db5f07fc5b6f015f412efd4e40eef25a2ddef0b3799eee631c6eed695a1ee2440b9edbed34eed5cbdb8ed34f592eb9c7686eb9405a5eb89ea5aeb7d4565eb5ca85bea44f127ea314f3de9b97553e990603ae8a3ced2e88d647fe8308ba9e7808f38e776b616e74a9f9fe72c2e56e69cb729e67cff77e666ab38e5ea13b4e5ab74f1e5844184e4b06ca9e44785cde415f9e2e34f1bf9e27e54fae183a625e14397f4e0e23733e0e02008e08d6af2e0201392deb0d20edeae79dade8c2ee5ddf19ed0dd9f237add7b4a81dd5250bcdd2a1bcfdcb8c6e5dbcd06e2db8bdd41db3c38fadafe4d08dabf8f55da2247fbd8cdc913d8a80d9ed7dc5b44d7a46785d77be4e1d6fb5b86d6cb14cfd5f91b02d502fc74d4f810fad4c947c1d46b7600d3a9479cd39a6049d324ca73d2d69065d1cd4bbfd1248f39d0dba351d025c41bcfcbd63dcfa1a7a0cf19686dced5370cced0c5e4cec9e11ece648837ce30b988ce20d51fcd96d98acd928697cd763151cd222496cd144f91ccb9a223cc57906fcc4d0a11cbaba2d0cb266276cac37812caa5d66fca8db9c0c9c1378ec993e255c968420ac8a9314fc87e82d9c847d426c80ea13ac76d6ce1c6ffbff9c6b0b2bdc670cf60c65f76b3c61a016ac5d611b1c598f06ac5295837c41ea3b9c3852987c35d987cc2e0b114c1e8f1abc1d12055c1cd34c1bf4af3cbbe2ac069bde02355bdad4798bda49564bd9f2121bcfb8965bc8fbb30bc783505bbf1bb78bac975a0ba8ab7c7ba6b7311ba0b411fb9b8cef4b9a9757bb975f9cbb8a6be05b89c8419b8591143b814a91bb7b87a54b6dc3d21b5a5ad2ab4ef2c7db4d0f3c3b4b01c29b45373c9b433df53b3c8fe7cb3765f30b3218a73b2d945c2b29b7a19b299ac71b269ee2eb240d7a3b236f8d9b1d917a9b17e5407b1438b59b10a8967b0e7cc6db0b41839b09991dab08de79fb089a133b0516a63afd79a71afb788f4af686fe9aeaf69e0aea47644ae5c2fa7ad6d9ac0ad576353ad1aada1acffedd8ace02331acb0e09cac4e4922ac45931cabf3c7beabf317c6aa8810bdaa7b66f2a9245595a84c8cfca6e6c39ca6af5428a5ffdb9ca5379e56a511e22da4548a1ca3d3049fa386259ba2f646aaa29d952ea295724ba19b54aaa11c5064a114d0fda0712ff2a05ae2a3a038ee4b9f8905349f1daf419edddf319e5437579e04443e9db02ecd9d57ec469d440ffb9cf4f7419c9b8bdd9bc96ca19af7b6cd9a162c7d99cdae4c99c30ec79823259e980d48219786789296e629c09692c1e39580f6a495545cb195275e3e9469d84c93fcd4c893adbc4a926a22869223a0709213ef6c91c1168791bb34719158341491558d709137909e90d5501e90b4bc1e9064010a902979c98f8f02c28f1f5ff78eb6f6e68e8b2aa38e6f029d8df7845d8df265628cb3766e8c59220a8c4884308c013be48b3e04298ab362de8aa8aa228a2f37698a1f7aee89fbd2d088bf675d889dc30d887ef11d8863be4f8814543b87c9ee1787c3339b87b0026e879b828986dcb6e086689d6785e5fff685893313855f1efc855374c1853da78e842dfd0b83f9a17683e0328a83b05cac8384fc68837a206f830da3c582e0f12f828919038258fd538211476d81ca537c81c57afa818dbc9781766dbe8094cbef80513a51802d0bf58026aa187fd248537fc33ca67f94d9d27eca98e77ec6d1267ea55eaf7dd9f8b87d11bb727cf44bf47bc18f0c7b9497c17af0d2fa7aa0a6447a6a062b794933f678ec777f783a2d207806c90877d9fcaf77970fb9776322507737be7d7721bf6876e88ee076d57dfd769e8df17688187d763587de74dc113274ce06f473e6404073b9d34473a389bd7377a99c724a34a771a7cb68714a3af67133c3d570d97f5b70b390bd6fee535f6fe7653d6ec5243e6ea972986e8ce2976ddcf9806dca0ecd6ce18c056cd737f76ca82ba36c9a59e06be18e7a6b9804476b63c40b6b593dad6b143c626aa1312d6a7cf1626a246fd0680396e567a0926c6795859466ebda4166d97c8e6626d7f765ec30d165df3aba65d402a365cc827e65b3cacc659a76e96526350664e6b62f64acdaec63e4ed1963da269763d4eaf06311e9516282c73e6260610a61f9980a61c89fb66176271e614af8de611eaf2c60be16d260b7ee0160590e3960150ad35fcae3e55f8a1f8a5f09ae965de2f70e5d63502f5d2f9a1b5ced0a075cc2f6e95cc2409b5c610fab5b8468a15ad422765a4ec0355a16347759d2b91859a3b79c5948e6555875e9ce586dbed357a7f94756af992356554841556acc615554aab754f8b9f354ce6a0f5488c9c853dd275f53a7690d52bc199a5281f15752544983522eb62451a7adb5517621ca5164b1a551346ef150196f4650174b4d4fca620a4fb419cb4f8fefe74f2f934d4ee3ce0d4ec2abfc4e6fcd774e6235994e03c4c44c1486c64c01afcf4bfd4b9f4bec56cd4bccb05d4b9b0b1f4b8973eb4b51c6b84aff4b624ab98a6a4a9c94384a61673e4929753d48b39c774882f51d47ebd27f46c1ccd74687f858461f244745b7169c458a4d6945791ddf448fd75b43ba7fd743a40e6d4356391f433de12743335ac9432ce3f942311a4542046a2940be4c29408fc5c53fb7a53f3f767dce3f66be4f3f0c175f3d00b2c63d0052223ceb579e3cadd6cc3c4913413c2cc28e3b9991ed3b904c1c3aec65193a58d4623972680e389fb3b93839429037f9983937d7767335b447aa35a06b51351975b434de689d34c2d9db3462637833b71126335e85bd32c6a14532ba13f03228dd5131615a503151f49730ec96623078be6f2f3063f32eb3ca562eabad762e6e06e82e6944be2e1a22fd2dd357ca2d93914d2d5da2e22cfebd082c8826372c6d86692c084eb02bb7447b2b88781c2ab503f72a3059832a0b5d3a2981cad129503ee6293e0f06293388a8292816c228a2b481288801a027e6afad27b2825e26fdda3426d621b326c9de1a26bdeb292574d1032529d42924bbc88524a93c8d2453eb7823c673e9233458f6232be3d42305d5122300800122dcbe1422d9687e22c951e622c8c8af21ee290521100de620d6871820c59a5320923d7f2082a15a1f26d6651ede7bef1eaecd881de385ba1dd6ff371db1924b1d8387991d48823f1d2a1df21c45dfbb1bc000981b7e2b891a513feb1a4fda8b1a3e99031a39703819fa035519eeff6b19c9a8ce19bb82001992d051195eb39c18f376a017f2711b17789c5916ce78881580c05c15149572150c205b14655a4a13cd122b13c4ff6f1390584e13828b44136953f0133fb5f212312cc411c90a2611b7725a0f81f8b00f506cc50f1293460edb47050dbb0c1f0d5dffb80d1441f80cbe19080ba337e70b3f4bea0aa437e30a79d4cc09c6a1c8098866fd09405965092c11b30927f09a08f0cf6b08d9965d0892728b06f3a805062b6abf061781b904739b33040a8e1703f94cfd03e189e503d5ce4803b7abd40379577803325ce902dfb01f01d2eee50151ec22014db359007cd19d0029946a
  | 7 => 0xfeb03ecafd4eee1afadff229f8b0a42ff85cbe71f6b89906f58baf62e27e54fad7a46785d6fb5b86d3a9479ccd763151c968420ac6ffbff9c6b0b2bda29d952ea19b54aa9f8905349db02ecd99c30ec79469d84c9137909e8ab362de8026aa187dd9f8b87d11bb727763225073a389bd71a7cb68680396e565cc827e6282c73e5f8a1f8a5d63502f4fb419cb4ec2abfc4e6235994b51c6b848b39c7745b7169c433de12743335ac93d005222335e85bd3228dd512bb7447b2981cad129503ee626bdeb2923c673e9232be3d422d9687e007cd19d
  | 8 => 0x77632250
  | _ => 0
def PTT : ℕ → ℕ
  | 2 => 0x2313
  | 3 => 0xf2321000213310001d231000ec3130005f331000123320001433200008302000d33210001a3040005f321000c030300008342000e1331000743120004c3320007e3310014633100091331000af33100006332000d63310000833200146321001253320009c331000bb3430012c230000a67310009a342000a663000006312000403420011631200051332000da2030009934200091341000bf343000f9331000cf3210005f3410002a3210007c3320005434200023212000052230004d3420008a3120005134200027341000773320006b343000d02430004d3120000034100040332000673210004b3310005e34200070341000283410004534300070313001023130001a332000003010000e321
  | 4 => 0x35b332000a6313000452410002f332001292150004d3010012622500224304003892030038a231000243320011a243001102540010f2430010e2430010a254000153400000833200224350002913410038874100103250000fe2530021570300008301001a0203003183320003e330001993010000a230000f5235003fc205000f3232000f2232000f0253000ee2540006f210000ea235000083210011e332000632100004d3510003e350002093500005c232001e62050031525000203351001ba340000d4243000d32430005b220000c32540035b34100219304002c7250003ed221002d433200040323000243510011b3420023634200238240000083510033e205000653410008c254002f22210017d22300085254001af2120001121000052203001c33300037c2040007d2250007b2430035b3510002f2310000b221003dd3400029f7130004f341001b6250001862050000c23200197302002aa250000a96240037e221001fa3200018b25100003202000492540004824300046225002093400012e7200004125400035253001ea301001b4730002ab3310012d2050029f743000292350002824300027243000262540005e34000045332001f02150001e2530008020500014225000122540020d3520003d3210002a34100010251002ac35000024341003f1340001443020034c221000072520000525400002251000263320010d35000008341001bc250000653010011d25100093351001df3510007033000268341003e0205002e5221001d4341001cf34000349321001892140000021500353215002403510043a3500014d332002eb20400250350003953410016f3400029c3120014e2500034f2410029f712003427130018e225000fa25000056351002bd203000c02050014c330002883130023235000216351000c5251000a1350002b93400043a340002267430028f251002f334000135232003cf250002683510012e3200012c3410015522100320221000d53510011133000208741000ce2210014b34000196731000962500023f3500015a34000197343002c8331003bf25400422204001f6741002bd313001657400011b2140014735100196b1200264332001c2342000112410021e321001b0351000bb204001c3340000f43120020535200221204000b32430014b33100144343000b82140029c3400002c210000be35100271332000c82100008725000353214001813510044f2040012e74000269321001923500003e340000b231200114350004033400011a34100100640001cc3500001b202001b47200035825200161351001c3350000cd703000f2741000f2640002693500034425400207250001453510025325000097704000062500008a2210013c35100157a02001403410030620400122232000b32020031b250000e6212003212540014d3420004f3210007130100144352000cc34000192330000642140010823200269340002ad205000a9721002eb250002713510015f3500011234200111351002f3350000a96200012472300165721000533300014b350001197410022233100165321000a3221001d52150014c350000e13320000622100356350000d4352000d3352002c52430014b321002b22520014733200145332002333510028821200245313000192010003a2320012c35100013220001923210012eb2000233314003fc204002a2235002623210006635000219305001832300011433100125205000a9723001873130001f221001d52140007223200169232001583500007b312001ba32100068243001473410004a340000cd7210004a3500024035000228204001fc2030007474200199323000663400004f2320018a20200196741000eb205000ca20500215724000952500024b2540003d2430027f31000173321003553010002a2320011434000047723001967120002831200027301001af2030024030400222254003252050000121000143343000253500007232100065351000ab250001963120019935100181342000cd000000153500012c33200330240003602050005e35000181323000ef33200114321001f32350008f3030008a324000de3320029c350001e425400158340000bc30300214b03001de225002033320009700000070331001cb2540009c331001c6254001c5252002a72040005225000097721000a22130007400000063343000ad343001f73520006d000001d7252001b2253000ba252002f62030018d3300006225000055330003062050019f254001d9721000e02400008f313000b4332000b3313003f135000262340000a3230001313210015f340000a334100047000002a72500030c2500015520300053331000747210017a254001782540017424300275350001732540003f2510005e3120016d25400378304001aa204002ac3400007432100020000000a02050004d3320001b25000065332000643320014625400086320002683310013f25400074b21
  | 5 => 0xeb350000ef723000ab2540006e7140008e101000aa261000a92650004e210000a82540000770300069210000346200003a360002143500023c206000a32430010c360001c4360000a2215000a12350000a301000026030001c250000537250000ea210009d2630008310000034724000496250000d33100003724001f6604000093320009c25400056210000992540007ab21000982540002c2060000e71400199204000d93510000b20600014a50000536210000d3500014a33000214360000ac3300001f654000a42060018f340000902160008f226000482100009e2400008b7500010062100003703000052400002d360000093010008c26200053221000e336000082b020000d3210027624000001712002652600008525400084243000822250015f604001ee3600007ab300004d604000f6651000613500007e24300255340001023600006a31200002704000792510023d2600027a3400003eb50000772310007621300075254001c3b300001f62500003652001d560300072252000016100007026100002b310009e640001b63620017f2210006d2260007b20500024210001f0753000232100006821500066243002613210015a3300006436000044b41000c62310004da50000632120012f36000062262001f6a04000017130010a36000009361001ada500005f216000536040005d235001caa300005c221000b63500003920600018210000e0730000592130000e6020000e72500195a500001221000052251000fa2060020b36000051265001823500008b720001a03610006434000050212001d2b300004f2610016a331001a7704000bcb50000536030002233100065331000e5f2400252a01001d37530004b2360000e6240004925400036203000472520004626500043254001917400004225400041251002112130000e704000e6a1400206205000e5502002243320003d2150017e7040003b253001d7206000bba52000392260003823600037265000352650002e2050013a25200049624001b036100191b0300031263000302160002f2250014030100034a520002c2160002b2260002a26500029265000827240008aa0500002724001f62040002626500186331000e5e020002d350000e5f210008b7300012b2040017736100122203000537230002223500175351000212530003eb2100125360000e5e24000202360027d2050001f254001ff2030001e25200191b50001042600000b2040011426200215321001697500001a22600229321000496230018926000013265000d13400001126500002b500019e3310002b3300010d252001323500007f3600002d330001466510001f6240009ea40001dd2060004a35000005a400004736000186361000021000000d2540000c2540000b253000e5e210000a265000082160001c3320008ba5400006216000027230014b3500004f36000229340001a71000027f3500000426500276a4000043260001e4260000032520001b30100016321000dd250001cf3600000934100087252000002650003ca04000983600016173100082a2500060221000b0260000a72600008124100141220000de2300000d3400014674000180a020024f10000017b2100019a5000001a5100240350000613400000e623000e0330000b6360001ff22100290260000676310000a332000e5f0200094350001c732100007b5000053605001e91000005e3300018a603001773410012c34000017b50001cf350000932210019c330000e23300003220200240304001a62040015d10000014704001a770300007b20001e9b50000223300007ab4000083e4100002703001843600012c350000bc740000572030000770400154361001e27140027a350001dba200007c604001c3b2000018312001cc22100014b50001607530000e72300083500001ad1000007aa50001d5713001c5261002043300000e62500257350001e6350001d51000019110000159751001c3a2000289b200004410000253100001ca724001dbb50000d9205001517530008831200067103001ea36000067a0300005640000ec2050026c2360005621200049a54000acb300002823200115243001bd206001d2730001d36040024f6040000e7050017b3600013733200042a54000563120024761400245100000c7703001bf2300000e60300064350001162210007b20400073b200025e2150015c2040013f3610014fb10001ab2060014fa2000044b420014fa3000007a200007426000016240000c021000002b520006a26200004320000cf2210016736100093250000a6250001fa350000a42620000171400229360000aca300019c32100014b200019d6040016f221000bc10000053a21000df2040024b25400174205002553600015a360000d7a50001a7321000df250001d2b5000044a30001fa304000a9221000a9205000333010018770400242236000bc34000252b0100073a200001fa54000e0750001c3a500023d25400067b03000323010009325200017703000e33310013a20300044b320009f210001bd2040010a3300018234000276640000de330000c83500001522100019100001813600009722100212350000973230015c224002312430015b23200083e400022722500289a20000d83400009d2060010b7240020120500033260000016130000e703000d8360001e9750001a6250000c6226001e26040014a224000742210015d32100003a520015d704000f8752000e5e03000f67520006522100220254000c22040004d100000fc221000f66410021a263000c760500017b20000ef751000d4a210023c221000d13500000a3510012b20600061330001dba4000081324000d7100000dd30100083f40000a37500008134100019703001d3a040001636000007a50001fa3210007c204000652200020d26500263206001d560400014604000e67520020a2650015f22100047350000cc23200001101001a23400015d705000e0752002022160015321200191750001c3a40000e5100000a7221001532030018f360001fe2610017a35000105361000d7754001d6230000da351001ea321001d3204000d47240004da30000812430022334000084741001f82540017326000132340001f72650003e70300000310000c77140015da30000c1360000b3362001ee25400002250001ec254001a2360000196020000b2050018236000191703000b6340000bc753001e8213001e7265001e622500094a30001913400017a100000703600016733200017a500009473000040205000eb36000199205000e0350001de2650013f332001ad72400017100000b3221000b02310003e100000ac75400191303000c77040017e7050008270300019b500008a605000d936100107313001a7721001d1265000e0b30000d7603001cf26500014b10000ad32100161a03000a92060004db5000098361001813400010a3500018771500120321001c425200257360000bcb40001f222100187705001c126300094330000293010009e7520017e725001bd235000bc7300011720500063202000572210001821200002621001813500003a35000187613000a92040006a243000b0221000e860500028210000497210008c331000df2600017e623000947510025a3500010e72100094b500011420200062321002293500000d3300000e604000a62210009175300240360002233500008e743000022210007ab500007b206000d522300151b30001cab32000762100008036100134331000e8603001a235000012102000d33400004a3600002e203000153210015d721001a8215001956500017e7150009410000046221000682100000e30200132360001843500014fb50001a2254000d3321001a02650019132100061243001152020018a6040015d6240019b2530002a221001843400007c75200067634000ef724000333320006536100199235000333610029ca3000223360000737500004e2030010b713000f2312001917210005e331000e55000005021000241330000f8721000c76030001f721002972050009c2600008e104000d83500002e225001a2331001b4340000d226000065230000d522100151a50001053320001f6200014fb40001a7b2100001b510015f7050018aa500000e2210010e654000bc330000bd3400010b61000271250000d76040014fb2000151a300003f221000ea360001b9330000f83210003a2300008c3300003e60300044352000932030000e724001a7b5000074231001683210001d2210014c2050017c2210007f350000da332000446210015f6030001c351001792530000e621000bc7500007f340000bcb3000177265000f86430003732100069213000947400003533100016340001fa360000f8b210017326100007603000447520014524000161b0300094b400000265000191b40000ea32100225260000e5e0400081221001eca540004422100040206000e07400003e7540001a221000a22600000d320001642160002b3310000a3610008a20500153226001023500027e250001622650001a206000ac721000333410009e000000d93320008472100094340001582520006136000151b50000a4203001ad603002792060015526500044a210004020400084b21000a3721001c3a30001502260015f1000000d360000e936000102304000177040002d34000007604001fe26000247b0100247a0100147254000ac3210008721000186360001877120013120600002601001b43500000f2210015db300015f6210029a3500024e3600014026500084321000a3321000163300018f350000ac7500001f723000cc3300008b000000063010023b26000014a100015f605002212520015db31000b32400021e2620000c301000197530004d704000eb3400027a360000da3610000121000134235000d136000017754000bb652000d7b5000006230000147540012f2350007533200098332001e9b21000e72020012e2350012d25200089321000bc3500003e6040002e22000044b40000016120015fa210003a3210000e7210003335100122260000003130017e10000019604001b43600000e60100125254000077540015d7230012b2050000575100009351001222650000e1000006e000001c435000105341000027530011f2360004522100001753000bfb3000110261000a3643000d7704001222500011a265001d23300007ab20001182610010232100117235001fc262000e5f430011426400014a20001c3b500006a212000392320011225100002604001112650004db3000053000000cd360000ac35000003b02001c3b40000723500010c225000e5102000926410003462100002a500010c35000109254001222040010823100107265000f72250004d000000197020000e102001ec703001012510000030300123330000fe2120027d206000c022600112250001e63600004400000085332000fb252000792500018ba54000813210001970400042000000e034000094b300003a340000e0b500000e6050008b6540011b25000191350000e72260007a1000003e0000003c0000006771400041250000bca5000105250000d934100084643001d9352001d5a50000ec2150003400000044a40000e92620003626000067734000ce360000b223100014603000e6651000e325300002a2100023312001ad604000ac100000bf101001e260300061321000db261000ac740000d22050000620600017603000a0203000eb313001952500001a2040001c3410000623100067632000927500001f00000191b21000d22150006124000016350000d02540004e232000cf265000ce226000e1250000c71000002e2210012c360001ad704000a2205000acb2100019000000c82250017e70300067731000016140007ca04000071000002d321001992060000c332000a3b210000a34100019603000ac730000be2650009c250001bd205000bb2520000e000001f42600004b332000b9254000347230009c2040016f2060006ea15000147030003e704000aca500008f23100126231001a6260000496540027e260000b52610000700000005000000b2262000182620025535000023212000092500000300000002000000a022100088212001007240027126000001000000a4212
  | 6 => 0x23f410000f62500031a5000018a40000212500001b10400008f310000b2520000410000012a600000260600022b5000000e1200023e510001d360000027040000040300017604000341000002c60300011b600000810000019b500001a5030001a1040000850400028100000107030000770500034b6000019b4000002602000231040000e7030000cb6200031a2000003b4000010b60000092050000710000019a600000ab600000f62400000f520001e340000151000000c72300031b6000023e4200010b4000000e53000235050000071200023e05000096600000aa5000000f320002974000011721000046040000f7040000ab500000360300009b6000003a500000761500011b210000770400015a50000326060001f10400026b5000026a200000061000015b3200026a30000076050001160400013e13000062430000525400007a620000d704000007130002d60400017a2100013f540000570200021a60000135010002fb4000003254000022650000124300013f040002b70400009a6000013e520000760400013f43000227600000370300023f050001170300007b210001350000000e1400018b4000000504000026050001210000024a21000326260000110100007a6000000f530000d60300029a400001b1030003476000000404000326030002f626000097240002832100000f020002870300023e0200000f10000217240000665000013f0300021a6200017605000161000001a1030000b6600002060500021a5000000f420000771300013e0400031a40000234040002110000007b600000f725000047050000260400003660000077250001060300003a60000001000001ae300000d1000001d7500002870400000505000227620000f6060001e75000023100000047240002fb500002a3600002176400005a5000013e030002c650000056030000ab200001d35000013f130001470300013e510000f72600000f120002635000013e500000c100000042210000c26000012603000076240001361300014b5000003b600000910000000a510002a10000011a6000008f4300022360000004000000462100005a600002f7600001110000013101000141000001e7630000010300004b600000050200008f0300012b600001e35000008e4100005b60000216030000aa400000370100014b2100013f5000023e0400008f3200000f1300016b4000013e540002b72500009a050000b100000085000002b7050000ba6000013e120000050300007102000047030000040500003a40000001020002b62300006104000246050001d7610001db600000f6030001c7620001b75200019b6000027b30000011040002460300008f0200007b1000028b6000002705000287210000ca5000008e030001d100000202210000f30200026b600000c6030000b2500002f730000186020002c60400000714000286230003470300019763000097040002da62000187600000eb400002f35000023500000206030001b10500008e020003135000027a6000026b40000027060002ca600000f2210001371300016b500002060600013a510002160400026b2000022a400001a1050000760300014603000153620000f72300008e40000046050003370600015621000006130000b6040000f6210002f7400000ba210001d7300001db5000028b500000e602000157620002ea5000023f040001db3000004a2100013f1000023e030000f6050001522100007614000227300001476400013f510000aa6000000e510000c660000137530001432100008f400000c62100008e4300000f5400020a0600013e320001d33000031b200002da0500027b600003260400015a2100009b620000710100013612000337050000010100000f04000117040001eb500000e60300000e5200013f1400006103000057030000c22100000f43000051000001a10200024a060000050000028b210001e76000027b5000007b6200003601000011030000b72300015a40000127640001670300001100000131050002d6030001176400013e0200021b6000010763000096030002ab4000031b40000146040000c7030000d6020000f721000126050000310000000f03000056020000e76300013e420002f1000000f10000000e040002ab60000206210000d7630001fb2000021704000321000000ba500002b1000000470400000f140000c7630000b7630000ca4000022b400000aa200000b650000027020001e3600000b62100026a400002020600013e43000036020002ab500000ca600000260300022740000097050000a71300000e030002ca21000042050001340200031b500001310400015000000271000000f7050001270500022330000096210000b2210000771400022b600000f60400007a61000191000000ea400002c25000000e500000722000005b5000015a3000000e1300031a6000013b51000097630000922100008742000106020000b6030000762300005b4000008e210001e100000134030001472100030a40000246210001e7300002275000011603000137140000776400000f500002420600000e5400010b5000019a30000033610000576200026a6000020100000076130000ca21000005010000d7050002d10000000b51000047610000d604000291040000e10000013f520001260400020a21000081040000376100013e5300008e0100034360000027030000175100010702000147040001ea6000016a500000c60200013f320002b70300005a400000770300010a400000460200013e1400008e310002e1000003260500023f02000061050000c0000000b0000002d6050000bb620001e33000003b500002a703000177240000fa21000223400000bb60000221000000210000030740000011050001eb300000f71300010a600001762100008e320000b7240002c2210000840100016a6000033703000081030000772100024604000172210002f36000007625000106540002c6210000900000022b300001d32100000210000092600000f66500019b3000016603000061020000e654000223500000b704000006120001db4000014b6000011b500002ca500001d72100013f02000084020002c100000070000002410000007b61000242210003370400006000000015000000c6540000b65200009a2100000753000011020000cb3100016a400002bb6000023e4100000e32000040000000f626000176030000460300026a50000131000000300000034b50000020000000f7240000a665000077150000100000008f410002ea400001710000024606000235040002165000008e42000231050002a7600000f6230002f3300000960500031a3000023f3100000f5100008f2100003702000032600001eb400000f703000001050001361400010a500001132100027b4000000e020002070500004a600000ab30000077230002fb300002d2050002f7500003175000014a600003310000026b300000472300000e4200016b600002060400023f030001eb6000004a050001f1050002ea600000762000006643000056540000960400034b400002da600002f34000031b30000046250001d7400002675000023f5300007321000036540000061400000e4300002665000085030000ab40000016430000cb60000004020000010400008f420002e6030001db210000b7030001d7600001e74000017606000084030002fb600001d3400000aa300000b26000008f010000000000015a60
  | 7 => 0xe3100000e5400000f52000005030000010400000e5000000f2100000f4200000f3100000e5300000e410000010300000e5200000e30000005040000040300000f530000075100000e1000000f3200000f540000010500000e2000000e2100000400000001020000000000000e400000040100000f5000000e5100000f1000000e320000064300000f4300000e420000050200000f51000004020000040400000f2000000f300000050500000f400000024300000e43000001010000050000000f4100000501000004050000010000000a43
  | _ => 0
def ZT (s : ℕ) := bar 52 (Sgen 52 8 xsT PTT) NNT (idxGen NNT HTT) id [] s
theorem zT_0 : span (ZT 0) 0 0 = true := rfl
theorem zT_1 : span (ZT 1) 0 0 = true := rfl
theorem hT_2_0 : span (ZT 2) 1 0 = true := by decide +kernel
theorem zT_2 : span (ZT 2) 1 0 = true := hT_2_0
theorem hT_3_0 : span (ZT 3) 10 0 = true := by decide +kernel
theorem hT_3_10 : span (ZT 3) 10 10 = true := by decide +kernel
theorem hT_3_20 : span (ZT 3) 10 20 = true := by decide +kernel
theorem hT_3_30 : span (ZT 3) 10 30 = true := by decide +kernel
theorem hT_3_40 : span (ZT 3) 10 40 = true := by decide +kernel
theorem hT_3_50 : span (ZT 3) 10 50 = true := by decide +kernel
theorem hT_3_60 : span (ZT 3) 8 60 = true := by decide +kernel
theorem zT_3 : span (ZT 3) 68 0 = true := (@span_join (ZT 3) 60 0 8 (@span_join (ZT 3) 50 0 10 (@span_join (ZT 3) 40 0 10 (@span_join (ZT 3) 30 0 10 (@span_join (ZT 3) 20 0 10 (@span_join (ZT 3) 10 0 10 hT_3_0 hT_3_10) hT_3_20) hT_3_30) hT_3_40) hT_3_50) hT_3_60)
theorem hT_4_0 : span (ZT 4) 10 0 = true := by decide +kernel
theorem hT_4_10 : span (ZT 4) 10 10 = true := by decide +kernel
theorem hT_4_20 : span (ZT 4) 10 20 = true := by decide +kernel
theorem hT_4_30 : span (ZT 4) 10 30 = true := by decide +kernel
theorem hT_4_40 : span (ZT 4) 10 40 = true := by decide +kernel
theorem hT_4_50 : span (ZT 4) 10 50 = true := by decide +kernel
theorem hT_4_60 : span (ZT 4) 10 60 = true := by decide +kernel
theorem hT_4_70 : span (ZT 4) 10 70 = true := by decide +kernel
theorem hT_4_80 : span (ZT 4) 10 80 = true := by decide +kernel
theorem hT_4_90 : span (ZT 4) 10 90 = true := by decide +kernel
theorem hT_4_100 : span (ZT 4) 10 100 = true := by decide +kernel
theorem hT_4_110 : span (ZT 4) 10 110 = true := by decide +kernel
theorem hT_4_120 : span (ZT 4) 10 120 = true := by decide +kernel
theorem hT_4_130 : span (ZT 4) 10 130 = true := by decide +kernel
theorem hT_4_140 : span (ZT 4) 10 140 = true := by decide +kernel
theorem hT_4_150 : span (ZT 4) 10 150 = true := by decide +kernel
theorem hT_4_160 : span (ZT 4) 10 160 = true := by decide +kernel
theorem hT_4_170 : span (ZT 4) 10 170 = true := by decide +kernel
theorem hT_4_180 : span (ZT 4) 10 180 = true := by decide +kernel
theorem hT_4_190 : span (ZT 4) 10 190 = true := by decide +kernel
theorem hT_4_200 : span (ZT 4) 10 200 = true := by decide +kernel
theorem hT_4_210 : span (ZT 4) 10 210 = true := by decide +kernel
theorem hT_4_220 : span (ZT 4) 10 220 = true := by decide +kernel
theorem hT_4_230 : span (ZT 4) 10 230 = true := by decide +kernel
theorem hT_4_240 : span (ZT 4) 10 240 = true := by decide +kernel
theorem hT_4_250 : span (ZT 4) 10 250 = true := by decide +kernel
theorem hT_4_260 : span (ZT 4) 10 260 = true := by decide +kernel
theorem hT_4_270 : span (ZT 4) 10 270 = true := by decide +kernel
theorem hT_4_280 : span (ZT 4) 10 280 = true := by decide +kernel
theorem hT_4_290 : span (ZT 4) 10 290 = true := by decide +kernel
theorem hT_4_300 : span (ZT 4) 10 300 = true := by decide +kernel
theorem hT_4_310 : span (ZT 4) 10 310 = true := by decide +kernel
theorem hT_4_320 : span (ZT 4) 10 320 = true := by decide +kernel
theorem hT_4_330 : span (ZT 4) 10 330 = true := by decide +kernel
theorem hT_4_340 : span (ZT 4) 10 340 = true := by decide +kernel
theorem hT_4_350 : span (ZT 4) 10 350 = true := by decide +kernel
theorem hT_4_360 : span (ZT 4) 10 360 = true := by decide +kernel
theorem hT_4_370 : span (ZT 4) 10 370 = true := by decide +kernel
theorem hT_4_380 : span (ZT 4) 10 380 = true := by decide +kernel
theorem hT_4_390 : span (ZT 4) 10 390 = true := by decide +kernel
theorem hT_4_400 : span (ZT 4) 10 400 = true := by decide +kernel
theorem hT_4_410 : span (ZT 4) 10 410 = true := by decide +kernel
theorem hT_4_420 : span (ZT 4) 10 420 = true := by decide +kernel
theorem hT_4_430 : span (ZT 4) 10 430 = true := by decide +kernel
theorem hT_4_440 : span (ZT 4) 9 440 = true := by decide +kernel
theorem zT_4 : span (ZT 4) 449 0 = true := (@span_join (ZT 4) 440 0 9 (@span_join (ZT 4) 430 0 10 (@span_join (ZT 4) 420 0 10 (@span_join (ZT 4) 410 0 10 (@span_join (ZT 4) 400 0 10 (@span_join (ZT 4) 390 0 10 (@span_join (ZT 4) 380 0 10 (@span_join (ZT 4) 370 0 10 (@span_join (ZT 4) 360 0 10 (@span_join (ZT 4) 350 0 10 (@span_join (ZT 4) 340 0 10 (@span_join (ZT 4) 330 0 10 (@span_join (ZT 4) 320 0 10 (@span_join (ZT 4) 310 0 10 (@span_join (ZT 4) 300 0 10 (@span_join (ZT 4) 290 0 10 (@span_join (ZT 4) 280 0 10 (@span_join (ZT 4) 270 0 10 (@span_join (ZT 4) 260 0 10 (@span_join (ZT 4) 250 0 10 (@span_join (ZT 4) 240 0 10 (@span_join (ZT 4) 230 0 10 (@span_join (ZT 4) 220 0 10 (@span_join (ZT 4) 210 0 10 (@span_join (ZT 4) 200 0 10 (@span_join (ZT 4) 190 0 10 (@span_join (ZT 4) 180 0 10 (@span_join (ZT 4) 170 0 10 (@span_join (ZT 4) 160 0 10 (@span_join (ZT 4) 150 0 10 (@span_join (ZT 4) 140 0 10 (@span_join (ZT 4) 130 0 10 (@span_join (ZT 4) 120 0 10 (@span_join (ZT 4) 110 0 10 (@span_join (ZT 4) 100 0 10 (@span_join (ZT 4) 90 0 10 (@span_join (ZT 4) 80 0 10 (@span_join (ZT 4) 70 0 10 (@span_join (ZT 4) 60 0 10 (@span_join (ZT 4) 50 0 10 (@span_join (ZT 4) 40 0 10 (@span_join (ZT 4) 30 0 10 (@span_join (ZT 4) 20 0 10 (@span_join (ZT 4) 10 0 10 hT_4_0 hT_4_10) hT_4_20) hT_4_30) hT_4_40) hT_4_50) hT_4_60) hT_4_70) hT_4_80) hT_4_90) hT_4_100) hT_4_110) hT_4_120) hT_4_130) hT_4_140) hT_4_150) hT_4_160) hT_4_170) hT_4_180) hT_4_190) hT_4_200) hT_4_210) hT_4_220) hT_4_230) hT_4_240) hT_4_250) hT_4_260) hT_4_270) hT_4_280) hT_4_290) hT_4_300) hT_4_310) hT_4_320) hT_4_330) hT_4_340) hT_4_350) hT_4_360) hT_4_370) hT_4_380) hT_4_390) hT_4_400) hT_4_410) hT_4_420) hT_4_430) hT_4_440)
theorem hT_5_0 : span (ZT 5) 10 0 = true := by decide +kernel
theorem hT_5_10 : span (ZT 5) 10 10 = true := by decide +kernel
theorem hT_5_20 : span (ZT 5) 10 20 = true := by decide +kernel
theorem hT_5_30 : span (ZT 5) 10 30 = true := by decide +kernel
theorem hT_5_40 : span (ZT 5) 10 40 = true := by decide +kernel
theorem hT_5_50 : span (ZT 5) 10 50 = true := by decide +kernel
theorem hT_5_60 : span (ZT 5) 10 60 = true := by decide +kernel
theorem hT_5_70 : span (ZT 5) 10 70 = true := by decide +kernel
theorem hT_5_80 : span (ZT 5) 10 80 = true := by decide +kernel
theorem hT_5_90 : span (ZT 5) 10 90 = true := by decide +kernel
theorem hT_5_100 : span (ZT 5) 10 100 = true := by decide +kernel
theorem hT_5_110 : span (ZT 5) 10 110 = true := by decide +kernel
theorem hT_5_120 : span (ZT 5) 10 120 = true := by decide +kernel
theorem hT_5_130 : span (ZT 5) 10 130 = true := by decide +kernel
theorem hT_5_140 : span (ZT 5) 10 140 = true := by decide +kernel
theorem hT_5_150 : span (ZT 5) 10 150 = true := by decide +kernel
theorem hT_5_160 : span (ZT 5) 10 160 = true := by decide +kernel
theorem hT_5_170 : span (ZT 5) 10 170 = true := by decide +kernel
theorem hT_5_180 : span (ZT 5) 10 180 = true := by decide +kernel
theorem hT_5_190 : span (ZT 5) 10 190 = true := by decide +kernel
theorem hT_5_200 : span (ZT 5) 10 200 = true := by decide +kernel
theorem hT_5_210 : span (ZT 5) 10 210 = true := by decide +kernel
theorem hT_5_220 : span (ZT 5) 10 220 = true := by decide +kernel
theorem hT_5_230 : span (ZT 5) 10 230 = true := by decide +kernel
theorem hT_5_240 : span (ZT 5) 10 240 = true := by decide +kernel
theorem hT_5_250 : span (ZT 5) 10 250 = true := by decide +kernel
theorem hT_5_260 : span (ZT 5) 10 260 = true := by decide +kernel
theorem hT_5_270 : span (ZT 5) 10 270 = true := by decide +kernel
theorem hT_5_280 : span (ZT 5) 10 280 = true := by decide +kernel
theorem hT_5_290 : span (ZT 5) 10 290 = true := by decide +kernel
theorem hT_5_300 : span (ZT 5) 10 300 = true := by decide +kernel
theorem hT_5_310 : span (ZT 5) 10 310 = true := by decide +kernel
theorem hT_5_320 : span (ZT 5) 10 320 = true := by decide +kernel
theorem hT_5_330 : span (ZT 5) 10 330 = true := by decide +kernel
theorem hT_5_340 : span (ZT 5) 10 340 = true := by decide +kernel
theorem hT_5_350 : span (ZT 5) 10 350 = true := by decide +kernel
theorem hT_5_360 : span (ZT 5) 10 360 = true := by decide +kernel
theorem hT_5_370 : span (ZT 5) 10 370 = true := by decide +kernel
theorem hT_5_380 : span (ZT 5) 10 380 = true := by decide +kernel
theorem hT_5_390 : span (ZT 5) 10 390 = true := by decide +kernel
theorem hT_5_400 : span (ZT 5) 10 400 = true := by decide +kernel
theorem hT_5_410 : span (ZT 5) 10 410 = true := by decide +kernel
theorem hT_5_420 : span (ZT 5) 10 420 = true := by decide +kernel
theorem hT_5_430 : span (ZT 5) 10 430 = true := by decide +kernel
theorem hT_5_440 : span (ZT 5) 10 440 = true := by decide +kernel
theorem hT_5_450 : span (ZT 5) 10 450 = true := by decide +kernel
theorem hT_5_460 : span (ZT 5) 10 460 = true := by decide +kernel
theorem hT_5_470 : span (ZT 5) 10 470 = true := by decide +kernel
theorem hT_5_480 : span (ZT 5) 10 480 = true := by decide +kernel
theorem hT_5_490 : span (ZT 5) 10 490 = true := by decide +kernel
theorem hT_5_500 : span (ZT 5) 10 500 = true := by decide +kernel
theorem hT_5_510 : span (ZT 5) 10 510 = true := by decide +kernel
theorem hT_5_520 : span (ZT 5) 10 520 = true := by decide +kernel
theorem hT_5_530 : span (ZT 5) 10 530 = true := by decide +kernel
theorem hT_5_540 : span (ZT 5) 10 540 = true := by decide +kernel
theorem hT_5_550 : span (ZT 5) 10 550 = true := by decide +kernel
theorem hT_5_560 : span (ZT 5) 10 560 = true := by decide +kernel
theorem hT_5_570 : span (ZT 5) 10 570 = true := by decide +kernel
theorem hT_5_580 : span (ZT 5) 10 580 = true := by decide +kernel
theorem hT_5_590 : span (ZT 5) 10 590 = true := by decide +kernel
theorem hT_5_600 : span (ZT 5) 10 600 = true := by decide +kernel
theorem hT_5_610 : span (ZT 5) 10 610 = true := by decide +kernel
theorem hT_5_620 : span (ZT 5) 10 620 = true := by decide +kernel
theorem hT_5_630 : span (ZT 5) 10 630 = true := by decide +kernel
theorem hT_5_640 : span (ZT 5) 10 640 = true := by decide +kernel
theorem hT_5_650 : span (ZT 5) 10 650 = true := by decide +kernel
theorem hT_5_660 : span (ZT 5) 10 660 = true := by decide +kernel
theorem hT_5_670 : span (ZT 5) 10 670 = true := by decide +kernel
theorem hT_5_680 : span (ZT 5) 10 680 = true := by decide +kernel
theorem hT_5_690 : span (ZT 5) 10 690 = true := by decide +kernel
theorem hT_5_700 : span (ZT 5) 10 700 = true := by decide +kernel
theorem hT_5_710 : span (ZT 5) 10 710 = true := by decide +kernel
theorem hT_5_720 : span (ZT 5) 10 720 = true := by decide +kernel
theorem hT_5_730 : span (ZT 5) 10 730 = true := by decide +kernel
theorem hT_5_740 : span (ZT 5) 10 740 = true := by decide +kernel
theorem hT_5_750 : span (ZT 5) 10 750 = true := by decide +kernel
theorem hT_5_760 : span (ZT 5) 10 760 = true := by decide +kernel
theorem hT_5_770 : span (ZT 5) 10 770 = true := by decide +kernel
theorem hT_5_780 : span (ZT 5) 10 780 = true := by decide +kernel
theorem hT_5_790 : span (ZT 5) 10 790 = true := by decide +kernel
theorem hT_5_800 : span (ZT 5) 10 800 = true := by decide +kernel
theorem hT_5_810 : span (ZT 5) 10 810 = true := by decide +kernel
theorem hT_5_820 : span (ZT 5) 10 820 = true := by decide +kernel
theorem hT_5_830 : span (ZT 5) 10 830 = true := by decide +kernel
theorem hT_5_840 : span (ZT 5) 10 840 = true := by decide +kernel
theorem hT_5_850 : span (ZT 5) 10 850 = true := by decide +kernel
theorem hT_5_860 : span (ZT 5) 10 860 = true := by decide +kernel
theorem hT_5_870 : span (ZT 5) 10 870 = true := by decide +kernel
theorem hT_5_880 : span (ZT 5) 10 880 = true := by decide +kernel
theorem hT_5_890 : span (ZT 5) 10 890 = true := by decide +kernel
theorem hT_5_900 : span (ZT 5) 10 900 = true := by decide +kernel
theorem hT_5_910 : span (ZT 5) 10 910 = true := by decide +kernel
theorem hT_5_920 : span (ZT 5) 10 920 = true := by decide +kernel
theorem hT_5_930 : span (ZT 5) 10 930 = true := by decide +kernel
theorem hT_5_940 : span (ZT 5) 10 940 = true := by decide +kernel
theorem hT_5_950 : span (ZT 5) 10 950 = true := by decide +kernel
theorem hT_5_960 : span (ZT 5) 10 960 = true := by decide +kernel
theorem hT_5_970 : span (ZT 5) 10 970 = true := by decide +kernel
theorem hT_5_980 : span (ZT 5) 10 980 = true := by decide +kernel
theorem hT_5_990 : span (ZT 5) 10 990 = true := by decide +kernel
theorem hT_5_1000 : span (ZT 5) 10 1000 = true := by decide +kernel
theorem hT_5_1010 : span (ZT 5) 10 1010 = true := by decide +kernel
theorem hT_5_1020 : span (ZT 5) 10 1020 = true := by decide +kernel
theorem hT_5_1030 : span (ZT 5) 10 1030 = true := by decide +kernel
theorem hT_5_1040 : span (ZT 5) 10 1040 = true := by decide +kernel
theorem hT_5_1050 : span (ZT 5) 10 1050 = true := by decide +kernel
theorem hT_5_1060 : span (ZT 5) 10 1060 = true := by decide +kernel
theorem hT_5_1070 : span (ZT 5) 10 1070 = true := by decide +kernel
theorem hT_5_1080 : span (ZT 5) 10 1080 = true := by decide +kernel
theorem hT_5_1090 : span (ZT 5) 10 1090 = true := by decide +kernel
theorem hT_5_1100 : span (ZT 5) 4 1100 = true := by decide +kernel
theorem zT_5 : span (ZT 5) 1104 0 = true := (@span_join (ZT 5) 1100 0 4 (@span_join (ZT 5) 1090 0 10 (@span_join (ZT 5) 1080 0 10 (@span_join (ZT 5) 1070 0 10 (@span_join (ZT 5) 1060 0 10 (@span_join (ZT 5) 1050 0 10 (@span_join (ZT 5) 1040 0 10 (@span_join (ZT 5) 1030 0 10 (@span_join (ZT 5) 1020 0 10 (@span_join (ZT 5) 1010 0 10 (@span_join (ZT 5) 1000 0 10 (@span_join (ZT 5) 990 0 10 (@span_join (ZT 5) 980 0 10 (@span_join (ZT 5) 970 0 10 (@span_join (ZT 5) 960 0 10 (@span_join (ZT 5) 950 0 10 (@span_join (ZT 5) 940 0 10 (@span_join (ZT 5) 930 0 10 (@span_join (ZT 5) 920 0 10 (@span_join (ZT 5) 910 0 10 (@span_join (ZT 5) 900 0 10 (@span_join (ZT 5) 890 0 10 (@span_join (ZT 5) 880 0 10 (@span_join (ZT 5) 870 0 10 (@span_join (ZT 5) 860 0 10 (@span_join (ZT 5) 850 0 10 (@span_join (ZT 5) 840 0 10 (@span_join (ZT 5) 830 0 10 (@span_join (ZT 5) 820 0 10 (@span_join (ZT 5) 810 0 10 (@span_join (ZT 5) 800 0 10 (@span_join (ZT 5) 790 0 10 (@span_join (ZT 5) 780 0 10 (@span_join (ZT 5) 770 0 10 (@span_join (ZT 5) 760 0 10 (@span_join (ZT 5) 750 0 10 (@span_join (ZT 5) 740 0 10 (@span_join (ZT 5) 730 0 10 (@span_join (ZT 5) 720 0 10 (@span_join (ZT 5) 710 0 10 (@span_join (ZT 5) 700 0 10 (@span_join (ZT 5) 690 0 10 (@span_join (ZT 5) 680 0 10 (@span_join (ZT 5) 670 0 10 (@span_join (ZT 5) 660 0 10 (@span_join (ZT 5) 650 0 10 (@span_join (ZT 5) 640 0 10 (@span_join (ZT 5) 630 0 10 (@span_join (ZT 5) 620 0 10 (@span_join (ZT 5) 610 0 10 (@span_join (ZT 5) 600 0 10 (@span_join (ZT 5) 590 0 10 (@span_join (ZT 5) 580 0 10 (@span_join (ZT 5) 570 0 10 (@span_join (ZT 5) 560 0 10 (@span_join (ZT 5) 550 0 10 (@span_join (ZT 5) 540 0 10 (@span_join (ZT 5) 530 0 10 (@span_join (ZT 5) 520 0 10 (@span_join (ZT 5) 510 0 10 (@span_join (ZT 5) 500 0 10 (@span_join (ZT 5) 490 0 10 (@span_join (ZT 5) 480 0 10 (@span_join (ZT 5) 470 0 10 (@span_join (ZT 5) 460 0 10 (@span_join (ZT 5) 450 0 10 (@span_join (ZT 5) 440 0 10 (@span_join (ZT 5) 430 0 10 (@span_join (ZT 5) 420 0 10 (@span_join (ZT 5) 410 0 10 (@span_join (ZT 5) 400 0 10 (@span_join (ZT 5) 390 0 10 (@span_join (ZT 5) 380 0 10 (@span_join (ZT 5) 370 0 10 (@span_join (ZT 5) 360 0 10 (@span_join (ZT 5) 350 0 10 (@span_join (ZT 5) 340 0 10 (@span_join (ZT 5) 330 0 10 (@span_join (ZT 5) 320 0 10 (@span_join (ZT 5) 310 0 10 (@span_join (ZT 5) 300 0 10 (@span_join (ZT 5) 290 0 10 (@span_join (ZT 5) 280 0 10 (@span_join (ZT 5) 270 0 10 (@span_join (ZT 5) 260 0 10 (@span_join (ZT 5) 250 0 10 (@span_join (ZT 5) 240 0 10 (@span_join (ZT 5) 230 0 10 (@span_join (ZT 5) 220 0 10 (@span_join (ZT 5) 210 0 10 (@span_join (ZT 5) 200 0 10 (@span_join (ZT 5) 190 0 10 (@span_join (ZT 5) 180 0 10 (@span_join (ZT 5) 170 0 10 (@span_join (ZT 5) 160 0 10 (@span_join (ZT 5) 150 0 10 (@span_join (ZT 5) 140 0 10 (@span_join (ZT 5) 130 0 10 (@span_join (ZT 5) 120 0 10 (@span_join (ZT 5) 110 0 10 (@span_join (ZT 5) 100 0 10 (@span_join (ZT 5) 90 0 10 (@span_join (ZT 5) 80 0 10 (@span_join (ZT 5) 70 0 10 (@span_join (ZT 5) 60 0 10 (@span_join (ZT 5) 50 0 10 (@span_join (ZT 5) 40 0 10 (@span_join (ZT 5) 30 0 10 (@span_join (ZT 5) 20 0 10 (@span_join (ZT 5) 10 0 10 hT_5_0 hT_5_10) hT_5_20) hT_5_30) hT_5_40) hT_5_50) hT_5_60) hT_5_70) hT_5_80) hT_5_90) hT_5_100) hT_5_110) hT_5_120) hT_5_130) hT_5_140) hT_5_150) hT_5_160) hT_5_170) hT_5_180) hT_5_190) hT_5_200) hT_5_210) hT_5_220) hT_5_230) hT_5_240) hT_5_250) hT_5_260) hT_5_270) hT_5_280) hT_5_290) hT_5_300) hT_5_310) hT_5_320) hT_5_330) hT_5_340) hT_5_350) hT_5_360) hT_5_370) hT_5_380) hT_5_390) hT_5_400) hT_5_410) hT_5_420) hT_5_430) hT_5_440) hT_5_450) hT_5_460) hT_5_470) hT_5_480) hT_5_490) hT_5_500) hT_5_510) hT_5_520) hT_5_530) hT_5_540) hT_5_550) hT_5_560) hT_5_570) hT_5_580) hT_5_590) hT_5_600) hT_5_610) hT_5_620) hT_5_630) hT_5_640) hT_5_650) hT_5_660) hT_5_670) hT_5_680) hT_5_690) hT_5_700) hT_5_710) hT_5_720) hT_5_730) hT_5_740) hT_5_750) hT_5_760) hT_5_770) hT_5_780) hT_5_790) hT_5_800) hT_5_810) hT_5_820) hT_5_830) hT_5_840) hT_5_850) hT_5_860) hT_5_870) hT_5_880) hT_5_890) hT_5_900) hT_5_910) hT_5_920) hT_5_930) hT_5_940) hT_5_950) hT_5_960) hT_5_970) hT_5_980) hT_5_990) hT_5_1000) hT_5_1010) hT_5_1020) hT_5_1030) hT_5_1040) hT_5_1050) hT_5_1060) hT_5_1070) hT_5_1080) hT_5_1090) hT_5_1100)
theorem hT_6_0 : span (ZT 6) 10 0 = true := by decide +kernel
theorem hT_6_10 : span (ZT 6) 10 10 = true := by decide +kernel
theorem hT_6_20 : span (ZT 6) 10 20 = true := by decide +kernel
theorem hT_6_30 : span (ZT 6) 10 30 = true := by decide +kernel
theorem hT_6_40 : span (ZT 6) 10 40 = true := by decide +kernel
theorem hT_6_50 : span (ZT 6) 10 50 = true := by decide +kernel
theorem hT_6_60 : span (ZT 6) 10 60 = true := by decide +kernel
theorem hT_6_70 : span (ZT 6) 10 70 = true := by decide +kernel
theorem hT_6_80 : span (ZT 6) 10 80 = true := by decide +kernel
theorem hT_6_90 : span (ZT 6) 10 90 = true := by decide +kernel
theorem hT_6_100 : span (ZT 6) 10 100 = true := by decide +kernel
theorem hT_6_110 : span (ZT 6) 10 110 = true := by decide +kernel
theorem hT_6_120 : span (ZT 6) 10 120 = true := by decide +kernel
theorem hT_6_130 : span (ZT 6) 10 130 = true := by decide +kernel
theorem hT_6_140 : span (ZT 6) 10 140 = true := by decide +kernel
theorem hT_6_150 : span (ZT 6) 10 150 = true := by decide +kernel
theorem hT_6_160 : span (ZT 6) 10 160 = true := by decide +kernel
theorem hT_6_170 : span (ZT 6) 10 170 = true := by decide +kernel
theorem hT_6_180 : span (ZT 6) 10 180 = true := by decide +kernel
theorem hT_6_190 : span (ZT 6) 10 190 = true := by decide +kernel
theorem hT_6_200 : span (ZT 6) 10 200 = true := by decide +kernel
theorem hT_6_210 : span (ZT 6) 10 210 = true := by decide +kernel
theorem hT_6_220 : span (ZT 6) 10 220 = true := by decide +kernel
theorem hT_6_230 : span (ZT 6) 10 230 = true := by decide +kernel
theorem hT_6_240 : span (ZT 6) 10 240 = true := by decide +kernel
theorem hT_6_250 : span (ZT 6) 10 250 = true := by decide +kernel
theorem hT_6_260 : span (ZT 6) 10 260 = true := by decide +kernel
theorem hT_6_270 : span (ZT 6) 10 270 = true := by decide +kernel
theorem hT_6_280 : span (ZT 6) 10 280 = true := by decide +kernel
theorem hT_6_290 : span (ZT 6) 10 290 = true := by decide +kernel
theorem hT_6_300 : span (ZT 6) 10 300 = true := by decide +kernel
theorem hT_6_310 : span (ZT 6) 10 310 = true := by decide +kernel
theorem hT_6_320 : span (ZT 6) 10 320 = true := by decide +kernel
theorem hT_6_330 : span (ZT 6) 10 330 = true := by decide +kernel
theorem hT_6_340 : span (ZT 6) 10 340 = true := by decide +kernel
theorem hT_6_350 : span (ZT 6) 10 350 = true := by decide +kernel
theorem hT_6_360 : span (ZT 6) 10 360 = true := by decide +kernel
theorem hT_6_370 : span (ZT 6) 10 370 = true := by decide +kernel
theorem hT_6_380 : span (ZT 6) 10 380 = true := by decide +kernel
theorem hT_6_390 : span (ZT 6) 10 390 = true := by decide +kernel
theorem hT_6_400 : span (ZT 6) 10 400 = true := by decide +kernel
theorem hT_6_410 : span (ZT 6) 10 410 = true := by decide +kernel
theorem hT_6_420 : span (ZT 6) 10 420 = true := by decide +kernel
theorem hT_6_430 : span (ZT 6) 10 430 = true := by decide +kernel
theorem hT_6_440 : span (ZT 6) 10 440 = true := by decide +kernel
theorem hT_6_450 : span (ZT 6) 10 450 = true := by decide +kernel
theorem hT_6_460 : span (ZT 6) 10 460 = true := by decide +kernel
theorem hT_6_470 : span (ZT 6) 10 470 = true := by decide +kernel
theorem hT_6_480 : span (ZT 6) 10 480 = true := by decide +kernel
theorem hT_6_490 : span (ZT 6) 10 490 = true := by decide +kernel
theorem hT_6_500 : span (ZT 6) 10 500 = true := by decide +kernel
theorem hT_6_510 : span (ZT 6) 10 510 = true := by decide +kernel
theorem hT_6_520 : span (ZT 6) 10 520 = true := by decide +kernel
theorem hT_6_530 : span (ZT 6) 10 530 = true := by decide +kernel
theorem hT_6_540 : span (ZT 6) 10 540 = true := by decide +kernel
theorem hT_6_550 : span (ZT 6) 10 550 = true := by decide +kernel
theorem hT_6_560 : span (ZT 6) 10 560 = true := by decide +kernel
theorem hT_6_570 : span (ZT 6) 10 570 = true := by decide +kernel
theorem hT_6_580 : span (ZT 6) 10 580 = true := by decide +kernel
theorem hT_6_590 : span (ZT 6) 10 590 = true := by decide +kernel
theorem hT_6_600 : span (ZT 6) 10 600 = true := by decide +kernel
theorem hT_6_610 : span (ZT 6) 10 610 = true := by decide +kernel
theorem hT_6_620 : span (ZT 6) 10 620 = true := by decide +kernel
theorem hT_6_630 : span (ZT 6) 10 630 = true := by decide +kernel
theorem hT_6_640 : span (ZT 6) 10 640 = true := by decide +kernel
theorem hT_6_650 : span (ZT 6) 10 650 = true := by decide +kernel
theorem hT_6_660 : span (ZT 6) 10 660 = true := by decide +kernel
theorem hT_6_670 : span (ZT 6) 5 670 = true := by decide +kernel
theorem zT_6 : span (ZT 6) 675 0 = true := (@span_join (ZT 6) 670 0 5 (@span_join (ZT 6) 660 0 10 (@span_join (ZT 6) 650 0 10 (@span_join (ZT 6) 640 0 10 (@span_join (ZT 6) 630 0 10 (@span_join (ZT 6) 620 0 10 (@span_join (ZT 6) 610 0 10 (@span_join (ZT 6) 600 0 10 (@span_join (ZT 6) 590 0 10 (@span_join (ZT 6) 580 0 10 (@span_join (ZT 6) 570 0 10 (@span_join (ZT 6) 560 0 10 (@span_join (ZT 6) 550 0 10 (@span_join (ZT 6) 540 0 10 (@span_join (ZT 6) 530 0 10 (@span_join (ZT 6) 520 0 10 (@span_join (ZT 6) 510 0 10 (@span_join (ZT 6) 500 0 10 (@span_join (ZT 6) 490 0 10 (@span_join (ZT 6) 480 0 10 (@span_join (ZT 6) 470 0 10 (@span_join (ZT 6) 460 0 10 (@span_join (ZT 6) 450 0 10 (@span_join (ZT 6) 440 0 10 (@span_join (ZT 6) 430 0 10 (@span_join (ZT 6) 420 0 10 (@span_join (ZT 6) 410 0 10 (@span_join (ZT 6) 400 0 10 (@span_join (ZT 6) 390 0 10 (@span_join (ZT 6) 380 0 10 (@span_join (ZT 6) 370 0 10 (@span_join (ZT 6) 360 0 10 (@span_join (ZT 6) 350 0 10 (@span_join (ZT 6) 340 0 10 (@span_join (ZT 6) 330 0 10 (@span_join (ZT 6) 320 0 10 (@span_join (ZT 6) 310 0 10 (@span_join (ZT 6) 300 0 10 (@span_join (ZT 6) 290 0 10 (@span_join (ZT 6) 280 0 10 (@span_join (ZT 6) 270 0 10 (@span_join (ZT 6) 260 0 10 (@span_join (ZT 6) 250 0 10 (@span_join (ZT 6) 240 0 10 (@span_join (ZT 6) 230 0 10 (@span_join (ZT 6) 220 0 10 (@span_join (ZT 6) 210 0 10 (@span_join (ZT 6) 200 0 10 (@span_join (ZT 6) 190 0 10 (@span_join (ZT 6) 180 0 10 (@span_join (ZT 6) 170 0 10 (@span_join (ZT 6) 160 0 10 (@span_join (ZT 6) 150 0 10 (@span_join (ZT 6) 140 0 10 (@span_join (ZT 6) 130 0 10 (@span_join (ZT 6) 120 0 10 (@span_join (ZT 6) 110 0 10 (@span_join (ZT 6) 100 0 10 (@span_join (ZT 6) 90 0 10 (@span_join (ZT 6) 80 0 10 (@span_join (ZT 6) 70 0 10 (@span_join (ZT 6) 60 0 10 (@span_join (ZT 6) 50 0 10 (@span_join (ZT 6) 40 0 10 (@span_join (ZT 6) 30 0 10 (@span_join (ZT 6) 20 0 10 (@span_join (ZT 6) 10 0 10 hT_6_0 hT_6_10) hT_6_20) hT_6_30) hT_6_40) hT_6_50) hT_6_60) hT_6_70) hT_6_80) hT_6_90) hT_6_100) hT_6_110) hT_6_120) hT_6_130) hT_6_140) hT_6_150) hT_6_160) hT_6_170) hT_6_180) hT_6_190) hT_6_200) hT_6_210) hT_6_220) hT_6_230) hT_6_240) hT_6_250) hT_6_260) hT_6_270) hT_6_280) hT_6_290) hT_6_300) hT_6_310) hT_6_320) hT_6_330) hT_6_340) hT_6_350) hT_6_360) hT_6_370) hT_6_380) hT_6_390) hT_6_400) hT_6_410) hT_6_420) hT_6_430) hT_6_440) hT_6_450) hT_6_460) hT_6_470) hT_6_480) hT_6_490) hT_6_500) hT_6_510) hT_6_520) hT_6_530) hT_6_540) hT_6_550) hT_6_560) hT_6_570) hT_6_580) hT_6_590) hT_6_600) hT_6_610) hT_6_620) hT_6_630) hT_6_640) hT_6_650) hT_6_660) hT_6_670)
theorem hT_7_0 : span (ZT 7) 10 0 = true := by decide +kernel
theorem hT_7_10 : span (ZT 7) 10 10 = true := by decide +kernel
theorem hT_7_20 : span (ZT 7) 10 20 = true := by decide +kernel
theorem hT_7_30 : span (ZT 7) 10 30 = true := by decide +kernel
theorem hT_7_40 : span (ZT 7) 10 40 = true := by decide +kernel
theorem hT_7_50 : span (ZT 7) 3 50 = true := by decide +kernel
theorem zT_7 : span (ZT 7) 53 0 = true := (@span_join (ZT 7) 50 0 3 (@span_join (ZT 7) 40 0 10 (@span_join (ZT 7) 30 0 10 (@span_join (ZT 7) 20 0 10 (@span_join (ZT 7) 10 0 10 hT_7_0 hT_7_10) hT_7_20) hT_7_30) hT_7_40) hT_7_50)
theorem hT_8_0 : span (ZT 8) 1 0 = true := by decide +kernel
theorem zT_8 : span (ZT 8) 1 0 = true := hT_8_0
theorem baseT : ∀ s : ℕ, HasCircuitSize 6 fT s → 9 ≤ s := by
  refine prove_base 6 52 8 fT rowsT xsT [] NNT HTT PTT
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (fun s hs => by
      interval_cases s
      · exact fun i hi => span_ok zT_0 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_1 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_2 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_3 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_4 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_5 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_6 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_7 i (Nat.zero_le i) hi
      · exact fun i hi => span_ok zT_8 i (Nat.zero_le i) hi
    )
def upperT : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩]
theorem upperT_ok : ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨upperT, 14⟩ (List.ofFn x) = fT x := by
  decide +kernel
end PEqualNP.Outside.L_meta_12671

open PEqualNP.Outside.L_meta_12671 in
theorem PEqualNP.Outside.L_meta_12671 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  have hM := baseT s hs
  refine ⟨⟨upperT, 14⟩, ?_, ?_, fun x => upperT_ok x⟩
  · intro g hg
    simp only [upperT, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · show upperT.length ≤ s
    simp only [upperT, List.length_cons, List.length_nil]
    omega
