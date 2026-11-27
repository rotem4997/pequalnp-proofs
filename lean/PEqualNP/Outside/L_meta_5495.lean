import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5495
/- Restrict one of the twin vertices. Its first reader simplifies, so a six-gate
    circuit would induce a five-gate circuit for the bull graph. -/
namespace TwinRestriction5495

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
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


/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


end TwinRestriction5495

namespace TwinRestriction5495

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
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

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
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


end TwinRestriction5495

namespace TwinRestriction5495

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A NOT gate reads only its first wire: drop the others. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
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

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
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

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
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

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
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
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
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

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
input is the constant `b`. -/
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

/-- If no gate reads wire `n`, no other wire has the last input in its support. -/
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

/-- Gate elimination: fix the last input of `f` to `b`. If `f` depends on that input and the
restriction is not constant, a circuit of size `s + 1` for `f` gives one of size `s` for the
restriction. -/
theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
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
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
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
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
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
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end TwinRestriction5495

namespace TwinRestriction5495.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
`w - n + m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
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

/-- Renaming inputs along any map keeps the circuit size. -/
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

end TwinRestriction5495.PermInputs

namespace TwinRestriction5495
open PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 5) ||
    (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4)

def bull (y : Fin 5 → Bool) : Bool :=
  (y 0 && y 1) || (y 0 && y 2) || (y 0 && y 4) || (y 1 && y 2) || (y 1 && y 3)

/-- Original vertices in new coordinates, moving vertex 2 to the last wire. -/
private def coords : Fin 6 → Fin 6 := ![0,1,5,2,3,4]

/-- A physical six-gate circuit restricts to at most five gates on the bull. -/
theorem target_to_bull (h : HasCircuitSize 6 target 6) : HasCircuitSize 5 bull 5 := by
  let f : (Fin 6 → Bool) → Bool := fun x => target (x ∘ coords)
  have hc : HasCircuitSize 6 f 6 := PermInputs.relabel_size coords target 6 h
  have dep : ∃ x : Fin 6 → Bool, f (Function.update x (Fin.last 5) (!(x (Fin.last 5)))) ≠ f x := by
    refine ⟨fun i => decide (i = 0), ?_⟩
    change true ≠ false
    decide
  have nc : ∃ y z : Fin 5 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc z false) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    change false ≠ true
    decide
  have hcut := gate_elim 5 f false 5 dep nc hc
  have restrict_eq : (fun y : Fin 5 → Bool => f (Fin.snoc y false)) = bull := by
    funext y
    change ((y 0 && y 1) || (y 0 && false) || (y 0 && y 2) || (y 0 && y 4) ||
      (y 1 && y 2) || (y 1 && y 3) || (false && y 2) || (false && y 3)) = _
    simp [bull]
  rwa [restrict_eq] at hcut

end TwinRestriction5495

namespace BullFinite5495
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each bit is one adjacent pair of positive/negative assignments. A cut through
-- a computing circuit must distinguish the two assignments on every such pair.
private abbrev B := BitVec 24
private abbrev W := B × B
private def goal : W := (BitVec.allOnes 24, 0)
private def zero : W := (0,0)
private def one : W := (BitVec.allOnes 24, BitVec.allOnes 24)
private def raw : List W := [(0x4cf70f,0x41305),(0xb349f3,0x114052),(0xc38e3c,0xc28c28),
  (0xfc0fc0,0xec0f80),(0xfff000,0xfbe000)]
private def bank := zero :: one :: raw
private abbrev R := Bool × Fin 24
private def bit (q : R) (w : W) := (if q.1 then w.1 else w.2).getLsbD q.2.val
private inductive Op | meet | join | neg
private def run : Op → W → W → W
  | .meet,a,b => (a.1 &&& b.1,a.2 &&& b.2)
  | .join,a,b => (a.1 ||| b.1,a.2 ||| b.2)
  | .neg,a,_ => (~~~a.1,~~~a.2)
private def act : Op → Bool → Bool → Bool
  | .meet,a,b => a && b
  | .join,a,b => a || b
  | .neg,a,_ => !a
private theorem bit_run (o : Op) (a b : W) (q : R) : bit q (run o a b) = act o (bit q a) (bit q b) := by
  obtain ⟨s,i⟩ := q; cases o <;> cases s <;> simp [bit,run,act,i.isLt]

-- A straight-line program, with unused gates admissible via `idle`.
private inductive Prog : Finset W → ℕ → Prop
  | done {S k} : goal ∈ S → Prog S k
  | idle {S k} : Prog S k → Prog S (k+1)
  | step {S k a b} (o : Op) : a ∈ S → b ∈ S → Prog (insert (run o a b) S) k → Prog S (k+1)
private theorem mono {S k} (h : Prog S k) {T} (st : S ⊆ T) : Prog T k := by
  induction h generalizing T with
  | done m => exact .done (st m)
  | idle _ ih => exact .idle (ih st)
  | step o ha hb _ ih => exact .step o (st ha) (st hb) (ih (Finset.insert_subset_insert _ st))

-- Trace demand backwards: a gate can replace one needed word by at most two.
private theorem sparse {S k} (h : Prog S k) : ∃ T ⊆ S, T.card ≤ k+1 ∧ Prog T k := by
  induction h with
  | done m => exact ⟨{goal},by simpa,by simp,.done (by simp)⟩
  | idle _ ih => obtain ⟨T,sub,c,pr⟩ := ih; exact ⟨T,sub,by omega,.idle pr⟩
  | @step S k a b o ha hb _ ih =>
    obtain ⟨T,sub,c,pr⟩ := ih
    let z := run o a b
    by_cases need : z ∈ T
    · let U := insert a (insert b (T.erase z))
      refine ⟨U,?_,?_,.step (a:=a) (b:=b) o (by simp [U]) (by simp [U]) (mono pr ?_)⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl|hx; exact ha
        rcases Finset.mem_insert.mp hx with rfl|hx; exact hb
        exact (Finset.mem_insert.mp (sub (Finset.mem_erase.mp hx).2)).resolve_left (Finset.mem_erase.mp hx).1
      · have e := Finset.card_erase_of_mem need
        have p := Finset.card_insert_le b (T.erase z)
        have q := Finset.card_insert_le a (insert b (T.erase z)); dsimp [U]; omega
      · intro x hx; by_cases e : x=z
        · exact Finset.mem_insert.mpr (Or.inl e)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hx⟩)))
    · exact ⟨T,fun x hx => (Finset.mem_insert.mp (sub hx)).resolve_left (by rintro rfl; exact need hx),by omega,.idle pr⟩

private theorem onBits : ∀ i : Fin 24, (BitVec.allOnes 24).getLsbD i.val = true := by decide +kernel
private theorem splits {S k} (h : Prog S k) (i : Fin 24) : ∃ w ∈ S, bit (true,i) w ≠ bit (false,i) w := by
  induction h with
  | done m => exact ⟨goal,m,by change (BitVec.allOnes 24).getLsbD i.val ≠ (0:B).getLsbD i.val; rw [onBits]; simp⟩
  | idle _ ih => exact ih
  | @step S k a b o ha hb _ ih =>
    obtain ⟨w,hm,d⟩ := ih
    rcases Finset.mem_insert.mp hm with rfl|hm
    · rw [bit_run,bit_run] at d
      by_cases e : bit (true,i) a = bit (false,i) a
      · exact ⟨b,hb,fun f => d (by rw [e,f])⟩
      · exact ⟨a,ha,e⟩
    · exact ⟨w,hm,d⟩
private def mask : List W → B
  | [] => 0
  | w::ws => (w.1 ^^^ w.2) ||| mask ws
private theorem masked {L : List W} {k} (h : Prog L.toFinset k) : mask L = BitVec.allOnes 24 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨w,hw,sep⟩ := splits h ⟨i,hi⟩
  have hw' : w ∈ L := by simpa using hw
  have aux (l : List W) (m : w ∈ l) : (mask l).getLsbD i=true := by
    induction l with
    | nil => simp at m
    | cons x xs ih =>
      rcases List.mem_cons.mp m with rfl|m
      · simp only [bit,ite_true] at sep
        simp [mask,show ((w.1.getLsbD i) ^^ (w.2.getLsbD i)) = true by grind]
      · simp [mask,ih m]
  rw [show (BitVec.allOnes 24).getLsbD i = true from onBits ⟨i,hi⟩]; exact aux L hw'

private def candidates (l : List W) := (l.flatMap fun a => run .neg a a :: l.flatMap fun b => [run .meet a b,run .join a b]).dedup
private theorem candidate (l : List W) (o : Op) {a b} (ha : a ∈ l) (hb : b ∈ l) : run o a b ∈ candidates l := by
  simp only [candidates,List.mem_dedup,List.mem_flatMap,List.mem_cons]
  refine ⟨a,ha,?_⟩
  cases o with
  | neg => exact Or.inl rfl
  | meet => exact Or.inr ⟨b,hb,Or.inl rfl⟩
  | join => exact Or.inr ⟨b,hb,Or.inr (Or.inl rfl)⟩

private def check : ℕ → List W → Bool
  | 0,L => L.contains goal
  | k+1,L => L.sublists.any fun Q => decide (Q.length ≤ k+2) && (mask Q == BitVec.allOnes 24) &&
      (check k Q || (candidates Q).any (fun z => !(Q.contains z) && check k (z::Q)))

private theorem checked {L : List W} {k} (h : Prog L.toFinset k) : check k L=true := by
  induction k generalizing L with
  | zero => cases h with | done h => simpa [check] using h
  | succ k ih =>
    obtain ⟨T,sub,sz,pr⟩ := sparse h
    let Q := L.dedup.filter fun w => decide (w ∈ T)
    have eqT : Q.toFinset=T := by ext w; simp [Q]; exact fun h => (show w∈L by simpa using sub h)
    have mq : Q ∈ L.sublists := List.mem_sublists.mpr (List.filter_sublist.trans (List.dedup_sublist _))
    have len : Q.length ≤ k+2 := by
      rw [← List.toFinset_card_of_nodup (l:=Q) ((List.nodup_dedup L).filter _),eqT]; exact sz
    rw [← eqT] at pr
    apply List.any_eq_true.mpr; refine ⟨Q,mq,?_⟩
    simp only [decide_eq_true len,masked pr,beq_self_eq_true,Bool.true_and,Bool.or_eq_true]
    generalize hs : Q.toFinset=S at pr
    cases pr with
    | done m => left; exact ih (.done (hs ▸ m))
    | idle p => left; exact ih (hs ▸ p)
    | @step _ _ a b o ma mb p =>
      subst S
      by_cases old : run o a b ∈ Q
      · left; apply ih; simpa [Finset.insert_eq_of_mem (List.mem_toFinset.mpr old)] using p
      · right; apply List.any_eq_true.mpr
        refine ⟨_,candidate _ o (by simpa using ma) (by simpa using mb),?_⟩
        have yes := ih (L:=run o a b :: Q) (by simpa using p)
        simp [old,yes]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem excluded : check 5 bank=false := by decide +kernel

private def bull (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3)
private def sample (q : R) (i : Fin 5) := bit q (raw.getD i.val zero)
private theorem goal_bits : ∀ q : R, bull (sample q) = bit q goal := by decide +kernel
private theorem separate {a b : W} (h : ∀ q : R, bit q a = bit q b) : a=b := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact h (true,⟨i,hi⟩)
  · exact h (false,⟨i,hi⟩)
private def BStep (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private def Covers (S : Finset W) (w : R → List Bool) := ∀ i : ℕ, ∃ v ∈ S, ∀ q, bit q v = (w q).getD i false
private theorem gate {w : R → List Bool} {S : Finset W} (hr : Covers S w) (hz : zero ∈ S) (hu : one ∈ S)
    (g : Gate) (hm : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) (hlen : g.inputs.length≤2) :
    ∃ o a b, a∈S ∧ b∈S ∧ ∀ q, bit q (run o a b) = g.op.eval (g.inputs.map fun i => (w q).getD i false) := by
  obtain ⟨op,ins⟩ := g; change op=.and ∨ op=.or ∨ op=.not at hm; change ins.length≤2 at hlen
  have bz (q : R) : bit q zero=false := by obtain ⟨s,i⟩ := q; cases s <;> simp [bit,zero]
  have bu (q : R) : bit q one=true := by obtain ⟨s,i⟩ := q; cases s <;> exact onBits i
  cases ins with
  | nil => rcases hm with rfl|rfl|rfl
           · exact ⟨.meet,one,one,hu,hu,fun q => by simp [bit_run,act,bu,GateOp.eval]⟩
           · exact ⟨.join,zero,zero,hz,hz,fun q => by simp [bit_run,act,bz,GateOp.eval]⟩
           · exact ⟨.neg,zero,zero,hz,hz,fun q => by simp [bit_run,act,bz,GateOp.eval]⟩
  | cons i tl =>
    obtain ⟨a,ha,ea⟩ := hr i
    cases tl with
    | nil => rcases hm with rfl|rfl|rfl
             · exact ⟨.meet,a,a,ha,ha,fun q => by simp [bit_run,act,ea,GateOp.eval]⟩
             · exact ⟨.join,a,a,ha,ha,fun q => by simp [bit_run,act,ea,GateOp.eval]⟩
             · exact ⟨.neg,a,a,ha,ha,fun q => by simp [bit_run,act,ea,GateOp.eval]⟩
    | cons j rest => cases rest with
      | nil => obtain ⟨b,hb,eb⟩ := hr j; rcases hm with rfl|rfl|rfl
               · exact ⟨.meet,a,b,ha,hb,fun q => by simp [bit_run,act,ea,eb,GateOp.eval]⟩
               · exact ⟨.join,a,b,ha,hb,fun q => by simp [bit_run,act,ea,eb,GateOp.eval]⟩
               · exact ⟨.neg,a,a,ha,ha,fun q => by simp [bit_run,act,ea,GateOp.eval]⟩
      | cons t ts => simp at hlen
private theorem circuitProgram (gs : List Gate) (out : ℕ) (S : Finset W) (w : R → List Bool) (n : ℕ)
    (hm : FanInTwo ⟨gs,out⟩) (hr : Covers S w) (hz : zero∈S) (hu : one∈S) (len : ∀ q,(w q).length=n)
    (sem : ∀ q, (gs.foldl BStep (w q)).getD out false = bit q goal) : Prog S gs.length := by
  induction gs generalizing S w n with
  | nil => obtain ⟨v,m,e⟩ := hr out; exact .done (separate (fun q => (e q).trans (sem q)) ▸ m)
  | cons g gs ih =>
    obtain ⟨ho,hi⟩ := hm g (by simp)
    obtain ⟨o,a,b,ha,hb,ev⟩ := gate hr hz hu g ho hi
    apply Prog.step o ha hb
    apply ih _ (fun q => BStep (w q) g) (n+1) (fun u h => hm u (List.mem_cons_of_mem _ h)) _
      (Finset.mem_insert_of_mem hz) (Finset.mem_insert_of_mem hu) (fun q => by simp [BStep,len]) sem
    intro i
    by_cases eq : i=n
    · subst i; exact ⟨_,Finset.mem_insert_self ..,fun q => by simpa [BStep,← len q] using ev q⟩
    · obtain ⟨v,m,e⟩ := hr i
      refine ⟨v,Finset.mem_insert_of_mem m,fun q => ?_⟩
      by_cases lt : i<n
      · unfold BStep; rw [List.getD_append _ _ _ _ (show i < (w q).length by simpa [len] using lt)]; exact e q
      · rw [e q,List.getD_eq_default _ _ (by rw [len];omega),List.getD_eq_default _ _ (by simp [BStep,len];omega)]

/-- No fan-in-two AND/OR/NOT circuit of size five computes the five-input bull. -/
theorem noBull : ¬ HasCircuitSize 5 (fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3)) 5 := by
  rintro ⟨C,hm,sz,sem⟩
  have hc : Covers bank.toFinset (fun q => List.ofFn (sample q)) := by
    intro i; by_cases h : i<5
    · refine ⟨raw.getD i zero,?_,fun q => ?_⟩
      · have hr : i<raw.length := h
        apply List.mem_toFinset.mpr; simp only [bank,List.mem_cons]; right; right
        rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem _
      · simp only [List.getD,List.getElem?_ofFn,dif_pos h]; rfl
    · exact ⟨zero,by decide,fun q => by obtain ⟨s,j⟩ := q; cases s <;> simp [bit,zero,List.getD,List.getElem?_ofFn,h]⟩
  have pr := circuitProgram C.gates C.output bank.toFinset (fun q => List.ofFn (sample q)) 5 hm hc (by decide) (by decide)
    (by simp) (fun q => (sem (sample q)).trans (goal_bits q))
  have pad {k m : ℕ} {S} (p : Prog S k) (le : k ≤ m) : Prog S m := by induction le with | refl => exact p | step _ ih => exact .idle ih
  have h := checked (pad pr sz : Prog bank.toFinset 5)
  rw [excluded] at h; contradiction
end BullFinite5495

end PEqualNP.Outside.L_meta_5495

open PEqualNP.Outside.L_meta_5495 PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_5495 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4)) t → 7 ≤ t := by
  intro t ht
  by_contra! small
  obtain ⟨C,ok,sz,ev⟩ := ht
  have six : HasCircuitSize 6 TwinRestriction5495.target 6 := ⟨C,ok,by omega,ev⟩
  have five := TwinRestriction5495.target_to_bull six
  exact BullFinite5495.noBull five
