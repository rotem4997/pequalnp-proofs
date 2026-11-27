import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta170Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The constant-propagation pass and its evaluation invariant follow the project's
-- MetaComplexity helpers Shannon, Support and Elim. The size bound below counts every
-- use of the fixed input, including repeated occurrences of the same gate in the list.

-- Run gates on a wire list: the fold inside `Circuit.wires`.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

private lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

private lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

-- The allowed gates: AND, OR, NOT reading at most two wires.
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

-- A NOT gate reads only its first wire: drop the others.
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

-- An allowed gate whose NOT gates read at most one wire.
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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

private lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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

-- The status of an old wire: a constant, or the wire `j` of the new circuit.
abbrev Stat := Sum Bool ℕ

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

-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
-- next new wire. The result is the gate to emit, if any, and the status of the gate's wire.
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      (simp [simpAnd] at hg; all_goals (subst hg; simp [Ok]))
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      (simp [simpOr] at hg; all_goals (subst hg; simp [Ok]))
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      (simp [simpNot] at hg; all_goals (subst hg; simp [Ok]))
  · simp at hg
  · simp at hg

private lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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

private lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k
      · cases c <;> cases d <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases c <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases d <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k
      · cases c <;> cases d <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases c <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases d <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates.
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

private lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

private lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

private lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

private lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
-- and every old wire has a valid status whose value on the new wires is the old value.
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

private lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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

-- The statuses at the start: the first `n` old wires are the new input wires, and the last
-- input is the constant `b`.
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

private lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
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
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

private lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

private lemma norm_reads (n : ℕ) (g : Gate) :
    n ∈ (normGate g).inputs ↔
      (g.op = GateOp.not ∧ g.inputs.head? = some n) ∨
        (g.op ≠ GateOp.not ∧ n ∈ g.inputs) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [normGate]
  cases inputs <;> simp [eq_comm]

-- Each gate that reads the fixed input saves one gate in the new circuit.
private lemma elim_count (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ gs, NOk g) →
      k < acc.1.length → acc.1.getD k (.inl false) = .inl true →
      (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs)) ≤
        acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    let next := elimStep n acc g
    have hstep : elim n (g :: gs) acc = elim n gs next := rfl
    have htail := ih next (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [next, elimStep]; omega)
      (by
        dsimp only [next, elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega), hc])
    rw [hstep, List.length_cons, List.countP_cons]
    by_cases hread : k ∈ g.inputs
    · have hg := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.inl false))).1 = none :=
        simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2)
          (fun h => by simpa using hg.2 h)
          ⟨true, List.mem_map.2 ⟨k, hread, hc⟩⟩
      have hlen : next.2.length = acc.2.length := by
        change (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.inl false))).1.toList).length = _
        rw [hnone]
        simp
      simp only [hread, decide_true, ite_true]
      omega
    · have hlen : next.2.length ≤ acc.2.length + 1 := by
        simp only [next, elimStep, List.length_append]
        exact Nat.add_le_add_left (toList_length_le _) _
      simp only [hread, decide_false, Bool.false_eq_true, ite_false]
      omega

-- Changing just wire `n` preserves every other wire when no gate reads it.
private lemma eval_agree (n : ℕ) (gs : List Gate) :
    ∀ (w w' : List Bool), (∀ g ∈ gs, n ∉ g.inputs) →
      w.length = w'.length → (∀ j, j ≠ n → w.getD j false = w'.getD j false) →
      ∀ j, j ≠ n → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h j hj; exact h j hj
  | cons g gs ih =>
    intro w w' hno hl hag
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    let b' := g.op.eval (g.inputs.map fun i => w'.getD i false)
    have hbb : b = b' := by
      apply congrArg (g.op.eval)
      apply List.map_congr_left
      intro j hj
      exact hag j (fun h => hno g List.mem_cons_self (h ▸ hj))
    change ∀ j, j ≠ n →
      (wiresFrom gs (w ++ [b])).getD j false = (wiresFrom gs (w' ++ [b'])).getD j false
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [getD_snoc_len _ _ _ _ hjl.symm, getD_snoc_len _ _ _ _ (hl.symm.trans hjl.symm), hbb]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (hl ▸ hjl)]
      exact hag j hj

private lemma unique_read (n : ℕ) (C : Circuit) (ok : FanInTwo C)
    (depends : ∃ y : Fin n → Bool,
      circuitFun (n + 1) C (Fin.snoc y false) ≠ circuitFun (n + 1) C (Fin.snoc y true))
    (nonconstant : ∃ y y' : Fin n → Bool,
      circuitFun (n + 1) C (Fin.snoc y true) ≠ circuitFun (n + 1) C (Fin.snoc y' true))
    (bound : ∀ s, HasCircuitSize n (fun y => circuitFun (n + 1) C (Fin.snoc y true)) s →
      C.size ≤ s + 1) :
    ∃ j : Fin C.gates.length, n ∈ (normGate (C.gates.get j)).inputs ∧
      ∀ j' : Fin C.gates.length, n ∈ (normGate (C.gates.get j')).inputs → j' = j := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g₀ (ok g₀ hg₀)
  have heval (y : Fin n → Bool) (b : Bool) :
      (wiresFrom gs (List.ofFn y ++ [b])).getD C.output false =
        circuitFun (n + 1) C (Fin.snoc y b) := by
    rw [hgs, wiresFrom_norm, ← ofFn_snoc n y b]
    rfl
  have hout : C.output ≠ n := by
    intro h
    have hab (y : Fin n → Bool) : circuitFun (n + 1) C (Fin.snoc y true) = true := by
      rw [← heval, h, getD_wiresFrom _ _ _ (by simp),
        getD_snoc_len _ _ _ _ (by simp)]
    obtain ⟨y, y', hy⟩ := nonconstant
    exact hy ((hab y).trans (hab y').symm)
  have hread : ∃ g ∈ gs, n ∈ g.inputs := by
    by_contra! hnone
    obtain ⟨y, hy⟩ := depends
    apply hy
    rw [← heval, ← heval]
    apply eval_agree n gs _ _ hnone (by simp) _ _ hout
    intro j hj
    have hlen : (List.ofFn y).length = n := by simp
    rw [getD_snoc_ne _ _ _ _ (hlen.symm ▸ hj), getD_snoc_ne _ _ _ _ (hlen.symm ▸ hj)]
  let acc := elim n gs (initStats n true, [])
  have hval (y : Fin n → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        circuitFun (n + 1) C (Fin.snoc y true) := by
    have hi := inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1)
      (inv_init n true y)
    exact ((hi.2 C.output).2).trans (heval y true)
  have hsize : HasCircuitSize n (fun y => circuitFun (n + 1) C (Fin.snoc y true)) acc.2.length := by
    cases hst : acc.1.getD C.output (.inl false) with
    | inl b =>
      obtain ⟨y, y', hy⟩ := nonconstant
      exfalso
      apply hy
      rw [← hval y, ← hval y', hst]; rfl
    | inr j =>
      refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_rfl, ?_⟩
      intro y
      have hy := hval y
      rw [hst] at hy
      exact hy
  have hbound : C.gates.length ≤ acc.2.length + 1 := bound _ hsize
  have hsaved : acc.2.length + gs.countP (fun g => decide (n ∈ g.inputs)) ≤ gs.length := by
    simpa only [List.length_nil, zero_add] using
      elim_count n n gs (initStats n true, []) hnok (by simp [initStats])
        (getD_snoc_len _ _ _ _ (by simp))
  have hpos : 0 < gs.countP (fun g => decide (n ∈ g.inputs)) := by
    simpa only [List.countP_pos_iff, decide_eq_true_eq] using hread
  have hlen : gs.length = C.gates.length := by simp [hgs]
  have hone : gs.countP (fun g => decide (n ∈ g.inputs)) = 1 := by omega
  let users := (Finset.univ : Finset (Fin C.gates.length)).filter
    (fun j => n ∈ (normGate (C.gates.get j)).inputs)
  have hcard : gs.countP (fun g => decide (n ∈ g.inputs)) = users.card := by
    rw [hgs, List.countP_map]
    conv_lhs => rw [← List.ofFn_getElem (xs := C.gates)]
    rw [List.countP_ofFn]
    simp [users, List.get_eq_getElem]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hcard.symm.trans hone)
  have hmem (j' : Fin C.gates.length) : n ∈ (normGate (C.gates.get j')).inputs ↔ j' = j := by
    have : j' ∈ users ↔ j' = j := by rw [hj, Finset.mem_singleton]
    simpa [users] using this
  exact ⟨j, (hmem j).2 rfl, fun j' hj' => (hmem j').1 hj'⟩

end PEqualNP.Outside.LMeta170Helpers

open PEqualNP.Outside.LMeta170Helpers in
theorem PEqualNP.Outside.L_meta_170 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' true)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) s → C.size ≤ s + 1) → ∃ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) ∧ ∀ j' : Fin C.gates.length, ((C.gates.get j').op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j').inputs.head? = some n ∨ (C.gates.get j').op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j').inputs) → j' = j := by
  intro n C hminimal hdep hnonconstant hbound
  obtain ⟨j, hj, huniq⟩ := unique_read n C hminimal.1 hdep hnonconstant hbound
  exact ⟨j, (norm_reads n _).1 hj, fun j' hj' => huniq j' ((norm_reads n _).2 hj')⟩
