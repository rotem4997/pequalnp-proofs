import PEqualNP.Defs

/- The circuit normalization and parity arguments come from the project's
Shannon, Support, Elim, Parity, Parity3, and Parity4 helpers. The first-gate
analysis below needs global sensitivity only for the operands it uses.
The final applications establish the bounds for majority with zero, one,
and two independent parity inputs, then restrict the low bit of one addend. -/

/-!
# Shannon expansion as a straight-line program

Helper for `L-meta-001`. The construction is made at an arbitrary wire offset: the function
reads the first `k` wires of a wire list of length `m`, and the new gates are appended after
wire `m - 1`. So two subcircuits are put one after the other without renumbering any gate.
-/

namespace PEqualNP.Outside.L_meta_12302_aux.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

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

/-- The four gates that close one Shannon expansion step, appended to the wires `v`: with
`a = v[k]`, `p = v[o0]`, `q = v[o1]` they produce `(¬a ∧ p) ∨ (a ∧ q)` on the last wire. -/
theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_12302_aux.FirstGate


/-!
# Supports of wires

Helper for `L-meta-011`. Every wire gets a support: the set of inputs it can depend on, read
off the gates. Two facts: the value of a wire depends only on the inputs in its support, and
any set `W` of wires has a joint support of size at most (number of gates) + `|W|`, because a
gate of fan-in two replaces itself by at most two earlier wires.
-/

namespace PEqualNP.Outside.L_meta_12302_aux.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

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

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

/-- A function that depends on each of its `n` inputs has no circuit with fewer than `n - 1`
gates. -/
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.Outside.L_meta_12302_aux.FirstGate


/-!
# Gate elimination

Helper for `L-meta-014`. The last input of a circuit on `n + 1` inputs is fixed to `b`. One
pass over the gates gives every old wire a status: a constant, or an alias of a wire of the
new circuit on `n` inputs. A gate that reads a constant becomes a constant or an alias and is
not emitted, so if some gate reads the fixed input the new circuit is smaller. If no gate
reads it, the supports of `Support.lean` show the function does not depend on it.
-/

namespace PEqualNP.Outside.L_meta_12302_aux.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

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

end PEqualNP.Outside.L_meta_12302_aux.FirstGate


/-!
# Parity needs `2 (n - 1)` gates

Helper for `L-meta-020`. The pass of `Elim.lean` fixes the last input of a circuit to a
constant `b`. Here it is shown to save two gates for a suitable `b`, when the function depends
on the last input and both restrictions are non-constant. Either two gates read the fixed
input, or the only gate reading it becomes a constant for a suitable `b` and a later gate
reads that constant, or the output does not depend on the last input. Parity and its
complement satisfy the hypotheses, and their restrictions are again parity or its complement.
-/

namespace PEqualNP.Outside.L_meta_12302_aux.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-! ## The pass, cut at one gate -/

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
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

/-- A normalized allowed gate that reads a constant `b`, where `b` is `false` for an AND gate
and `true` for an OR gate, becomes a constant. -/
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
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

/-- A normalized allowed gate that reads a wire of constant status emits no gate. -/
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

/-- The value to give the fixed input so that a gate reading it becomes a constant. -/
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

/-! ## Supports -/

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

/-- If no gate reads a wire of the set `D`, no wire outside `D` gets the last input in its
support. -/
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

/-! ## Two gates saved -/

/-- If the output wire has the last input in its support and its status is never a constant,
then for some value of the last input the pass emits two gates fewer than it reads. -/
theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
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

/-- Gate elimination saving two gates: if `f` depends on its last input and stays non-constant
whichever value that input is fixed to, then for some value `b` the restriction has a circuit
with two gates fewer. -/
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
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

/-! ## Parity -/

/-- Parity of `n` bits: the number of true bits is odd. -/
def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

/-- Parity or its complement on `n + 1` inputs needs `2 n` gates. -/
theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

/-- Parity of `n` inputs needs at least `2 (n - 1)` gates. -/
theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

end PEqualNP.Outside.L_meta_12302_aux.FirstGate


/-!
# Parity needs `3 (n - 1)` gates

Helper for `L-meta-025`. The pass of `Elim.lean` is run from other starting statuses: with no
input fixed it only cleans a circuit (every emitted gate is a NOT of one earlier wire or an
AND or OR of two earlier wires), and with input `i` fixed to `b` it restricts the circuit.

In a clean circuit the first gate `g0` reads only inputs. Let `x` be one of them. Three gates
disappear when `x` is fixed to a suitable constant. Some gate `g2` other than `g0` reads `x` or
`g0`, because the output depends on `x`. If `g2` becomes a constant for a suitable value of
`x`, a third gate reads `x`, `g0` or `g2`. Otherwise `g2` reads `g0` and not `x`, and then
either another gate reads `x`, or `g0` is the only reader of `x`. In the last case `g0` reads
`x` only (then its value can be set either way, which makes `g2` a constant) or `g0` reads a
second input `y`, and fixing `y` to the absorbing constant makes the circuit independent of
`x`, which parity does not allow.
-/

namespace PEqualNP.Outside.L_meta_12302_aux.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-! ## Clean circuits -/

/-- A gate of a clean circuit, where `m` wires exist before it: a NOT of one earlier wire, or
an AND or OR of two earlier wires. -/
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

/-- A clean list of gates on `m` inputs. -/
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

/-- The pass emits a clean list of gates. -/
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

/-- A clean circuit with at most `s` gates computes `f`. -/
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

/-- The statuses at the start when no input is fixed. -/
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

/-- A circuit for a non-constant function can be cleaned without growing. -/
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

/-! ## Fixing input `i` -/

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

/-- The statuses at the start when input `i` is fixed to `b`: the other inputs are the new
input wires, in order. -/
def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
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
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

/-- The final status of old wire `a` when input `i` is fixed to `b`. -/
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

/-! ## The pass, position by position -/

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

/-- A gate that reads an earlier wire whose final status is the absorbing constant of the gate
has a constant final status. -/
theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

/-- Every position of `S` holds a gate that reads an earlier wire of constant final status: the
pass emits at least `|S|` gates fewer than it reads. -/
theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
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
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

/-! ## Readers -/

/-- `B` is a set of wires containing input `i`. If every gate outside `B` reads no wire of `B`,
no wire outside `B` has `i` in its support. -/
theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

/-- If the wire `o` outside `B` has `i` in its support, some gate outside `B` reads a wire of
`B`. -/
theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

/-- If no gate reads wire `k`, two wire lists that agree off `k` still agree off `k`. -/
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

/-! ## Three gates saved -/

/-- Position `p` holds a gate that reads a wire of constant final status. -/
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

/-- The core of the count. `g0` is the first gate and reads input `i`. Either the status of
`g0` can be made any constant, or another gate reads input `i`. -/
theorem three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  -- the third gate, once `g2` has a constant status under some `b`
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

/-- The final status of the first gate. -/
theorem stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)

/-- A first gate that reads only input `i` can be given either constant status. -/
theorem first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]

/-- The first gate is an AND or OR of the inputs `i` and `k`, and no other gate reads input
`i`: then the output does not depend on input `i` once input `k` is the absorbing constant. -/
theorem single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- In a clean circuit whose output flips with every input and is never a constant after one
input is fixed, some input and some value of it make the pass emit three gates fewer. -/
theorem three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)

/-! ## Parity -/

theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

/-- One step for parity or its complement: a clean circuit on `n + 2` inputs gives a clean
circuit on `n + 1` inputs with three gates fewer. -/
theorem clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Stat.const c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | const c' => exact absurd hst (hout i b c')
  | wire j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this

/-- A clean circuit for parity or its complement on `n + 1` inputs has at least `3 n` gates. -/
theorem par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega

/-- Parity of `n` inputs needs at least `3 (n - 1)` gates. -/
theorem parity_lower3 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.Outside.L_meta_12302_aux.FirstGate


/-!
# Parity needs `4 (n - 1)` gates

Helper for `L-meta-031`. Take a clean circuit of least size for parity or its complement on at
least two inputs. Least size gives two facts: no gate computes a constant, and no gate computes
the same function as an earlier wire, because such a gate can be dropped.

Fix one input to a constant and run the pass of `Elim.lean`. A gate is touched when it reads a
wire of constant status; touched gates are not emitted. It is shown that for some input and
some constant either four gates are touched, or three are touched and the restricted circuit
has a gate equal to an earlier wire, which is then dropped. So four gates are saved.

The argument, by contradiction. If two gates are constant for the same fixing, four gates are
touched. So no input has a NOT gate on it, and the first gate `G` is an AND or OR of two
inputs `x`, `y`. Each of `x`, `y` has exactly one other reader. If these readers differ, the
other reader of `x` copies `x` once `y` is fixed to the absorbing constant of `G`. If they are
the same gate `r`, then `G` has one reader `h1` and `r` has one reader `h2`, and each of the
second inputs of `h1`, `h2` must depend on the fixed input through the other gate, which the
order of the gates forbids.
-/

namespace PEqualNP.Outside.L_meta_12302_aux.FirstGate
open PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

/-! ## Values of wires -/

/-- The value of wire `j` of the gate list `gs` on the input `u`. -/
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

/-- An AND or OR gate with an input at its absorbing value has that value. -/
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

/-- Two inputs that agree outside the wire set `B` give wires that agree outside `B`, below the
bound `L`, as soon as every gate outside `B` that reads `B` agrees whenever the earlier wires
outside `B` do. -/
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

/-- A wire that is not a constant function takes both values. -/
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

/-! ## Dropping a gate -/

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
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
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

/-- A gate that computes the same function as an earlier wire can be dropped. -/
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
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

/-- A gate that computes a constant can be dropped. -/
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

/-! ## Statuses -/

/-- The input `y` with the value `b` inserted at position `i`. -/
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

/-- The gates the pass emits when input `i` is fixed to `b`. -/
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

/-- The final status of wire `a` is a constant when input `i` is fixed to `b`. -/
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

/-- The final status of a gate is what `simplify` makes of the final statuses of its inputs. -/
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
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem three_at (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (p0 : Nat) (g0 : Gate) (h0 : gs[p0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1 + p0) = Stat.const c) ∨
      ∃ p' g', p' ≠ p0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1 + p0) = Stat.const c0 :=
    hrd (fixBit g0) p0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 + p0 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b p0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1 + p0) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ p0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  -- the third gate, once `g2` has a constant status under some `b`
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ p0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 + p0 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 + p0 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 + p0 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1 + p0) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b p0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1 + p0, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) p0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1 + p0, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

end PEqualNP.Outside.L_meta_12302_aux.FirstGate

namespace PEqualNP.Outside.L_meta_12302_aux.FirstGate
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

theorem circuit_of_clean {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (h : HasClean n f s) : HasCircuitSize n f s := by
  obtain ⟨gs, o, hcl, hs, he⟩ := h
  exact ⟨⟨gs,o⟩, fun g hg => (clean_nok n gs hcl g hg).1, hs, he⟩

theorem unrestrictedHeavyLower (n cap : ℕ) (f : (Fin (n + 1) → Bool) → Bool)
    (heavy : Fin (n + 1) → Prop) (hheavy : ∃ i, heavy i)
    (hess : ∀ i, ∃ u, f (Function.update u i (!u i)) ≠ f u)
    (hnc : ∀ i b, ∃ y y' : Fin n → Bool, f (ins i b y) ≠ f (ins i b y'))
    (hlow : ∀ i, heavy i → ∀ u : Fin (n + 1) → Bool, ∃ v,
      (∀ j, ¬ heavy j → v j = u j) ∧ f (Function.update v i (!v i)) ≠ f v)
    (hpair : ∀ i, heavy i → ∀ j, heavy j → i ≠ j → ∀ b, ∃ u,
      u j = b ∧ f (Function.update u i (!u i)) ≠ f u)
    (hcofactor : ∀ i, heavy i → ∀ b s,
      HasCircuitSize n (fun x => f (ins i b x)) s → cap < s + 3) :
    ¬ HasCircuitSize (n + 1) f cap := by
  classical
  intro h
  obtain ⟨u, hu⟩ := hess 0
  have hf : ∃ v v', f v ≠ f v' := ⟨_, _, hu⟩
  have hc := clean_of (n + 1) f cap hf h
  have hex : ∃ s, HasClean (n + 1) f s := ⟨cap, hc⟩
  obtain ⟨gs, o, hcl, hs, he⟩ := Nat.find_spec hex
  have hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x := he
  have hlen := hs.trans (Nat.find_min' hex hc)
  have hmin : ∀ gs' o', CleanL (n + 1) gs' → (∀ x, vl gs' x o' = f x) →
      gs.length ≤ gs'.length := by
    intro gs' o' hc' he'
    exact hs.trans (Nat.find_min' hex ⟨gs', o', hc', Nat.le_refl _, he'⟩)
  have hnc' : ∃ y y' : Fin (n + 1) → Bool, vl gs y o ≠ vl gs y' o := by
    obtain ⟨y, y', hy⟩ := hf
    exact ⟨y, y', by simpa only [hev] using hy⟩
  have hconst : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ x : Fin (n + 1) → Bool, vl gs x (n + 1 + p) = c := by
    intro p g hp c hh
    have hp' := (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1) gs hcl o p c hp' hh hnc'
    have := hmin gs' o' hc' (fun x => (he' x).trans (hev x))
    omega
  have halias : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
      ¬ ∀ x : Fin (n + 1) → Bool, vl gs x (n + 1 + p) = vl gs x j := by
    intro p g hp j hj hh
    have hp' := (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias (n + 1) gs hcl o p j hp' hj hh hnc'
    have := hmin gs' o' hc' (fun x => (he' x).trans (hev x))
    omega
  have hout : ∀ i b c, stF n gs i b o ≠ Stat.const c := by
    intro i b c hh
    obtain ⟨y, y', hy⟩ := hnc i b
    apply hy
    rw [← hev, ← hev, st_val_const n gs hcl i b o c hh y, st_val_const n gs hcl i b o c hh y']
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    obtain ⟨v, hv⟩ := hess i
    by_contra hns
    apply hv
    rw [← hev, ← hev]
    exact (agree_wiresFrom (Function.update v i (!v i)) v gs _ _ _ (agree_inputs _ _)).2.2 o (by
      intro j hj
      have hji : j ≠ i := fun e => hns (e ▸ hj)
      simp [Function.update_of_ne hji])
  have hoi : ∀ i : Fin (n + 1), o ≠ i := fun i e =>
    hout i false false (by rw [e]; exact stF_self n gs i false)
  let B : ℕ → Prop := fun w => ∃ i : Fin (n + 1), heavy i ∧ i.val = w
  have hoB : ¬ B o := by
    rintro ⟨i, _, hi⟩
    exact hoi i hi.symm
  obtain ⟨i0, hi0⟩ := hheavy
  have hxg : ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ ∃ w ∈ g.inputs, B w := by
    obtain ⟨p, g, hp, _, hpg⟩ :=
      exists_reader (n + 1) i0 B ⟨i0, hi0, rfl⟩ gs o hoB (hsupp i0)
    exact ⟨p, g, hp, hpg⟩
  let p := Nat.find hxg
  obtain ⟨g, hp, a, ha, i, hi, hia⟩ := Nat.find_spec hxg
  have hp' : gs[p]? = some g := hp
  have hread : i.val ∈ g.inputs := hia.symm ▸ ha
  have hprior : ∀ (q : Nat) (g' : Gate), gs[q]? = some g' → q < p → ¬ ∃ w ∈ g'.inputs, B w := by
    intro q g' hq hqp hw
    exact (not_le_of_gt hqp) (Nat.find_min' hxg ⟨g', hq, hw⟩)
  have noThree (halt : (∀ c, ∃ b, stF n gs i b (n + 1 + p) = Stat.const c) ∨
      ∃ (q : Nat) (g' : Gate), q ≠ p ∧ gs[q]? = some g' ∧ i.val ∈ g'.inputs) : False := by
    obtain ⟨b, hb⟩ := three_at n gs hcl o hsupp hout p g hp' i hread halt
    cases hst : stF n gs i b o with
    | const c => exact hout i b c hst
    | wire j =>
      have hpass : CleanL n (passG n gs i b) :=
        clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
          (fun g' hg' => (clean_nok _ gs hcl g' hg').1) (inv_at n i b _)
          (by intro q g' hq; simp at hq)
      have hnew : HasClean n (fun x => f (ins i b x)) (passG n gs i b).length :=
        ⟨_, j, hpass, Nat.le_refl _, fun x =>
          (st_val_wire n gs hcl i b o j hst x).symm.trans (hev _)⟩
      have hc := hcofactor i hi b _ (circuit_of_clean hnew)
      change (passG n gs i b).length + 3 ≤ gs.length at hb
      omega
  have binary (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
      (w : ℕ) (hw : w ∈ g.inputs) (hwi : w ≠ i.val) : False := by
    apply noThree
    right
    by_contra hno
    have hpLim : p < gs.length := (List.getElem?_eq_some_iff.1 hp').1
    have hwLim : w < n + 1 + p := (hcl p g hp').lt w hw
    have hprefix (x x' : Fin (n + 1) → Bool) (heq : ∀ j, ¬ heavy j → x j = x' j)
        (hwB : ¬ B w) : vl gs x w = vl gs x' w := by
      refine agree_B gs hcl x x' B (n + 1 + p) ?_ ?_ w hwLim hwB
      · intro j hj hjB
        rw [vl_input gs x j hj, vl_input gs x' j hj]
        exact heq ⟨j, hj⟩ (fun h => hjB ⟨⟨j, hj⟩, h, rfl⟩)
      · intro q g' hq hbound _ hgate _
        exact (hprior q g' hq (by omega) hgate).elim
    have hx : ∃ x, vl gs x w = fixBit g ∧
        vl gs (Function.update x i (!x i)) w = fixBit g ∧
        f (Function.update x i (!x i)) ≠ f x := by
      by_cases hwB : B w
      · obtain ⟨j, hj, hjw⟩ := hwB
        have hjne : j ≠ i := fun e => hwi (hjw.symm.trans (congrArg Fin.val e))
        obtain ⟨x, hx, hdiff⟩ := hpair i hi j hj hjne.symm (fixBit g)
        have hwRaw : w < n + 1 := hjw ▸ j.isLt
        have hjEq : (⟨w, hwRaw⟩ : Fin (n + 1)) = j := Fin.ext hjw.symm
        refine ⟨x, ?_, ?_, hdiff⟩
        · rw [vl_input gs x w hwRaw, hjEq, hx]
        · rw [vl_input gs _ w hwRaw, hjEq, Function.update_of_ne hjne, hx]
      · obtain ⟨u, hu⟩ := takes gs hconst w (by omega) (fixBit g)
        obtain ⟨x, hx, hdiff⟩ := hlow i hi u
        have hx' : ∀ j, ¬ heavy j → Function.update x i (!x i) j = u j := by
          intro j hj
          rw [Function.update_of_ne (fun e : j = i => hj (e.symm ▸ hi)), hx j hj]
        exact ⟨x, (hprefix x u hx hwB).trans hu, (hprefix _ u hx' hwB).trans hu, hdiff⟩
    obtain ⟨x, hx, hx', hdiff⟩ := hx
    apply hdiff
    rw [← hev, ← hev]
    refine agree_B gs hcl _ _ (fun w => w = i.val) (o + 1) ?_ ?_ o (by omega) (hoi i)
    · intro j hj hjne
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne (fun e => hjne (congrArg Fin.val e)) _ _
    · intro q g' hq _ _ hreads _
      obtain ⟨k, hk, hki⟩ := hreads
      have hki' : k = i.val := hki
      have hqp : q = p := by
        by_contra hne
        exact hno ⟨q, g', hne, hq, hki' ▸ hk⟩
      subst q
      have hg' : g' = g := gate_eq hq hp' rfl
      subst g'
      rw [vl_abs gs hcl _ p g hp' hop w hw hx', vl_abs gs hcl x p g hp' hop w hw hx]
  rcases hcl p g hp' with ⟨hop,j,hj,hin⟩ | ⟨hop,j,k,hj,hk,hin⟩
  · have hji : j = i.val := by
      have hh : i.val = j := by simpa [hin] using hread
      exact hh.symm
    apply noThree
    left
    intro c
    obtain ⟨t, ht⟩ := st_gate n gs hcl i (!c) p g hp'
    refine ⟨!c, ?_⟩
    rw [ht, hop, hin, hji]
    simp [stF_self, simplify, simpNot]
  · have hr : i.val = j ∨ i.val = k := by
      have hh := hread
      rw [hin] at hh
      simpa using hh
    by_cases hsame : j = k
    · subst k
      apply halias p g hp' j hj
      intro x
      rw [vl_gate gs hcl x p g hp', hin]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · rcases hr with h | h
      · exact binary hop k (by rw [hin]; simp) (by omega)
      · exact binary hop j (by rw [hin]; simp) (by omega)

end PEqualNP.Outside.L_meta_12302_aux.FirstGate

namespace PEqualNP.Outside.L_meta_12302_aux.Cofactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

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

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

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
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
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

/-! ## Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

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

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
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

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
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


theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

/-! ## NOT-free circuits give NOT-free Runs (a copy of run_live with the NOT branch removed) -/

theorem simplify_nonot (op : GateOp) (hop : op ≠ GateOp.not) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op ≠ GateOp.not := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp)
  · exact absurd rfl hop
  · simp at hg
  · simp at hg

theorem elim_nonot (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, g.op ≠ GateOp.not) → (∀ g ∈ acc.2, g.op ≠ GateOp.not) →
    ∀ g ∈ (elim n gs acc).2, g.op ≠ GateOp.not := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hg h
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_nonot _ (hg g List.mem_cons_self) _ _ g' (by simpa using h1)

theorem exists_clean_m (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ gs o, CleanL n gs ∧ (∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hC, hsz, hev⟩ := h
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
    refine ⟨acc.2, j, hcl, fun p g hp => elim_nonot n C.gates (initId n, []) hC (fun _ h => by simp at h) g (List.mem_of_getElem? hp), hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

open Classical in
theorem run_live_m (n : ℕ) (inv : BFn n → BFn n) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hm : ∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run inv meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
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
          val gs n (n + p) = (if neg then inv (val gs n j) else val gs n j) →
          Run inv meetF joinF (val gs n o) (d' + 1)
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
      · exact absurd hop (hm p g hg)
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

theorem exists_run_m {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a => a) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hm, hlen, ho, hev⟩ := exists_clean_m n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live_m n (fun a => a) gs o hcl hm ho gs.length 0 (by omega)
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


/-! ## Family 1: a certified frontier search (Run states closed under the moves of `next`) -/

theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩

/-- bit `i` is set when some wire differs at points `i` and `d + i` -/
def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

/-- the union of the wires that are false at point `q` -/
def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)

/-- `pD` entries `(d, R)`: every bit `i` of `R` has `y i ≠ y (d + i)`, both inside the mask.
`pM` entries `(q, P)`: `y q` is false and every bit of `P` is a true point of `y`. -/
def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      apply land_of
      intro p hpP
      have hyp : y.testBit p = true := land_sub h1.1 hpP
      by_contra hc
      have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
        intro w hw
        cases h2 : w.testBit p
        · exact Bool.false_le _
        · cases h3 : w.testBit qp.1
          · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
          · exact le_refl _
      have := bits_le h hlen p qp.1 hle
      rw [hyp, h1.2] at this
      exact absurd this (by decide)
    · left; simpa using hlen

/-- a bit map of tables: bit `k` of `actL pi w` is bit `pi[k]` of `w` (a symmetry of the target) -/
def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

/-- a successor not stored as it is may be stored up to the symmetry named by its hint -/
def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, hc, hg] at hmem
    simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr


/-- the table index, written out for five inputs -/
def idx5 (x : Fin 5 → Bool) : ℕ :=
  (if x 0 then 2 ^ 0 else 0) + (if x 1 then 2 ^ 1 else 0) + (if x 2 then 2 ^ 2 else 0) +
    (if x 3 then 2 ^ 3 else 0) + (if x 4 then 2 ^ 4 else 0)

theorem sum_eq (x : Fin 5 → Bool) : (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) = idx5 x := by
  rw [Fin.sum_univ_five]; rfl

/-- a function true at the all-false input needs a gate -/
theorem one_le {n : ℕ} (f : BFn n) (hf : f (fun _ => false) = true) :
    ∀ s, HasCircuitSize n f s → 1 ≤ s := by
  intro s hs
  obtain ⟨C, _, hle, hC⟩ := hs
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · exfalso
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hle)
    have h1 := hC (fun _ => false)
    rw [hf] at h1
    have e : C.eval (List.ofFn fun _ : Fin n => false) = false := by
      unfold Circuit.eval Circuit.wires
      rw [hg, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split <;> rfl
    rw [e] at h1
    exact Bool.false_ne_true h1
  · exact hpos


namespace RestrictionCertificate

def L_ : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

def M_ : Nat := 4294967295

def Y_ : Nat := 3901261952

def XS_ : List Nat := [2863311530,3435973836,4042322160,4278255360,4294901760]

def PD_ : List (Nat × Nat) := [(8,6291464),(1,483183808),(16,24584),(4,100663304),(2,313174688),(3,362387856),(6,53127842),(7,22649233),(14,207522),(17,31940),(20,1544),(24,104),(15,88465)]

def PM_ : List (Nat × Nat) := [(13,3901261952),(22,3901261952),(3,3901261952),(14,3901261952),(28,3901261952),(25,3901261952),(26,3901261952),(21,3901261952)]

def G_ : List (List Nat) := [[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31],[0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31],[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31],[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31],[0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31],[0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31],[0,2,1,3,8,10,9,11,16,18,17,19,24,26,25,27,4,6,5,7,12,14,13,15,20,22,21,23,28,30,29,31],[0,2,1,3,16,18,17,19,4,6,5,7,20,22,21,23,8,10,9,11,24,26,25,27,12,14,13,15,28,30,29,31],[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31]]

abbrev v0 : Nat := 4294901760
abbrev v1 : Nat := 3435973836
abbrev v2 : Nat := 4278255360
abbrev v3 : Nat := 2863311530
abbrev v4 : Nat := 4042322160
abbrev v5 : Nat := 2290649224
abbrev v6 : Nat := 4026593280
abbrev v7 : Nat := 2694881440
abbrev v8 : Nat := 3772834016
abbrev v9 : Nat := 65535
abbrev va : Nat := 4293984240
abbrev vb : Nat := 858993459
abbrev vc : Nat := 4008636142
abbrev vd : Nat := 2829625512
abbrev ve : Nat := 4037079200
abbrev vf : Nat := 4210752250
abbrev v10 : Nat := 4026531840
abbrev v11 : Nat := 4294967040
abbrev v12 : Nat := 2863311520
abbrev v13 : Nat := 4294967280
abbrev v14 : Nat := 3993038336
abbrev v15 : Nat := 2862656160
abbrev v16 : Nat := 4278190080
abbrev v17 : Nat := 4294963440
abbrev v18 : Nat := 3768639648
abbrev v19 : Nat := 4194368000
abbrev v1a : Nat := 3233857728
abbrev v1b : Nat := 4289396650
abbrev v1c : Nat := 4042260480
abbrev v1d : Nat := 4034982016

def K_0 : List (List Nat × List (Nat × Nat)) := [([2,2829625504,v1,v10],[]),([2,v15,v1,4169662464],[]),([2,2863180448,v1,v10],[]),([2,v12,3435973824,v10],[]),([2,v12,v1,v10],[]),([3,v5,3758153728,4277206768,v0],[]),([3,v5,3758153728,va,v0],[]),([3,v5,3766542464,v14,v0],[]),([3,v5,3766542464,v2,v0],[]),([3,v5,3768623264,v2,v0],[]),([3,v5,v18,v14,v0],[]),([3,v5,v18,4004118528,v2],[]),([3,v5,v18,v2,v0],[]),([3,v5,3772833952,v2,v0],[]),([3,v5,v8,v14,4008574976],[]),([3,v5,v8,v14,v0],[]),([3,v5,v8,4160813056,v0],[]),([3,v5,v8,v19,v0],[]),([3,v5,v8,4261477888,v0],[]),([3,v5,v8,v16,v11],[]),([3,v5,v8,4278224896,v0],[]),([3,v5,v8,4278233600,v0],[]),([3,v5,v8,4278251008,v0],[]),([3,v5,v8,v2,v0],[]),([3,v5,v8,v2,4294906129],[]),([3,v5,v8,v2,4294934656],[]),([3,v5,v8,v2,4294936576],[]),([3,v5,3772838128,v2,v0],[]),([3,v5,3907053792,v2,v0],[]),([3,v5,3938511552,v6,v0],[]),([3,v5,4007718624,v6,v0],[]),([3,v7,2852170240,3364407432,v0],[]),([3,v7,2852170240,v1,4205445120],[]),([3,v7,2863311360,v1,v10],[]),([3,v7,3364391048,v2,v0],[]),([3,2827528328,3435187392,v6,v0],[])]

def K_1 : List (List Nat × List (Nat × Nat)) := [([3,2829625504,v1,v6,v0],[]),([3,2829625504,v1,v4,v16],[]),([3,v15,v1,v6,4205445120],[]),([3,v15,v1,4169726088,v0],[]),([3,2863180448,v1,v6,v0],[]),([3,2863180448,v1,v1c,v2],[]),([3,v12,v3,v1,v10],[]),([3,v12,3435973824,v6,v0],[]),([3,v12,v1,v10],[]),([3,v12,v1,v10,v6],[]),([3,v12,v1,v10,v4],[]),([3,v12,v1,v10,va],[]),([3,v12,v1,v10,v13],[]),([3,v12,v1,v6,v1c],[]),([3,v12,v1,v6,4293918720],[]),([3,v12,v1,v6,v0],[]),([3,v3,v1,v10,4210752240],[(108,5)]),([3,v3,v1,v10,4294639600],[(108,5)]),([3,v3,v1,v10,v13],[(108,5)]),([3,v3,v1,4026532080,v11],[]),([3,v3,v1,v6,4294905840],[]),([3,v3,v1,v6,4294936704],[]),([3,v3,v1,4026597360,v0],[]),([3,v3,v1,4034953344,v11],[(100,2),(108,8)]),([3,v3,v1,v1d,4294936576],[]),([3,v3,v1,v4,4287137792],[]),([4,61680,v3,v1,4026597120,v0],[]),([4,65520,v3,v1,v6,v0],[]),([4,v9,v5,v8,v2],[]),([4,v9,v5,v8,v2,v0],[]),([4,v9,v5,4008574976,v4,v2],[]),([4,v9,2863267840,3435956360,v4,v2],[]),([4,16776960,v3,v1,v4,v16],[(96,2)]),([4,286331153,v5,v8,v2,v0],[(96,0)]),([4,286392319,v5,4008574976,v4,v2],[]),([4,286392319,v5,v4,v2],[(2,3)])]

def K_2 : List (List Nat × List (Nat × Nat)) := [([4,vb,v5,v8,v2,v0],[]),([4,1717986918,v5,v4,v2,v0],[]),([4,1886449904,v3,v1,v2,v0],[]),([4,2004318071,v5,v8,v2,v0],[]),([4,2004318071,v8,v2,v0],[]),([4,2155905152,v5,v8,v2,v0],[(96,0)]),([4,2155905152,v5,v14,v4,v0],[(56,1),(72,1),(96,1),(128,1)]),([4,2155905152,v3,v1,4160813056,v0],[(96,3),(128,1)]),([4,2290124928,v3,v1,v6,v0],[(96,3)]),([4,v5,v5,v8,v2,v0],[]),([4,v5,2684395520,v1a,v2,v0],[(80,5)]),([4,v5,v7,v1a,v2,v0],[]),([4,v5,v7,3368601800,v2,v0],[]),([4,v5,v7,3422604288,v6,v0],[(80,1)]),([4,v5,v7,v1,4160813056,v0],[]),([4,v5,v7,v1,v19,v0],[]),([4,v5,v7,v8,v2,v0],[]),([4,v5,v7,3959483392,v4,v0],[(104,7)]),([4,v5,v7,v14,v4,v0],[(104,1)]),([4,v5,v15,v1,v6,v0],[]),([4,v5,v3,v18,v2,v0],[]),([4,v5,v3,3770736832,v2,v0],[(60,5)]),([4,v5,v3,v8,v14,v0],[]),([4,v5,v3,v8,v2,v0],[]),([4,v5,3758153728,v8,v2,v0],[(112,1)]),([4,v5,3758153728,v4,v2,v0],[]),([4,v5,v18,4004179626,v2,v0],[]),([4,v5,v18,v4,v2,v0],[]),([4,v5,v18,v2,v0],[]),([4,v5,v8,v8,v2,v0],[]),([4,v5,v8,3907578088,v2,v0],[(116,1),(148,3)]),([4,v5,v8,3941264106,v2,v0],[(116,1),(148,3)]),([4,v5,v8,v14,vc,v0],[]),([4,v5,v8,v14,v4,v0],[(104,1)]),([4,v5,v8,v14,v0],[]),([4,v5,v8,vc,v2,v0],[(148,0)])]

def K_3 : List (List Nat × List (Nat × Nat)) := [([4,v5,v8,v6,v2,v0],[]),([4,v5,v8,v4,v2,v0],[]),([4,v5,v8,4177066232,v2,v0],[(148,0)]),([4,v5,v8,vf,v2,v0],[(148,0)]),([4,v5,v8,4278124286,v2,v0],[(148,0)]),([4,v5,v8,v16,v2,v0],[]),([4,v5,v8,v2,v2,v0],[]),([4,v5,v8,v2,4287168392,v0],[(156,0)]),([4,v5,v8,v2,v1b,v0],[(156,0)]),([4,v5,v8,v2,4292935648,v0],[(84,1)]),([4,v5,v8,v2,4293853166,v0],[(156,0)]),([4,v5,v8,v2,va,v0],[]),([4,v5,v8,v2,v0],[]),([4,v5,v8,v2,v0,v11],[]),([4,v5,3907578088,v4,v2,v0],[(108,1),(140,3)]),([4,v5,3937069738,v4,v2,v0],[(108,1),(140,3)]),([4,v5,3938511552,v4,v2,v0],[(84,5),(108,1)]),([4,v5,3941264106,v4,v2,v0],[(108,1),(140,3)]),([4,v5,4007718624,v4,v2,v0],[(108,1)]),([4,v5,4008373994,v4,v2,v0],[(108,1),(140,3)]),([4,v5,vc,v6,va,v0],[(140,3)]),([4,v5,vc,v1d,v2,v0],[(108,1),(140,3)]),([4,v5,vc,ve,v2,v0],[(108,1),(140,3)]),([4,v5,vc,4041273568,v2,v0],[(108,1),(140,3)]),([4,v5,vc,v4,v2,v0],[(108,1),(140,3)]),([4,v5,vc,v4,v2,4294906129],[(108,1),(140,3)]),([4,v5,vc,v4,v2,4294934656],[(108,1),(140,3)]),([4,v5,4008640511,v4,v2,v0],[(108,1),(140,3)]),([4,2576980377,vc,v4,v2,v0],[]),([4,v7,2852170240,v1,4205509290,v0],[]),([4,v7,2863311360,v1,v6,v0],[]),([4,v7,2863311360,v1,v4,v16],[(56,2)]),([4,v7,v3,3364407432,v2,v0],[]),([4,v7,v3,3368601800,v19,v0],[]),([4,v7,v3,3368601800,v2,v0],[]),([4,v7,v3,v1,3925928448,v0],[])]

def K_4 : List (List Nat × List (Nat × Nat)) := [([4,v7,v3,v1,v10,v11],[(128,2)]),([4,v7,v3,v1,4026597120,v0],[]),([4,v7,v3,v1,4160813056,v0],[]),([4,v7,v3,v1,4194347520,v0],[(140,0)]),([4,v7,v3,v1,v19,4210688000],[]),([4,v7,v3,v1,v19,v0],[]),([4,v7,v1,4205488810,v2,v0],[]),([4,2827520136,v1,v4,v2,v0],[(84,5),(108,7),(140,9)]),([4,2827528328,v1,v6,va,v0],[]),([4,2827528328,v1,4039176384,v2,v0],[]),([4,2827528328,v1,v4,4241227776,v2],[]),([4,2827528328,v1,v4,v2,v0],[]),([4,2829101216,v3,v1,v6,v0],[]),([4,2829625480,v1,v4,v2,v0],[]),([4,2829625504,v1,v4,v2,v0],[(148,0)]),([4,vd,3368601800,v4,v2,v0],[]),([4,vd,3431517320,v4,v2,v0],[]),([4,vd,v1,v8,v2,v0],[]),([4,vd,v1,3959483392,v4,v0],[(60,7)]),([4,vd,v1,v14,v4,v0],[(60,1)]),([4,vd,v1,v6,va,v0],[]),([4,vd,v1,ve,v2,v0],[]),([4,vd,v1,4039176384,v2,v0],[]),([4,vd,v1,v4,4160813056,v0],[]),([4,vd,v1,v4,v19,v0],[]),([4,vd,v1,v4,4227922944,4244373504],[]),([4,vd,v1,v4,4227922944,v0],[]),([4,vd,v1,v4,4261477888,v0],[]),([4,vd,v1,v4,v16,v11],[]),([4,vd,v1,v4,4278233088,v0],[]),([4,vd,v1,v4,4278233600,v0],[]),([4,vd,v1,v4,4278242304,v0],[]),([4,vd,v1,v4,4278254592,v0],[]),([4,vd,v1,v4,v2,v0],[]),([4,vd,v1,v4,v2,4294902531],[]),([4,vd,v1,4092851187,v2,v0],[])]

def K_5 : List (List Nat × List (Nat × Nat)) := [([4,vd,v1,4176541936,v2,v0],[]),([4,vd,v1,4210096880,v2,v0],[]),([4,vd,3486502863,v4,v2,v0],[]),([4,2829626026,v1,v4,v2,v0],[]),([4,v15,v3,v1,v10,v0],[(128,3),(140,3)]),([4,v15,v3,v1,v6,v0],[]),([4,v15,v1,v6,4205509290,v0],[(108,5)]),([4,2863179944,v1,v4,v2,v0],[]),([4,2863180448,v1,v4,v2,v0],[(156,1)]),([4,2863180456,v1,v6,va,v0],[]),([4,2863180456,v1,4039176384,v2,v0],[]),([4,2863180456,v1,v4,4244373504,v2],[]),([4,2863180456,v1,v4,v2,4294705152],[]),([4,2863180456,v1,v4,v2,v0],[]),([4,v12,v3,v1,v6,v0],[]),([4,v12,3435973824,v4,v2,v0],[(148,0),(156,2)]),([4,v12,v1,v6,v4,v0],[]),([4,v12,v1,v6,va,v0],[]),([4,v12,v1,v6,v0],[(117,3)]),([4,v12,v1,v6,v0,v17],[(116,0)]),([4,v12,v1,v6,v0,v13],[]),([4,v12,v1,4042321920,v2,v0],[(148,0),(156,2)]),([4,v12,v1,v4,v2,v0],[(148,0),(156,2)]),([4,2863311528,v1,v4,v2,v0],[]),([4,v3,v1,3758153728,4277206768,v0],[]),([4,v3,v1,3758153728,va,v0],[]),([4,v3,v1,3768623264,v2,v0],[]),([4,v3,v1,v18,v14,v0],[]),([4,v3,v1,v18,4004118528,v2],[]),([4,v3,v1,v18,v2,v0],[]),([4,v3,v1,3772833952,v2,v0],[]),([4,v3,v1,v8,v14,4008574976],[]),([4,v3,v1,v8,v14,v0],[]),([4,v3,v1,v8,v19,v0],[]),([4,v3,v1,v8,4261477888,v0],[]),([4,v3,v1,v8,v16,v11],[])]

def K_6 : List (List Nat × List (Nat × Nat)) := [([4,v3,v1,v8,4278233600,v0],[]),([4,v3,v1,v8,4278251008,v0],[]),([4,v3,v1,v8,v2,v0],[]),([4,v3,v1,v8,v2,4294906129],[]),([4,v3,v1,3772838128,v2,v0],[]),([4,v3,v1,3938511552,v6,v0],[]),([4,v3,v1,4007718624,v6,v0],[]),([4,v3,v1,v10,v6,v13],[(140,5)]),([4,v3,v1,v10,v4,4289396480],[]),([4,v3,v1,v10,v4,v11],[]),([4,v3,v1,v10,v4,v13],[(140,5)]),([4,v3,v1,v10,4293980400,v11],[]),([4,v3,v1,v10,va,v17],[]),([4,v3,v1,v10,va,v13],[(140,5)]),([4,v3,v1,v10,v13],[(108,5),(109,5),(110,5)]),([4,v3,v1,4026572800,4293982960,v0],[]),([4,v3,v1,4026572800,va,v0],[]),([4,v3,v1,v6,v1c,v13],[(140,5)]),([4,v3,v1,v6,v4,4294905600],[]),([4,v3,v1,v6,v4,4294936576],[]),([4,v3,v1,v6,4042326000,v0],[]),([4,v3,v1,v6,4176541936,v0],[]),([4,v3,v1,v6,4204853920,v0],[]),([4,v3,v1,v6,4205445120,va],[]),([4,v3,v1,v6,4210096880,v0],[]),([4,v3,v1,v6,4210688000,va],[]),([4,v3,v1,v6,4210752240,v0],[(108,5)]),([4,v3,v1,v6,4277206768,v0],[]),([4,v3,v1,v6,4293918720,v13],[(140,5)]),([4,v3,v1,v6,4293962400,v0],[]),([4,v3,v1,v6,4293982960,v0],[]),([4,v3,v1,v6,va,4294574080],[]),([4,v3,v1,v6,va,v0],[]),([4,v3,v1,v6,4294180851,v0],[]),([4,v3,v1,v6,4294639600,v0],[(108,5)]),([4,v3,v1,v6,v0,4294945440],[(116,3),(140,9)])]

def K_7 : List (List Nat × List (Nat × Nat)) := [([4,v3,v1,v6,v0,4294966000],[(116,0),(140,6)]),([4,v3,v1,v6,v0,v13],[(140,5)]),([4,v3,v1,4026593440,v2,v0],[]),([4,v3,v1,4026593520,v2,v0],[]),([4,v3,v1,4026593520,4278255600,v0],[]),([4,v3,v1,4026593520,va,v0],[]),([4,v3,v1,4026593520,v0,v11],[]),([4,v3,v1,4026597375,va,v0],[]),([4,v3,v1,4027576335,va,v0],[(148,3)]),([4,v3,v1,4029739248,v2,v0],[]),([4,v3,v1,4034953344,v2,v0],[]),([4,v3,v1,v1d,v2,4287102976],[]),([4,v3,v1,v1d,v2,v0],[]),([4,v3,v1,v1d,4286644096,v0],[]),([4,v3,v1,v1d,va,v0],[]),([4,v3,v1,v1d,v0,v11],[]),([4,v3,v1,4037058720,4278233600,v0],[]),([4,v3,v1,4037058720,v2,v0],[]),([4,v3,v1,4037066880,v2,v0],[]),([4,v3,v1,4037075104,4278242304,v0],[]),([4,v3,v1,4037075104,v2,v0],[]),([4,v3,v1,4037079168,v2,v0],[]),([4,v3,v1,ve,v19,v0],[]),([4,v3,v1,ve,4210688000,v2],[]),([4,v3,v1,ve,4227922944,v0],[]),([4,v3,v1,ve,4244373504,v2],[]),([4,v3,v1,ve,v2,4289331200],[]),([4,v3,v1,ve,v2,4291559424],[]),([4,v3,v1,ve,v2,4293787648],[]),([4,v3,v1,ve,v2,4294574080],[]),([4,v3,v1,ve,v2,v0],[]),([4,v3,v1,ve,v2,4294901845],[]),([4,v3,v1,ve,4283826005,v0],[]),([4,v3,v1,ve,4286644096,v0],[]),([4,v3,v1,ve,4290838464,v0],[]),([4,v3,v1,ve,4291624704,v0],[])]

def K_8 : List (List Nat × List (Nat × Nat)) := [([4,v3,v1,4037079280,v2,v0],[]),([4,v3,v1,4038127792,v2,v0],[]),([4,v3,v1,4041269472,v2,v0],[]),([4,v3,v1,4041273504,v2,v0],[]),([4,v3,v1,4041273568,v2,4293787648],[]),([4,v3,v1,4041273568,v2,v0],[]),([4,v3,v1,4042322048,v2,v0],[]),([4,v3,v1,4042322080,v2,v0],[]),([4,v3,v1,4042322144,v2,v0],[]),([4,v3,v1,v4,v2,v0],[]),([4,v3,v1,v4,v2,4294901763],[]),([4,v3,v1,v4,v2,4294901777],[]),([4,v3,v1,v4,v2,4294901794],[]),([4,v3,v1,v4,v2,4294901808],[]),([4,v3,v1,v4,v2,4294901811],[]),([4,v3,v1,v4,v2,4294901879],[]),([4,v3,v1,v4,v2,4294901920],[]),([4,v3,v1,v4,v2,4294902000],[]),([4,v3,v1,v4,v2,4294902579],[]),([4,v3,v1,v4,v2,4294905872],[]),([4,v3,v1,v4,v2,4294906129],[]),([4,v3,v1,v4,v2,4294906163],[]),([4,v3,v1,v4,v2,4294934528],[]),([4,v3,v1,v4,v2,4294934656],[]),([4,v3,v1,v4,v2,4294936704],[]),([4,v3,v1,v4,4278451971,4294902531],[]),([4,v3,v1,v4,4279238400,4294905615],[(156,2)]),([4,v3,v1,v4,4279369489,4294906129],[]),([4,v3,v1,v4,4286644096,4294934656],[]),([4,v3,v1,v4,4287137928,v11],[(132,2),(140,8)]),([4,v3,v1,v4,4287168256,4294936712],[(148,0)]),([4,v3,3435973839,v4,v2,v0],[]),([4,v3,3435973853,v4,v2,v0],[]),([4,v3,3435977948,v4,v2,v0],[]),([4,v3,3435978205,4042301600,v2,v0],[]),([4,v3,3435978205,v4,v2,v0],[])]

def K_9 : List (List Nat × List (Nat × Nat)) := [([4,v3,3435978205,v4,4278255445,v0],[]),([4,v3,3437092317,v4,v2,v0],[]),([4,v3,3722304989,v8,v2,v0],[]),([4,v3,3972844748,v4,v2,v0],[]),([5,0,v3,v1,v4,v2,v0],[]),([5,15,v3,v1,v4,v2,v0],[(56,5)]),([5,51,v3,v1,v4,v2,v0],[(56,5),(96,2),(128,0)]),([5,170,v3,v1,v4,v2,v0],[]),([5,240,v3,v1,v4,v2,v0],[(128,0)]),([5,255,v3,v1,v4,v16],[(2,2)]),([5,255,v3,v1,v4,v16,v11],[(128,2)]),([5,255,v3,v1,v4,v2,v0],[]),([5,4095,v3,v1,v4,v2,v0],[]),([5,4369,v3,v1,v4,v2,v0],[(56,5),(96,2),(128,0)]),([5,8738,v3,v1,v4,v2,v0],[(96,2),(128,0)]),([5,12336,v3,v1,v4,v2,v0],[(56,5),(128,0)]),([5,13107,2863302792,v1,v4,v2,v0],[(56,5),(72,3),(96,4),(128,3),(168,3)]),([5,13107,v3,v1,4042309824,v2,v0],[(56,5),(96,2),(128,6),(168,6)]),([5,13107,v3,v1,v4,v2,v0],[(56,5),(96,2),(128,0)]),([5,13107,v3,v1,v4,4278255411,v0],[(56,5),(96,3),(128,0)]),([5,13107,2863315899,v1,v4,v2,v0],[(56,5),(96,7),(128,5)]),([5,13311,v3,v1,v4,v2,v0],[]),([5,30583,v3,v1,v4,v2,v0],[(96,2),(128,0)]),([5,34952,v3,v1,v4,v2,v0],[]),([5,41120,v3,v1,v4,v2,v0],[(128,0)]),([5,43690,2863267840,v1,v4,v2,v0],[]),([5,43690,v3,v1,v4,v2,v0],[]),([5,43690,2863333375,v1,v4,v2,v0],[]),([5,61166,v3,v1,v4,v2],[]),([5,61166,v3,v1,v4,v2,v0],[]),([5,61440,v3,v1,v4,v2,v0],[]),([5,61680,v3,v1,v6,v2,v0],[(128,1)]),([5,61680,v3,v1,v1c,v2,v0],[(128,3),(168,0)]),([5,61680,v3,v1,v4,v2,v0],[(128,0)]),([5,61680,v3,v1,v4,4278255600,v0],[(96,0),(128,0)]),([5,61680,v3,v1,4042326015,v2,v0],[(128,4)])]

def K_10 : List (List Nat × List (Nat × Nat)) := [([5,64250,v3,v1,v4,v2],[(2,7)]),([5,64250,v3,v1,v4,v2,v0],[]),([5,65520,v3,v1,v4,v2,v0],[(96,2),(128,0)]),([5,v9,16711935,252645135,v3,v1],[]),([5,v9,16711935,vb,v3,v4],[]),([5,v9,16711935,v3,v1,v4],[]),([5,v9,vb,1431655765,v4,v2],[]),([5,v9,vb,v3,v4,v2],[]),([5,v9,v5,vc,v4,v2],[(148,1)]),([5,v9,v5,vc,v4,v2,v0],[(148,1)]),([5,v9,vd,v1,v4,v2],[]),([5,v9,vd,v1,v4,v2,v0],[]),([5,v9,2863267840,v1,v4,v2,4294945450],[]),([5,v9,2863302792,v1,v4,v2],[(2,3)]),([5,v9,2863302792,v1,v4,v2,v0],[(72,3),(188,5)]),([5,v9,v3,v1,v8,v2],[]),([5,v9,v3,v1,v8,v2,v0],[]),([5,v9,v3,v1,4008574976,v4,v2],[]),([5,v9,v3,v1,v6,va],[]),([5,v9,v3,v1,v6,va,v0],[]),([5,v9,v3,v1,4026593520,v2],[]),([5,v9,v3,v1,4026593520,v2,v0],[(132,1)]),([5,v9,v3,v1,ve,v2],[]),([5,v9,v3,v1,ve,v2,v0],[]),([5,v9,v3,v1,v1c,v2,v17],[]),([5,v9,v3,v1,4042301600,v2],[(2,0)]),([5,v9,v3,v1,4042301600,v2,v0],[]),([5,v9,v3,v1,v4,4210688000,v2],[]),([5,v9,v3,v1,v4,v2],[]),([5,v9,v3,v1,v4,v2,v0],[]),([5,v9,v3,v1,v4,4278255600],[(2,0)]),([5,v9,v3,v1,v4,4278255600,v0],[(96,4)]),([5,1048575,v3,v1,v4,v2,v0],[]),([5,3355443,v3,v1,v4,v2,v0],[(56,5),(96,2)]),([5,3407871,v3,v1,v4,v2],[(2,10)]),([5,3407871,v3,v1,v4,v2,4291559424],[])]

def K_11 : List (List Nat × List (Nat × Nat)) := [([5,3407871,v3,v1,v4,v2,v0],[]),([5,11184810,v3,v1,v4,v2,v0],[]),([5,15790320,v3,v1,v4,v2,v0],[]),([5,16777215,v3,v1,v4,v16,v11],[]),([5,16777215,v3,v1,v4,v2,v0],[]),([5,16777215,v3,v1,v4,v11],[(2,2)]),([5,268435455,v3,v1,v4,v2,v0],[]),([5,269488144,v3,v1,v4,v2,v0],[(128,0)]),([5,286331153,v5,vc,v4,v2,v0],[(96,2),(128,0),(148,1),(188,3)]),([5,286331153,v5,v4,v2,v0],[]),([5,286331153,v3,v1,v8,v2,v0],[(56,5),(96,2),(128,0)]),([5,286331153,v3,v1,v4,v2,v0],[(96,2),(128,0)]),([5,286331153,v3,v1,v4,v2,4294906129],[(96,1)]),([5,286339891,v3,v1,v4,v2,v0],[(96,2),(128,0)]),([5,286392319,v3,v1,4008574976,v4,v2],[]),([5,286392319,v3,v1,v4,v2],[(2,3)]),([5,286392319,v3,v1,v4,v2,v0],[]),([5,538976288,v3,v1,v4,v2,v0],[]),([5,572662306,v5,v1,v4,v2,v0],[]),([5,572662306,v3,v1,v4,v2,v0],[]),([5,572662306,3149642683,v1,v4,v2,v0],[]),([5,572697258,v3,v1,v4,v2,v0],[]),([5,805318656,v3,v1,v4,v2,v0],[]),([5,808464432,v3,v1a,v1,v2,v0],[]),([5,808464432,v3,v1,v4,v2,v0],[]),([5,808464432,v3,v1,4092851187,v2,v0],[]),([5,808513776,v3,v1,v4,v2,v0],[]),([5,842150450,v3,v1,v4,v2,v0],[]),([5,842150450,v3,v4,v2,v0],[(2,2)]),([5,858796848,v3,v1,v4,v2,v0],[]),([5,vb,1431655765,v4,v2,v0],[]),([5,vb,v5,vc,v4,v2,v0],[(148,1),(188,3)]),([5,vb,vd,v1,v4,v2,v0],[]),([5,vb,vd,v4,v2,v0],[]),([5,vb,v3,3368601800,v4,v2,v0],[]),([5,vb,v3,v1,v8,v2,v0],[(56,5)])]

def K_12 : List (List Nat × List (Nat × Nat)) := [([5,vb,v3,v1,v6,va,v0],[]),([5,vb,v3,v1,ve,v2,v0],[]),([5,vb,v3,v1,4039176384,v2,v0],[(128,5)]),([5,vb,v3,v1,v4,v2,v0],[]),([5,vb,v3,v8,v2,v0],[]),([5,vb,v3,v6,va,v0],[]),([5,vb,v3,ve,v2,v0],[]),([5,vb,v3,4039176384,v2,v0],[(2,5)]),([5,vb,v3,v4,v2,v0],[]),([5,858993663,v3,v1,v4,v2,v0],[]),([5,859010935,v3,3435956360,v4,v2,v0],[]),([5,859010935,v3,v1,v4,v2,v0],[]),([5,859010935,v3,v4,v2,v0],[(2,9)]),([5,859045887,v3,v1,v4,v2,v0],[]),([5,872415231,v3,v1,v4,v2,v0],[]),([5,1886417008,v3,v1,v4,v2,v0],[]),([5,2004318071,v5,vc,v4,v2,v0],[(148,1),(188,3)]),([5,2004318071,v3,v1,v4,v2,v0],[]),([5,2004318071,vc,v4,v2,v0],[(108,1),(140,3)]),([5,2004353023,v3,v1,v4,v2,v0],[(132,1)]),([5,2147516416,v3,v1,v4,v2,v0],[]),([5,2155905152,v5,vc,v4,v2,v0],[(128,0),(188,0)]),([5,2155905152,v3,v1,v6,v2,v0],[(128,1),(168,1)]),([5,2155905152,v3,v1,v4,v2,v0],[(128,0)]),([5,2155905152,v3,v1,v4,v2,4294934656],[]),([5,2155905152,v3,v1,4177066232,v2,v0],[(128,4),(168,2),(196,0)]),([5,2290124928,v3,v1,v4,v2,v0],[(96,2),(128,0)]),([5,v5,v5,vc,v4,v2,v0],[(148,1),(188,3)]),([5,v5,2684395520,v1,v4,v2,v0],[(80,5),(148,1)]),([5,v5,v7,v3,v1a,v2,v0],[]),([5,v5,v7,v1a,v4,v2,v0],[]),([5,v5,v7,v1a,v2,v0],[(58,5),(81,5),(117,5),(141,0),(149,6)]),([5,v5,v7,3422604288,v4,v2,v0],[(80,1),(116,5),(140,1)]),([5,v5,v7,v1,v6,v2,v0],[(116,5)]),([5,v5,v7,v1,v4,v2,v0],[(80,5)]),([5,v5,v7,v1,4177066232,v2,v0],[(196,0)])]

def K_13 : List (List Nat × List (Nat × Nat)) := [([5,v5,v7,v1,vf,v2,v0],[(196,0)]),([5,v5,v7,3974950124,v4,v2,v0],[(80,5),(104,5),(188,0)]),([5,v5,v7,vc,v4,v2,v0],[(188,0)]),([5,v5,vd,v1,v4,v2,v0],[(80,5),(116,5)]),([5,v5,v15,v1,v4,v2,v0],[(80,5)]),([5,v5,v3,v1,v8,v2,v0],[(60,5)]),([5,v5,v3,v1,v6,va,v0],[(96,3),(148,5)]),([5,v5,v3,v1,v1d,v2,v0],[(132,1),(140,1),(148,7)]),([5,v5,v3,v1,ve,v2,v0],[(140,1)]),([5,v5,v3,v1,v4,v2,v0],[]),([5,v5,v3,v1,v4,v2,4294934656],[(96,2)]),([5,v5,v3,3435986943,v4,v2,v0],[]),([5,v5,v3,v8,vc,v2,v0],[(196,0)]),([5,v5,v3,v8,v4,v2,v0],[]),([5,v5,v3,v8,v2,v0],[(6,5),(109,1),(137,0),(141,3)]),([5,v5,v3,3941264106,v4,v2,v0],[(148,1),(188,3)]),([5,v5,v3,3974950124,v4,v2,v0],[(60,5),(148,1),(188,3)]),([5,v5,v3,vc,v4,v2,v0],[(148,1),(188,3)]),([5,v5,v8,vc,v4,v2,v0],[(188,0)]),([5,v5,v8,vc,v2,v0],[(117,1),(145,0),(148,0),(149,3),(150,0)]),([5,v5,v8,v4,v2,v0],[(10,2),(141,0),(145,0),(149,0)]),([5,v5,v8,v2,v0],[(6,2),(7,2),(10,0),(11,0),(13,0),(79,1),(99,0),(103,3),(107,0),(111,0)]),([5,v5,3941264106,v4,v2,v0],[(108,1),(109,1),(110,1),(140,3),(141,3),(142,3)]),([5,v5,vc,vc,v4,v2,v0],[(140,1),(180,3)]),([5,v5,vc,v6,v4,v2,v0],[(140,1),(180,3)]),([5,v5,vc,v4,v4,v2,v0],[(140,1),(180,3)]),([5,v5,vc,v4,4177066232,v2,v0],[(140,1),(156,1),(180,3),(196,3)]),([5,v5,vc,v4,vf,v2,v0],[(140,1),(156,1),(180,3),(196,3)]),([5,v5,vc,v4,4278124286,v2,v0],[(140,1),(156,1),(180,3),(196,3)]),([5,v5,vc,v4,v2,va,v0],[(108,1),(180,3)]),([5,v5,vc,v4,v2,v0],[(108,1),(109,1),(110,1),(140,3),(141,3),(142,3)]),([5,2290657962,v3,v1,v4,v2,v0],[]),([5,2290679807,v3,v1,v4,v2,v0],[]),([5,2684354560,v3,v1,v4,v2,v0],[]),([5,2684395520,v3,v1a,v1,v2,v0],[(72,5)]),([5,2684395520,v3,v1,v6,va,v0],[])]

def K_14 : List (List Nat × List (Nat × Nat)) := [([5,2684395520,v3,v1,v4,v2,v0],[]),([5,2684395520,v3,v1,v4,4288741280,v0],[]),([5,2692784256,2861083272,v1,v4,v2,v0],[(56,1),(96,1),(128,1)]),([5,2692784256,v3,v1,4039176384,v2,v0],[(56,5),(96,5),(128,5)]),([5,2692784256,v3,v1,v4,v2,v0],[(128,0)]),([5,2694881280,v3,v1,v4,v2,v0],[]),([5,v7,vd,v1,v4,v2,v0],[]),([5,v7,2852170240,v3,v1,v6,v0],[(128,1)]),([5,v7,2861083272,v1,v4,v2,v0],[(96,1),(128,1)]),([5,v7,2863311360,v1,v4,v2,v0],[(196,0)]),([5,v7,v3,v1a,v1,v2,v0],[]),([5,v7,v3,3368601800,v1,v2,v0],[]),([5,v7,v3,3368601800,v4,v2,v0],[(56,5),(96,5)]),([5,v7,v3,3368601800,vf,v2,v0],[(196,0)]),([5,v7,v3,3368601800,v2,v0],[]),([5,v7,v3,3422604288,v1,v6,v0],[(72,1)]),([5,v7,v3,3431517320,v4,v2,v0],[(56,7),(96,7)]),([5,v7,v3,v1,v8,v2,v0],[]),([5,v7,v3,v1,3941264106,v2,v0],[(196,0)]),([5,v7,v3,v1,3959483392,v4,v0],[(56,7),(128,7)]),([5,v7,v3,v1,v14,v4,v0],[(56,1),(128,1)]),([5,v7,v3,v1,v10,v2,v0],[(128,4),(168,2)]),([5,v7,v3,v1,v6,v2,v0],[(128,1)]),([5,v7,v3,v1,v6,4288741280,v0],[(56,1),(128,1)]),([5,v7,v3,v1,v6,va,v0],[]),([5,v7,v3,v1,v6,v0,v11],[(168,1)]),([5,v7,v3,v1,ve,v2,v0],[]),([5,v7,v3,v1,4039176384,v2,v0],[(56,5),(128,5)]),([5,v7,v3,v1,4042321920,v2,v0],[]),([5,v7,v3,v1,v4,v19,v0],[(56,1),(96,1)]),([5,v7,v3,v1,v4,4227922944,v0],[(56,7),(96,7)]),([5,v7,v3,v1,v4,v16,v11],[(56,2),(96,2),(168,2)]),([5,v7,v3,v1,v4,4278233600,v0],[(56,2),(96,2)]),([5,v7,v3,v1,v4,4278242304,v0],[(56,8),(96,8),(168,8)]),([5,v7,v3,v1,v4,v2,v0],[]),([5,v7,v3,v1,v4,v2,4294934656],[])]

def K_15 : List (List Nat × List (Nat × Nat)) := [([5,v7,v3,v1,4042326015,v2,v0],[]),([5,v7,v3,v1,4092851187,v2,v0],[]),([5,v7,v3,v1,4177066232,v2,v0],[(196,0)]),([5,v7,v3,v1,v19,vf,v0],[]),([5,v7,v3,v1,v19,v2,v0],[]),([5,v7,v3,v1,v19,v0],[]),([5,v7,v3,v1,4205509290,v2,v0],[(196,0)]),([5,v7,v3,v1,4210096880,v2,v0],[]),([5,v7,v3,v1,vf,v2,v0],[(196,0)]),([5,v7,3149642683,v1,v4,v2,v0],[]),([5,v7,3368601800,v4,v2,v0],[(10,2)]),([5,2694884010,v3,v1,v4,v2,v0],[]),([5,2694902000,v3,v1,v4,v2,v0],[]),([5,2694905855,v3,v1,v4,v2,v0],[]),([5,2728567458,v3,v1,v4,v2,v0],[]),([5,2827528328,v3,v1,v4,v2,v0],[]),([5,2827528328,v1,v6,v4,v2,v0],[]),([5,2827528328,v1,v4,4241292492,v2,v0],[(156,1)]),([5,2827528328,v1,v4,v2,v0],[(86,5),(110,7)]),([5,2829101216,v3,v1,v4,v2,v0],[(96,2)]),([5,vd,vd,v1,v4,v2,v0],[]),([5,vd,v3,v1,v4,4227922944,v0],[(56,7)]),([5,vd,v3,v1,v4,v2,v0],[]),([5,vd,v1,v1,v4,v2,v0],[(108,5)]),([5,vd,v1,3974950124,v4,v2,v0],[(60,5),(188,0)]),([5,vd,v1,vc,v4,v2,v0],[(188,0)]),([5,vd,v1,v6,v4,v2,v0],[]),([5,vd,v1,v4,v4,v2,v0],[]),([5,vd,v1,v4,4177066232,v2,v0],[(196,0)]),([5,vd,v1,v4,vf,v2,v0],[(196,0)]),([5,vd,v1,v4,4227922944,4244438268,v0],[]),([5,vd,v1,v4,4227922944,v2,v0],[]),([5,vd,v1,v4,4227922944,v0],[(86,5)]),([5,vd,v1,v4,4244438268,v2,v0],[(196,0)]),([5,vd,v1,v4,4278124286,v2,v0],[(196,0)]),([5,vd,v1,v4,v16,v2,v0],[])]

def K_16 : List (List Nat × List (Nat × Nat)) := [([5,vd,v1,v4,v2,v2,v0],[]),([5,vd,v1,v4,v2,4289265576,v0],[(204,0)]),([5,vd,v1,v4,v2,v1b,v0],[(204,0)]),([5,vd,v1,v4,v2,4291624908,v0],[(204,0)]),([5,vd,v1,v4,v2,va,v0],[]),([5,vd,v1,v4,v2,4294770684,v0],[(204,0)]),([5,vd,v1,v4,v2,v0],[(86,5)]),([5,vd,v1,v4,v2,v0,v11],[]),([5,2862653600,v3,v1,v4,v2,v0],[]),([5,v15,v3,v1,v6,v4,v0],[]),([5,v15,v3,v1,v6,va,v0],[]),([5,v15,v3,v1,v6,v0],[(141,3)]),([5,v15,v3,v1,v1c,v2,v0],[(168,3),(180,3)]),([5,v15,v3,v1,v4,v2,v0],[]),([5,2863180456,v3,v1,v4,v2,v0],[]),([5,2863180456,v1,v4,4244438268,v2,v0],[(156,1)]),([5,2863180456,v1,v4,v2,va,v0],[]),([5,2863180456,v1,v4,v2,4294770684,v0],[]),([5,2863180456,v1,v4,v2,v0],[]),([5,v12,v3,v1,v4,v2,v0],[(196,0),(204,2)]),([5,v12,v1,v4,v2,va,v0],[(188,0),(196,2),(204,3)]),([5,v12,v1,v4,v2,v0],[(117,1),(148,0),(149,3),(150,0),(156,2),(157,4),(158,2)]),([5,v12,v1,v4,v2,v0,v13],[(148,0),(156,2)]),([5,v3,v3,v1,v8,v2,v0],[]),([5,v3,v3,v1,v6,va,v0],[]),([5,v3,v3,v1,ve,v2,v0],[(132,1)]),([5,v3,v3,v1,4039176384,v2,v0],[(48,5),(52,5)]),([5,v3,v3,v1,v4,v2,v0],[]),([5,v3,2863311615,v1,v4,v2,v0],[]),([5,v3,2863315899,v1,v4,v2,v0],[(56,5)]),([5,v3,2863329006,v1,v4,v2,v0],[]),([5,v3,2863332090,v1,v4,v2,v0],[]),([5,v3,2863333375,v1,v4,v2,v0],[]),([5,v3,2868903935,v1,v4,v2,v0],[]),([5,v3,2964369584,v1,v4,v2,v0],[]),([5,v3,3014898611,v1,v4,v2,v0],[])]

def K_17 : List (List Nat × List (Nat × Nat)) := [([5,v3,3132799674,v1,v4,v2,v0],[]),([5,v3,3149642683,v1,v4,v2,v0],[]),([5,v3,3149660159,v1,v4,v2,v0],[]),([5,v3,v1,3758153728,v8,v2,v0],[(152,1)]),([5,v3,v1,3758153728,v4,v2,v0],[]),([5,v3,v1,v18,4004179626,v2,v0],[(108,7)]),([5,v3,v1,v18,v4,v2,v0],[]),([5,v3,v1,v18,v2,v0],[(61,5),(102,1)]),([5,v3,v1,v8,v8,v2,v0],[]),([5,v3,v1,v8,3941264106,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v8,v14,vc,v0],[]),([5,v3,v1,v8,v14,v4,v0],[(144,1)]),([5,v3,v1,v8,v14,v0],[(61,5)]),([5,v3,v1,v8,vc,v2,v0],[(196,0)]),([5,v3,v1,v8,v6,v2,v0],[(144,1)]),([5,v3,v1,v8,v4,v2,v0],[]),([5,v3,v1,v8,vf,v2,v0],[(108,5),(196,0)]),([5,v3,v1,v8,4278124286,v2,v0],[(196,0)]),([5,v3,v1,v8,v16,v2,v0],[]),([5,v3,v1,v8,v2,v2,v0],[]),([5,v3,v1,v8,v2,v1b,v0],[(140,7),(204,0)]),([5,v3,v1,v8,v2,4292935648,v0],[(116,1)]),([5,v3,v1,v8,v2,4293853166,v0],[(204,0)]),([5,v3,v1,v8,v2,va,v0],[]),([5,v3,v1,v8,v2,v0],[(61,5)]),([5,v3,v1,v8,v2,v0,v11],[]),([5,v3,v1,3937069738,v4,v2,v0],[(84,5),(148,1),(188,3)]),([5,v3,v1,3938511552,v4,v2,v0],[(116,5),(148,1)]),([5,v3,v1,3941264106,v4,v2,v0],[(84,5),(148,1),(188,3)]),([5,v3,v1,4007718624,v4,v2,v0],[(148,1)]),([5,v3,v1,4008373994,v4,v2,v0],[(84,5),(148,1),(188,3)]),([5,v3,v1,vc,v6,va,v0],[(188,3)]),([5,v3,v1,vc,ve,v2,v0],[(148,1),(188,3)]),([5,v3,v1,vc,4041273568,v2,v0],[(148,1),(188,3)]),([5,v3,v1,vc,v4,v2,v0],[(148,1),(188,3)]),([5,v3,v1,vc,v4,v2,4294906129],[(148,1),(188,3)])]

def K_18 : List (List Nat × List (Nat × Nat)) := [([5,v3,v1,4008640511,v4,v2,v0],[(148,1),(188,3)]),([5,v3,v1,v10,v6,v4,v11],[]),([5,v3,v1,v10,v6,va,v0],[(116,3),(152,3),(192,3)]),([5,v3,v1,v10,v4,v2,v0],[(152,3),(192,1)]),([5,v3,v1,v10,v4,v2,4294963200],[(152,3),(192,1)]),([5,v3,v1,v10,v4,v2,v17],[(116,1),(192,1)]),([5,v3,v1,v10,v4,v11],[(110,5),(134,2),(142,8),(153,2)]),([5,v3,v1,4026572800,4042301600,v2,v0],[(112,0),(144,0),(152,1)]),([5,v3,v1,4026572800,v4,v2,v0],[]),([5,v3,v1,v6,v6,va,v0],[]),([5,v3,v1,v6,ve,v2,v0],[(152,1)]),([5,v3,v1,v6,v1c,v4,v11],[]),([5,v3,v1,v6,v1c,v2,v17],[(116,1),(144,0),(184,0)]),([5,v3,v1,v6,4042301600,v2,v0],[(144,0),(152,1)]),([5,v3,v1,v6,v4,4205445120,v2],[(112,3),(184,3)]),([5,v3,v1,v6,v4,4210096880,v0],[]),([5,v3,v1,v6,v4,4210688000,v2],[(112,3),(184,3)]),([5,v3,v1,v6,v4,v2,v0],[]),([5,v3,v1,v6,v4,4281597747,v0],[]),([5,v3,v1,v6,v4,4288741280,v0],[(116,1)]),([5,v3,v1,v6,v4,4289396480,v0],[]),([5,v3,v1,v6,v4,4293984000,v0],[]),([5,v3,v1,v6,v4,va,v0],[]),([5,v3,v1,v6,v4,v0,4294945280],[(148,0)]),([5,v3,v1,v6,v4,v0,v11],[]),([5,v3,v1,v6,v4,v0,v13],[(180,5)]),([5,v3,v1,v6,4205509290,va,v0],[(108,5)]),([5,v3,v1,v6,4210096880,v0],[(110,5),(149,3)]),([5,v3,v1,v6,vf,va,v0],[(108,5)]),([5,v3,v1,v6,4293918720,va,v0],[(116,3)]),([5,v3,v1,v6,va,va,v0],[]),([5,v3,v1,v6,va,4294639610,v0],[(140,5)]),([5,v3,v1,v6,va,v0],[(110,5),(149,3)]),([5,v3,v1,v6,va,v0,v0],[(148,3)]),([5,v3,v1,v6,va,v0,4294945450],[(180,9)]),([5,v3,v1,v6,va,v0,4294963200],[(148,3)])]

def K_19 : List (List Nat × List (Nat × Nat)) := [([5,v3,v1,v6,va,v0,v17],[]),([5,v3,v1,v6,va,v0,v13],[(180,5)]),([5,v3,v1,v6,v0,v17,v11],[(116,3)]),([5,v3,v1,v6,v0,v17,v13],[(116,0),(180,5)]),([5,v3,v1,v6,v0,v13],[(117,3),(140,5),(141,5),(142,5)]),([5,v3,v1,4026593520,v4,v2,v0],[(144,0)]),([5,v3,v1,4026593520,v2,4278255615,v0],[]),([5,v3,v1,4026593520,v2,v0],[(102,1),(110,7)]),([5,v3,v1,4026597375,v4,v2,v0],[(148,1)]),([5,v3,v1,4029739056,v4,v2,v0],[]),([5,v3,v1,v1d,v4,v2,v0],[(144,0)]),([5,v3,v1,v1d,v2,4287168392,v0],[(132,1),(140,7)]),([5,v3,v1,v1d,v2,v0],[(102,1),(110,7)]),([5,v3,v1,4037058720,v4,v2,v0],[]),([5,v3,v1,4037058720,v2,4289374890,v0],[(140,8),(204,0)]),([5,v3,v1,4037058720,v2,v0],[(102,1),(134,3)]),([5,v3,v1,4037079040,v4,v2,v0],[]),([5,v3,v1,ve,ve,v2,v0],[]),([5,v3,v1,ve,v4,v2,4289331200],[(112,4)]),([5,v3,v1,ve,v4,v2,v0],[]),([5,v3,v1,ve,4205509290,v2,v0],[(108,5),(196,3)]),([5,v3,v1,ve,vf,v2,v0],[(108,5)]),([5,v3,v1,ve,4243389676,v2,v0],[(196,9)]),([5,v3,v1,ve,4244438268,v2,v0],[]),([5,v3,v1,ve,v2,v2,v0],[]),([5,v3,v1,ve,v2,4288741280,v0],[(116,1)]),([5,v3,v1,ve,v2,4289331200],[(102,1)]),([5,v3,v1,ve,v2,4289331200,v1b],[(180,7)]),([5,v3,v1,ve,v2,v1b,v0],[(140,7)]),([5,v3,v1,ve,v2,4291624908,v0],[(132,1)]),([5,v3,v1,ve,v2,4293853166,v0],[]),([5,v3,v1,ve,v2,va,v0],[]),([5,v3,v1,ve,v2,4294639610,v0],[(140,5)]),([5,v3,v1,ve,v2,v0],[(102,1)]),([5,v3,v1,ve,v2,v0,v0],[]),([5,v3,v1,ve,v2,v0,4294945450],[(180,9),(196,2)])]

def K_20 : List (List Nat × List (Nat × Nat)) := [([5,v3,v1,ve,v2,v0,4294954188],[(172,3),(196,8)]),([5,v3,v1,ve,v2,v0,4294963360],[(148,3)]),([5,v3,v1,ve,v2,v0,v17],[(148,0)]),([5,v3,v1,ve,v2,v0,v11],[(156,2)]),([5,v3,v1,ve,v2,v0,4294967210],[(180,8)]),([5,v3,v1,4041273568,v4,v2,v0],[]),([5,v3,v1,4041273568,v2,v1b,v0],[(140,7),(204,4)]),([5,v3,v1,4041273568,v2,4293853166,v0],[]),([5,v3,v1,4041273568,v2,v0],[]),([5,v3,v1,4042321920,v4,v2,v0],[]),([5,v3,v1,4042321920,v2,va,v0],[]),([5,v3,v1,4042321920,v2,v0,v13],[(148,0),(156,2),(180,5)]),([5,v3,v1,4042322080,v4,v2,v0],[]),([5,v3,v1,4042322080,v2,v1b,v0],[(140,7),(204,4)]),([5,v3,v1,4042322080,v2,v0],[]),([5,v3,v1,4042322080,v2,v0,v11],[(156,2)]),([5,v3,v1,4042322080,v2,v0,4294967210],[(180,8)]),([5,v3,v1,v4,v4,v2,v0],[]),([5,v3,v1,v4,4042322175,v2,v0],[]),([5,v3,v1,v4,4042322931,v2,v0],[(112,2)]),([5,v3,v1,v4,4042324730,v2,v0],[(156,1)]),([5,v3,v1,v4,4042326000,v2,v0],[(112,2),(156,1)]),([5,v3,v1,v4,4042326015,v2,v0],[(156,1)]),([5,v3,v1,v4,4043309055,v2,v0],[(156,1),(196,3)]),([5,v3,v1,v4,4059165169,v2,v0],[(112,2)]),([5,v3,v1,v4,4076008178,v2,v0],[]),([5,v3,v1,v4,4080268083,v2,v0],[]),([5,v3,v1,v4,4092654576,v2,v0],[]),([5,v3,v1,v4,4092851187,v2,v0],[]),([5,v3,v1,v4,4092854271,v2,v0],[(156,1)]),([5,v3,v1,v4,4160223223,v2,v0],[]),([5,v3,v1,v4,4169726088,v2,v0],[(108,5),(144,3),(156,1),(196,3)]),([5,v3,v1,v4,4176541936,v2,v0],[(112,2),(156,1)]),([5,v3,v1,v4,4177066232,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4205488810,v2,v0],[(108,5),(132,1),(156,1),(172,3),(196,3)]),([5,v3,v1,v4,4205506560,v2,v0],[(196,3)])]

def K_21 : List (List Nat × List (Nat × Nat)) := [([5,v3,v1,v4,4205509290,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4207475400,v2,v0],[(100,1),(108,5),(116,5),(156,1),(196,3)]),([5,v3,v1,v4,4209703658,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4210094320,v2,v0],[]),([5,v3,v1,v4,4210096880,v2,v0],[(156,1)]),([5,v3,v1,v4,4210621176,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4210752000,v2,v0],[(156,1),(196,3),(204,2)]),([5,v3,v1,v4,4210752170,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4210752240,v2,v0],[(108,5),(156,1),(188,0),(196,3),(204,2)]),([5,v3,v1,v4,vf,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,vf,v2,4294903045],[(100,7),(108,5),(116,7),(156,1),(196,3)]),([5,v3,v1,v4,4210753535,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4227595259,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4277075694,v2,v0],[(156,1),(196,3)]),([5,v3,v1,v4,4277206768,v2,v0],[(156,1)]),([5,v3,v1,v4,4277862138,v2,v0],[(108,5),(156,1),(196,3)]),([5,v3,v1,v4,4278124286,v2,v0],[(156,1),(196,3)]),([5,v3,v1,v4,v2,4293980400,v0],[]),([5,v3,v1,v4,v2,4293982960,v0],[(156,1)]),([5,v3,v1,v4,v2,va,v0],[]),([5,v3,v1,v4,v2,4293984255,v0],[]),([5,v3,v1,v4,v2,4294180851,v0],[]),([5,v3,v1,v4,v2,4294508536,v0],[(140,5),(204,3)]),([5,v3,v1,v4,v2,4294638330,v0],[(140,5),(156,1),(204,3)]),([5,v3,v1,v4,v2,4294639600,v0],[(140,5),(188,0),(196,2),(204,3)]),([5,v3,v1,v4,v2,4294639610,v0],[(140,5),(204,3)]),([5,v3,v1,v4,v2,4294901758,v0],[(204,3)]),([5,v3,v1,v4,v2,v0],[]),([5,v3,v1,v4,v2,v0,v13],[(148,0),(156,2),(180,5)]),([5,v3,v1,v4,v2,v0,4294967290],[(180,5)]),([5,v3,v1,v4,v2,v0,4294967295],[]),([5,v3,v1,v4,v2,4294901811],[]),([5,v3,v1,v4,v2,4294902000],[(117,1),(149,0)]),([5,v3,v1,v4,v2,4294902015,v17],[(148,0)]),([5,v3,v1,v4,v2,4294902015,v11],[(148,0),(156,2)]),([5,v3,v1,v4,v2,4294906129],[])]

def K_22 : List (List Nat × List (Nat × Nat)) := [([5,v3,v1,v4,v2,4294914867,4294954188],[(172,3),(188,6),(196,8)]),([5,v3,v1,v4,v2,4294934656],[(117,1),(149,0)]),([5,v3,v1,v4,v2,4294936712,v17],[(148,0),(156,2)]),([5,v3,v1,v4,v2,4294942880,4294954188],[(172,3),(188,6),(196,8)]),([5,v3,3435978205,v4,v2,v0],[]),([5,v3,3435978205,v4,v2,v0,4294945450],[(180,9),(196,1)]),([5,v3,3435986943,v4,v2,v0,4294954188],[(172,3)]),([5,v3,3722304989,vc,v4,v2,v0],[(148,1),(188,3)]),([6,0,v9,v3,v1,v4,v2],[]),([6,0,v9,v3,v1,v4,v2,v0],[]),([6,0,vb,v3,v1,v4,v2,v0],[]),([6,0,vb,v3,v4,v2,v0],[]),([6,0,v3,v1,v4,v2,v0],[(73,5),(129,1),(169,3)]),([6,255,v3,v1,v4,v2,v0],[(2,2),(73,5),(77,5),(129,1),(169,3)]),([6,255,v3,v1,v4,v2,v0,v11],[(128,0)]),([6,13107,v3,v1,v4,v2,v0],[(2,9),(56,5),(73,5),(96,2),(98,1),(128,0),(129,1),(133,1),(169,3)]),([6,13107,v3,v1,v4,v2,v0,4294954188],[(56,5),(96,10),(128,9),(252,1)]),([6,43690,v9,v3,v1,v4,v2],[]),([6,43690,v9,v3,v1,v4,v2,v0],[]),([6,43690,v3,v1,v4,v2,v0],[(2,9),(73,5),(129,1),(133,1),(169,3)]),([6,61680,v9,v3,v1,v4,v2],[]),([6,61680,v9,v3,v1,v4,v2,v0],[]),([6,61680,v3,v1,v4,v2,v0],[(2,4),(73,5),(77,5),(128,0),(129,1),(169,0)]),([6,v9,v9,v3,v1,v4,v2],[]),([6,v9,v9,v3,v1,v4,v2,v0],[]),([6,v9,16711935,v3,v1,v4],[(2,0),(10,5)]),([6,v9,16711935,v3,v1,v4,v2],[(2,0)]),([6,v9,16711935,v3,v1,v4,v2,v0],[]),([6,v9,vb,v3,v1,v4,v2],[]),([6,v9,vb,v3,v1,v4,v2,v0],[]),([6,v9,vb,v3,v4,v2],[(14,1)]),([6,v9,vb,v3,v4,v2,v0],[]),([6,v9,v5,v3,v1,v4,v2],[]),([6,v9,v5,v3,v1,v4,v2,v0],[(72,5)]),([6,v9,v7,v3,v1,v4,v2],[]),([6,v9,v7,v3,v1,v4,v2,v0],[])]

def K_23 : List (List Nat × List (Nat × Nat)) := [([6,v9,2863267840,v3,v1,v4,v2],[(2,3)]),([6,v9,2863267840,v3,v1,v4,v2,v0],[]),([6,v9,v3,v3,v1,v4,v2],[]),([6,v9,v3,v3,v1,v4,v2,v0],[]),([6,v9,v3,2863333375,v1,v4,v2],[]),([6,v9,v3,2863333375,v1,v4,v2,v0],[]),([6,v9,v3,v1,vc,v4,v2],[(196,1)]),([6,v9,v3,v1,vc,v4,v2,v0],[(196,1)]),([6,v9,v3,v1,v6,v4,v2],[]),([6,v9,v3,v1,v6,v4,v2,v0],[(172,1)]),([6,v9,v3,v1,v1c,v4,v2],[(2,0)]),([6,v9,v3,v1,v1c,v4,v2,v0],[]),([6,v9,v3,v1,v4,v4,v2],[]),([6,v9,v3,v1,v4,v4,v2,v0],[]),([6,v9,v3,v1,v4,4042326015,v2],[(204,1)]),([6,v9,v3,v1,v4,4042326015,v2,v0],[(204,1)]),([6,v9,v3,v1,v4,vf,v2],[(148,5),(204,1)]),([6,v9,v3,v1,v4,vf,v2,v0],[(148,5),(204,1)]),([6,v9,v3,v1,v4,v2],[(6,5),(14,1)]),([6,v9,v3,v1,v4,v2,va],[]),([6,v9,v3,v1,v4,v2,va,v0],[(96,2),(128,0)]),([6,v9,v3,v1,v4,v2,v0],[(2,3),(73,5),(77,5),(129,1),(133,1)]),([6,v9,v3,v1,v4,v2,v0,v0],[]),([6,v9,v3,v1,v4,v2,v0,4294945450],[(56,5),(236,5),(252,1)]),([6,v9,v3,v1,v4,v2,v0,v17],[(96,2)]),([6,v9,v3,v1,v4,v2,v0,4294967295],[]),([6,v9,v3,v1,v4,v2,4294945450],[(2,3),(188,5),(204,1)]),([6,v9,v3,v1,v4,v2,v17],[(2,0)]),([6,v9,v3,v1,v4,v2,4294967295],[]),([6,16777215,v3,v1,v4,v16,v2,v0],[(172,1),(220,3)]),([6,16777215,v3,v1,v4,v2,v0],[(2,2),(73,5),(77,5),(133,1),(173,3)]),([6,286331153,v3,v1,vc,v4,v2,v0],[(56,5),(128,2),(168,0),(196,1),(244,3)]),([6,286331153,v3,v1,v4,v2,v0],[(73,5),(96,2),(98,2),(128,0),(129,1),(130,0),(133,1),(169,3),(173,3)]),([6,572662306,vb,v3,v1,v4,v2,v0],[]),([6,572662306,vb,v3,v4,v2,v0],[]),([6,572662306,v3,v1,v4,v2,v0],[(2,5),(129,1),(133,1),(169,3),(173,3)])]

def K_24 : List (List Nat × List (Nat × Nat)) := [([6,808464432,vb,v3,v1,v4,v2,v0],[]),([6,808464432,vb,v3,v4,v2,v0],[]),([6,808464432,v3,v1,v4,v2,v0],[(2,8),(73,5),(129,1),(169,3),(173,0)]),([6,vb,vb,v3,v1,v4,v2,v0],[]),([6,vb,vb,v3,v4,v2,v0],[]),([6,vb,1431655765,v3,v1,v4,v2,v0],[]),([6,vb,1431655765,v3,v4,v2,v0],[(2,5)]),([6,vb,1431655765,v4,v2,v0],[(2,5),(10,2),(14,0)]),([6,vb,v5,v3,v1,v4,v2,v0],[]),([6,vb,v5,v3,v4,v2,v0],[]),([6,vb,v7,v3,v1,v4,v2,v0],[]),([6,vb,v7,v3,v4,v2,v0],[]),([6,vb,v3,v3,v1,v4,v2,v0],[]),([6,vb,v3,v3,v4,v2,v0],[]),([6,vb,v3,3149642683,v1,v4,v2,v0],[]),([6,vb,v3,3149642683,v4,v2,v0],[]),([6,vb,v3,v1a,v1,v4,v2,v0],[]),([6,vb,v3,v1a,v4,v2,v0],[(2,5)]),([6,vb,v3,v1,v1,v4,v2,v0],[]),([6,vb,v3,v1,vc,v4,v2,v0],[(56,5),(196,1),(244,3)]),([6,vb,v3,v1,v6,v4,v2,v0],[(128,1)]),([6,vb,v3,v1,v4,v4,v2,v0],[]),([6,vb,v3,v1,v4,4092851187,v2,v0],[]),([6,vb,v3,v1,v4,vf,v2,v0],[(204,1),(252,3)]),([6,vb,v3,v1,v4,4244438268,v2,v0],[(96,2),(204,1),(252,3)]),([6,vb,v3,v1,v4,v2,va,v0],[]),([6,vb,v3,v1,v4,v2,v0],[(2,5),(129,1),(133,1),(169,3),(173,3)]),([6,vb,v3,v1,v4,v2,v0,4294967295],[]),([6,vb,v3,vc,v4,v2,v0],[(148,1),(188,3)]),([6,vb,v3,v6,v4,v2,v0],[]),([6,vb,v3,v4,v4,v2,v0],[]),([6,vb,v3,v4,4092851187,v2,v0],[]),([6,vb,v3,v4,vf,v2,v0],[(156,1),(196,3)]),([6,vb,v3,v4,4244438268,v2,v0],[(2,5),(156,1),(196,3)]),([6,vb,v3,v4,v2,va,v0],[]),([6,vb,v3,v4,v2,v0],[(10,2),(14,0)])]

def K_25 : List (List Nat × List (Nat × Nat)) := [([6,vb,v3,v4,v2,v0,4294967295],[]),([6,859045887,v3,3435921408,v1,v4,v2,v0],[(100,5),(220,3)]),([6,859045887,v3,v1,v4,v2,v0],[(2,9),(77,5),(129,1),(133,1),(173,3)]),([6,2004318071,v5,v3,v1,v4,v2,v0],[(100,5)]),([6,2004318071,v3,v1,v4,v2,v0],[(77,5),(129,1),(133,1),(169,3),(173,3)]),([6,2155905152,v5,v3,v1,v4,v2,v0],[(168,0)]),([6,2155905152,v7,v3,v1,v4,v2,v0],[(168,0)]),([6,2155905152,v3,v1,v4,v2,v0],[(2,2),(73,5),(128,0),(129,1),(130,0),(169,3),(173,0),(197,0)]),([6,v5,v5,v3,v1,v4,v2,v0],[]),([6,v5,v7,v3,v1,v4,v2,v0],[]),([6,v5,v7,v1,v4,v2,v0],[(80,5),(81,5),(118,5),(181,0),(189,0),(197,0)]),([6,v5,v3,v3,v1,v4,v2,v0],[]),([6,v5,v3,v1,vc,v4,v2,v0],[(60,5),(104,5),(196,1),(244,3)]),([6,v5,v3,v1,v6,v4,v2,v0],[(116,5),(148,5),(172,1),(180,1),(188,7)]),([6,v5,v3,v1,v4,v4,v2,v0],[(116,5)]),([6,v5,v3,v1,v4,4177066232,v2,v0],[(116,5),(148,5),(204,1),(252,3)]),([6,v5,v3,v1,v4,vf,v2,v0],[(148,5),(204,1),(252,3)]),([6,v5,v3,v1,v4,v2,va,v0],[(96,2),(128,0),(188,5)]),([6,v5,v3,v1,v4,v2,v0],[(73,5),(81,5),(117,5),(129,1),(133,1),(141,1),(149,7),(169,3),(173,3),(181,3),(189,9)]),([6,v5,v3,vc,v4,v2,v0],[(6,5),(137,1),(141,1),(148,1),(149,1),(150,1),(177,3),(181,3),(188,3),(189,3),(190,3)]),([6,v5,vc,v4,v2,v0],[(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(99,1),(103,1),(107,1),(108,1),(109,1),(110,1),(111,1),(131,3),(135,3),(139,3),(140,3),(141,3),(142,3),(143,3),(147,0),(151,0),(155,2),(159,2)]),([6,2684395520,v7,v3,v1,v4,v2,v0],[]),([6,2684395520,v3,v1,v6,v4,v2,v0],[]),([6,2684395520,v3,v1,v4,v2,v0],[(2,9),(73,5),(129,1),(150,1),(169,3)]),([6,v7,v7,v3,v1,v4,v2,v0],[]),([6,v7,2852170240,v3,v1,v4,v2,v0],[(72,1),(128,1),(168,1)]),([6,v7,v3,v3,v1,v4,v2,v0],[]),([6,v7,v3,v1a,v1,v4,v2,v0],[(56,5),(128,5)]),([6,v7,v3,v1a,v1,v2,v0],[(73,5),(97,5),(109,5),(149,5),(173,0),(189,6)]),([6,v7,v3,3422604288,v1,v4,v2,v0],[(56,7),(72,1),(128,7),(148,5),(172,1)]),([6,v7,v3,v1,v1,v4,v2,v0],[(56,5),(72,5),(128,5)]),([6,v7,v3,v1,3974950124,v4,v2,v0],[(56,5),(96,5),(128,5),(244,0)]),([6,v7,v3,v1,vc,v4,v2,v0],[(244,0)]),([6,v7,v3,v1,v6,v4,v2,v0],[]),([6,v7,v3,v1,v6,v2,v0],[(118,5),(128,1),(129,1),(169,1)]),([6,v7,v3,v1,v4,v4,v2,v0],[])]

def K_26 : List (List Nat × List (Nat × Nat)) := [([6,v7,v3,v1,v4,vf,v2,v0],[(252,0)]),([6,v7,v3,v1,v4,4244438268,v2,v0],[(56,5),(96,5),(128,5),(252,0)]),([6,v7,v3,v1,v4,v16,v2,v0],[(56,2),(96,2),(128,2),(168,4),(216,2)]),([6,v7,v3,v1,v4,v2,v2,v0],[(56,1),(96,1),(128,1)]),([6,v7,v3,v1,v4,v2,4288741280,v0],[(56,1),(96,1),(168,1)]),([6,v7,v3,v1,v4,v2,v1b,v0],[(56,1),(96,1),(168,1),(260,0)]),([6,v7,v3,v1,v4,v2,4291624908,v0],[(56,7),(96,7),(128,0),(168,7),(260,0)]),([6,v7,v3,v1,v4,v2,va,v0],[]),([6,v7,v3,v1,v4,v2,v0],[(2,8),(73,5),(129,1),(169,3),(173,0),(197,0)]),([6,v7,v3,v1,v4,v2,v0,v11],[(56,2),(96,2),(196,0),(216,2)]),([6,v7,v3,v1,vf,v2,v0],[(196,0),(197,0),(198,0)]),([6,v7,v1,v4,vf,v2,v0],[(10,2)]),([6,vd,v3,v1,v4,4244438268,v2,v0],[(56,5),(128,5),(252,0)]),([6,vd,v3,v1,v4,v2,v0],[(2,8),(6,5),(73,5),(118,5),(129,1),(133,1),(141,1),(169,3),(173,3),(177,0),(181,3)]),([6,vd,v1,v4,4244438268,v2,v0],[(14,2),(86,5),(193,0),(196,0),(197,0),(198,0)]),([6,vd,v1,v4,v2,v0],[(2,8),(3,8),(10,2),(11,2),(14,0),(15,0),(17,0),(85,5),(86,5),(87,5),(103,1),(111,7),(131,0),(135,3),(139,0),(143,9),(147,0),(151,0)]),([6,v15,v3,v1,v4,v2,va,v0],[]),([6,v15,v3,v1,v4,v2,v0],[(2,9),(73,5),(129,1),(133,1),(157,1),(169,3),(173,3),(181,3),(205,1)]),([6,v3,v3,v3,v1,v4,v2,v0],[]),([6,v3,v3,v1,v1,v4,v2,v0],[(48,5),(52,5)]),([6,v3,v3,v1,vc,v4,v2,v0],[(196,1),(244,3)]),([6,v3,v3,v1,v6,v4,v2,v0],[(172,1)]),([6,v3,v3,v1,v4,v4,v2,v0],[]),([6,v3,v3,v1,v4,vf,v2,v0],[(148,5),(204,1),(252,3)]),([6,v3,v3,v1,v4,4244438268,v2,v0],[(48,5),(52,5),(204,1),(252,3)]),([6,v3,v3,v1,v4,v2,va,v0],[]),([6,v3,v3,v1,v4,v2,v0],[(2,5),(129,1),(133,1),(169,3),(173,3)]),([6,v3,2863333375,v1,v4,v2,v0],[(6,9),(77,5),(85,5),(137,1),(141,1),(169,5),(181,3)]),([6,v3,3149642683,v1,v4,v2,v0],[(6,5),(73,5),(133,1),(137,1),(141,1),(173,3),(177,3),(181,3)]),([6,v3,v1,v8,vc,v4,v2,v0],[(244,0)]),([6,v3,v1,v8,vc,v2,v0],[(61,5),(110,5),(157,1),(193,0),(196,0),(197,3),(198,0)]),([6,v3,v1,v8,v4,v2,v0],[(10,2),(14,2),(61,5),(82,5),(86,5),(106,5),(110,5),(145,1),(185,3),(189,0),(193,0),(197,0)]),([6,v3,v1,v8,v2,v0],[(2,5),(3,5),(5,5),(10,2),(11,2),(14,0),(15,0),(17,0),(61,5),(83,5),(87,5),(103,1),(107,5),(111,7),(131,0),(135,3),(139,6),(143,9),(147,0),(151,0)]),([6,v3,v1,3941264106,v4,v2,v0],[(10,8),(61,5),(84,5),(85,5),(86,5),(145,1),(148,1),(149,1),(150,1),(185,3),(188,3),(189,3),(190,3)]),([6,v3,v1,vc,vc,v4,v2,v0],[(188,1),(236,3)]),([6,v3,v1,vc,v6,v4,v2,v0],[(188,1),(236,3)])]

def K_27 : List (List Nat × List (Nat × Nat)) := [([6,v3,v1,vc,v4,v4,v2,v0],[(188,1),(236,3)]),([6,v3,v1,vc,v4,vf,v2,v0],[(140,5),(188,1),(204,1),(236,3),(252,3)]),([6,v3,v1,vc,v4,4278124286,v2,v0],[(188,1),(204,1),(236,3),(252,3)]),([6,v3,v1,vc,v4,v2,va,v0],[(148,1),(236,3)]),([6,v3,v1,vc,v4,v2,v0],[(61,5),(86,5),(145,1),(148,1),(149,1),(150,1),(185,3),(188,3),(189,3),(190,3)]),([6,v3,v1,v10,v6,v4,v2,v0],[(248,1)]),([6,v3,v1,v10,v4,v2,v0],[(82,5),(86,5),(110,5),(134,1),(142,7),(145,1),(152,3),(153,2),(154,0),(174,3),(182,9),(185,3),(192,1),(193,4),(201,3),(202,1)]),([6,v3,v1,v6,v6,v4,v2,v0],[]),([6,v3,v1,v6,v1c,v4,v2,v0],[(144,0),(184,0),(200,0),(232,0)]),([6,v3,v1,v6,v4,v4,v2,v0],[]),([6,v3,v1,v6,v4,4205509290,v2,v0],[(140,5),(204,1)]),([6,v3,v1,v6,v4,vf,v2,v0],[(140,5),(204,1)]),([6,v3,v1,v6,v4,v2,va,v0],[(116,1),(192,1)]),([6,v3,v1,v6,v4,v2,v0],[(10,3),(82,5),(86,5),(110,5),(134,1),(142,7),(145,1),(153,1),(185,3),(193,1)]),([6,v3,v1,v6,v4,v2,v0,v0],[(112,3),(144,3),(184,3),(192,1)]),([6,v3,v1,v6,v4,v2,v0,4294945450],[(112,3),(144,3),(228,9),(232,3),(252,1)]),([6,v3,v1,v6,v4,v2,v0,4294963200],[(112,3),(144,3),(232,3),(240,1)]),([6,v3,v1,v6,v4,v2,v0,v17],[(112,0),(116,1),(144,0),(232,0),(240,1)]),([6,v3,v1,v6,v4,va,v0],[(14,2),(106,5),(110,5),(142,5),(189,0),(197,0)]),([6,v3,v1,v6,v4,v0,v11],[(110,5),(149,3),(174,2),(182,8),(193,1)]),([6,v3,v1,v6,va,v0],[(2,5),(3,5),(5,5),(10,3),(11,3),(14,3),(15,3),(83,5),(87,5),(107,5),(110,5),(111,5),(135,3),(139,5),(143,9),(149,3)]),([6,v3,v1,ve,v4,v2,v1b,v0],[(112,1),(180,7),(184,1)]),([6,v3,v1,ve,v4,v2,v0],[(10,10),(14,2),(82,5),(86,5),(110,5),(134,1),(145,1),(185,3),(189,0),(197,0)]),([6,v3,v1,ve,v2,v1b,v0],[(18,6),(102,1),(140,7),(141,7),(142,7),(205,4)]),([6,v3,v1,ve,v2,v0],[(2,5),(3,5),(5,5),(10,10),(11,10),(14,0),(15,0),(87,5),(102,1),(103,1),(111,7),(135,3),(143,9),(151,0),(159,2)]),([6,v3,v1,4042321920,v4,v2,v0],[(10,2),(82,5),(86,5),(110,5),(145,1),(185,3),(189,0),(193,0)]),([6,v3,v1,4042321920,v4,v2,v0,v11],[(112,2),(188,0),(204,2),(232,2)]),([6,v3,v1,v4,v4,v4,v2,v0],[]),([6,v3,v1,v4,v4,vf,v2,v0],[(140,5),(204,1),(252,3)]),([6,v3,v1,v4,v4,v2,v2,v0],[(88,1),(92,1)]),([6,v3,v1,v4,v4,v2,v1b,v0],[(88,1),(92,1),(180,7),(260,4)]),([6,v3,v1,v4,v4,v2,va,v0],[]),([6,v3,v1,v4,v4,v2,v0],[(10,2),(82,5),(86,5),(185,0),(189,0)]),([6,v3,v1,v4,v4,v2,v0,v11],[(88,2),(92,2),(188,0),(204,2)]),([6,v3,v1,v4,4042326015,v2,v0],[(14,4),(86,5),(106,5),(110,5),(145,2),(156,1),(157,1),(158,1),(185,2),(197,0)]),([6,v3,v1,v4,4092851187,v2,v0],[(14,8),(82,2),(110,5),(149,1),(157,1),(189,3),(193,0),(197,3)])]

def K_28 : List (List Nat × List (Nat × Nat)) := [([6,v3,v1,v4,4177066232,v2,v0],[(14,2),(86,5),(106,5),(108,5),(109,5),(110,5),(145,2),(156,1),(157,1),(158,1),(185,4),(193,0),(196,3),(197,3),(198,3)]),([6,v3,v1,v4,4205509290,v2,v0],[(14,9),(108,5),(109,5),(110,5),(134,1),(153,1),(156,1),(157,1),(158,1),(193,3),(196,3),(197,3),(198,3)]),([6,v3,v1,v4,4210096880,v2,v0],[(14,10),(82,2),(106,5),(110,5),(149,1),(156,1),(157,1),(158,1),(189,3),(193,0),(197,3),(205,4)]),([6,v3,v1,v4,vf,vf,v2,v0],[(108,5),(196,1),(244,3)]),([6,v3,v1,v4,vf,4244438268,v2,v0],[(100,5),(108,5),(116,5),(196,1),(204,7),(244,3),(252,9)]),([6,v3,v1,v4,vf,4278124286,v2,v0],[(108,5),(196,1),(204,1),(244,3),(252,3)]),([6,v3,v1,v4,vf,v2,v1b,v0],[(100,1),(108,5),(116,1),(156,1),(180,7),(244,3),(260,4)]),([6,v3,v1,v4,vf,v2,4291624908,v0],[(100,7),(108,5),(116,7),(156,1),(172,1),(188,5),(244,3),(260,10)]),([6,v3,v1,v4,vf,v2,va,v0],[(108,5),(156,1),(244,3)]),([6,v3,v1,v4,vf,v2,4294639610,v0],[(108,5),(156,1),(180,5),(244,3),(260,3)]),([6,v3,v1,v4,vf,v2,v0],[(14,8),(108,5),(109,5),(110,5),(156,1),(157,1),(158,1),(193,0),(196,3),(197,3),(198,3)]),([6,v3,v1,v4,vf,v2,v0,v11],[(100,2),(108,5),(116,2),(156,1),(196,3),(204,2)]),([6,v3,v1,v4,4278124286,v2,v0],[(14,2),(110,5),(156,1),(157,1),(158,1),(193,0),(196,3),(197,3),(198,3)]),([6,v3,v1,v4,v2,4293980400,v0],[(18,2),(117,1),(138,5),(142,5),(158,1),(189,3),(201,0),(205,3)]),([6,v3,v1,v4,v2,va,va,v0],[]),([6,v3,v1,v4,v2,va,4294639610,v0],[(180,5),(260,3)]),([6,v3,v1,v4,v2,va,v0],[(18,3),(117,1),(138,5),(142,5),(158,1),(189,3),(197,4),(205,3)]),([6,v3,v1,v4,v2,va,v0,v17],[(148,0),(156,0),(188,0),(196,2),(204,3),(244,1)]),([6,v3,v1,v4,v2,va,v0,v13],[(188,0),(196,2),(204,3),(228,5)]),([6,v3,v1,v4,v2,4294639610,v0],[(18,9),(140,5),(141,5),(142,5),(158,1),(204,3),(205,3),(206,3)]),([6,v3,v1,v4,v2,v0],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(131,3),(135,3),(139,9),(143,9),(147,0),(151,0),(155,2),(159,2)]),([6,v3,v1,v4,v2,v0,v13],[(117,1),(148,0),(149,3),(150,0),(156,2),(157,4),(158,2),(178,5),(180,5),(181,5),(182,5),(198,1),(206,3)]),([6,v3,v1,v4,v2,v0,4294967295],[(182,5),(198,1),(206,3)]),([7,v9,v3,v1,v4,v2],[(6,5),(7,5),(9,5),(14,1),(15,1),(17,1),(75,5),(79,5),(115,5),(119,5),(131,1),(135,1),(139,1),(143,1),(147,7),(151,7)]),([7,v9,v3,v1,v4,v2,v0],[(2,3),(6,5),(7,5),(9,5),(14,2),(15,1),(17,1),(18,0),(73,5),(75,5),(77,5),(79,5),(115,5),(119,5),(129,1),(131,1),(133,1),(135,1),(139,1),(143,1),(147,7),(151,7),(186,5),(187,5),(190,5),(191,5),(202,1),(203,1),(206,1),(207,1)]),([7,vb,v3,v1,v4,v2,v0],[(2,5),(6,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(129,1),(131,1),(133,1),(135,1),(139,1),(143,1),(145,1),(147,1),(149,1),(151,1),(169,3),(171,3),(173,3),(175,3),(179,3),(183,3),(185,3),(187,3),(189,3),(191,3),(195,0),(199,0),(203,2),(207,2)]),([7,vb,v3,v4,v2,v0],[(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(99,1),(103,1),(107,1),(111,1),(131,3),(135,3),(139,3),(143,3),(147,0),(151,0),(155,2),(159,2)]),([7,v5,v3,v1,v4,v2,v0],[(6,5),(7,5),(9,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(73,5),(75,5),(81,5),(115,5),(117,5),(119,5),(129,1),(131,1),(133,1),(135,1),(139,1),(141,1),(143,1),(147,7),(149,7),(151,7),(169,3),(171,3),(173,3),(175,3),(179,3),(181,3),(183,3),(187,9),(189,9),(191,9),(195,0),(199,0),(203,2),(207,2)]),([7,v7,v3,v1,v4,v2,v0],[(2,8),(3,8),(6,5),(7,5),(14,2),(15,2),(18,0),(19,0),(21,0),(73,5),(129,1),(169,3),(171,0),(173,0),(175,0),(179,0),(183,0),(187,0),(191,0),(195,0),(197,0),(199,0)]),([7,v3,v3,v1,v4,v2,v0],[(2,5),(3,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(119,5),(129,1),(131,1),(133,1),(135,1),(147,1),(151,7),(169,3),(171,3),(173,3),(175,3),(187,3),(191,9),(195,0),(199,0),(203,2),(207,2)]),([7,v3,v1,vc,v4,v2,v0],[(2,5),(3,5),(5,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(61,5),(86,5),(87,5),(107,5),(111,5),(131,1),(135,1),(139,7),(143,7),(145,1),(147,1),(148,1),(149,1),(150,1),(151,1),(171,3),(175,3),(179,9),(183,9),(185,3),(187,3),(188,3),(189,3),(190,3),(191,3),(195,0),(199,0),(203,2),(207,2)]),([7,v3,v1,v6,v4,v2,v0],[(2,5),(3,5),(5,5),(10,3),(11,3),(14,2),(15,2),(17,1),(18,0),(19,0),(82,5),(83,5),(86,5),(87,5),(107,5),(110,5),(111,5),(131,1),(134,1),(135,1),(139,7),(142,7),(143,7),(145,1),(147,1),(153,1),(175,3),(179,5),(183,9),(185,3),(193,1),(203,1),(207,1)]),([7,v3,v1,v4,v4,v2,v0],[(2,5),(3,5),(5,5),(10,2),(11,2),(18,0),(19,0),(21,0),(82,5),(83,5),(86,5),(87,5),(135,1),(139,5),(143,7),(171,0),(175,3),(179,6),(183,9),(185,0),(187,0),(189,0),(191,0),(207,2)]),([7,v3,v1,v4,vf,v2,v0],[(2,5),(3,5),(5,5),(10,2),(11,2),(14,8),(15,8),(17,1),(18,0),(19,0),(21,3),(87,5),(108,5),(109,5),(110,5),(111,5),(135,1),(143,7),(156,1),(157,1),(158,1),(159,1),(171,0),(175,3),(179,0),(183,9),(187,0),(191,0),(193,0),(195,0),(196,3),(197,3),(198,3),(199,3),(207,2)]),([7,v3,v1,v4,v2,va,v0],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(18,3),(19,3),(21,3),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(117,1),(138,5),(139,5),(142,5),(143,5),(158,1),(159,1),(171,3),(175,3),(179,9),(183,9),(189,3),(191,0),(195,1),(197,4),(199,2),(205,3),(207,3)]),([7,v3,v1,v4,v2,v0],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(131,3),(135,3),(139,9),(143,9),(147,0),(151,0),(155,2),(159,2)])]

def K_29 : List (List Nat × List (Nat × Nat)) := [([8,v3,v1,v4,v2,v0],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(131,3),(135,3),(139,9),(143,9),(147,0),(151,0),(155,2),(159,2)])]

def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,2829625504,v1,v10] BT.lf) [2,v15,v1,4169662464] BT.lf) [2,2863180448,v1,v10] (BT.nd BT.lf [2,v12,3435973824,v10] BT.lf)) [2,v12,v1,v10] (BT.nd (BT.nd BT.lf [3,v5,3758153728,4277206768,v0] BT.lf) [3,v5,3758153728,va,v0] (BT.nd BT.lf [3,v5,3766542464,v14,v0] BT.lf))) [3,v5,3766542464,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [3,v5,3768623264,v2,v0] BT.lf) [3,v5,v18,v14,v0] (BT.nd BT.lf [3,v5,v18,4004118528,v2] BT.lf)) [3,v5,v18,v2,v0] (BT.nd (BT.nd BT.lf [3,v5,3772833952,v2,v0] BT.lf) [3,v5,v8,v14,4008574976] (BT.nd BT.lf [3,v5,v8,v14,v0] BT.lf)))) [3,v5,v8,4160813056,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,v5,v8,v19,v0] BT.lf) [3,v5,v8,4261477888,v0] (BT.nd BT.lf [3,v5,v8,v16,v11] BT.lf)) [3,v5,v8,4278224896,v0] (BT.nd (BT.nd BT.lf [3,v5,v8,4278233600,v0] BT.lf) [3,v5,v8,4278251008,v0] (BT.nd BT.lf [3,v5,v8,v2,v0] BT.lf))) [3,v5,v8,v2,4294906129] (BT.nd (BT.nd (BT.nd BT.lf [3,v5,v8,v2,4294934656] BT.lf) [3,v5,v8,v2,4294936576] (BT.nd BT.lf [3,v5,3772838128,v2,v0] BT.lf)) [3,v5,3907053792,v2,v0] (BT.nd (BT.nd BT.lf [3,v5,3938511552,v6,v0] BT.lf) [3,v5,4007718624,v6,v0] (BT.nd BT.lf [3,v7,2852170240,3364407432,v0] BT.lf))))) [3,v7,2852170240,v1,4205445120] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,v7,2863311360,v1,v10] BT.lf) [3,v7,3364391048,v2,v0] BT.lf) [3,2827528328,3435187392,v6,v0] (BT.nd BT.lf [3,2829625504,v1,v6,v0] BT.lf)) [3,2829625504,v1,v4,v16] (BT.nd (BT.nd BT.lf [3,v15,v1,v6,4205445120] BT.lf) [3,v15,v1,4169726088,v0] (BT.nd BT.lf [3,2863180448,v1,v6,v0] BT.lf))) [3,2863180448,v1,v1c,v2] (BT.nd (BT.nd (BT.nd BT.lf [3,v12,v3,v1,v10] BT.lf) [3,v12,3435973824,v6,v0] (BT.nd BT.lf [3,v12,v1,v10] BT.lf)) [3,v12,v1,v10,v6] (BT.nd (BT.nd BT.lf [3,v12,v1,v10,v4] BT.lf) [3,v12,v1,v10,va] (BT.nd BT.lf [3,v12,v1,v10,v13] BT.lf)))) [3,v12,v1,v6,v1c] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,v12,v1,v6,4293918720] BT.lf) [3,v12,v1,v6,v0] (BT.nd BT.lf [3,v3,v1,v10,4210752240] BT.lf)) [3,v3,v1,v10,4294639600] (BT.nd (BT.nd BT.lf [3,v3,v1,v10,v13] BT.lf) [3,v3,v1,4026532080,v11] (BT.nd BT.lf [3,v3,v1,v6,4294905840] BT.lf))) [3,v3,v1,v6,4294936704] (BT.nd (BT.nd (BT.nd BT.lf [3,v3,v1,4026597360,v0] BT.lf) [3,v3,v1,4034953344,v11] (BT.nd BT.lf [3,v3,v1,v1d,4294936576] BT.lf)) [3,v3,v1,v4,4287137792] (BT.nd (BT.nd BT.lf [4,61680,v3,v1,4026597120,v0] BT.lf) [4,65520,v3,v1,v6,v0] (BT.nd BT.lf [4,v9,v5,v8,v2] BT.lf)))))) [4,v9,v5,v8,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v9,v5,4008574976,v4,v2] BT.lf) [4,v9,2863267840,3435956360,v4,v2] BT.lf) [4,16776960,v3,v1,v4,v16] (BT.nd BT.lf [4,286331153,v5,v8,v2,v0] BT.lf)) [4,286392319,v5,4008574976,v4,v2] (BT.nd (BT.nd BT.lf [4,286392319,v5,v4,v2] BT.lf) [4,vb,v5,v8,v2,v0] (BT.nd BT.lf [4,1717986918,v5,v4,v2,v0] BT.lf))) [4,1886449904,v3,v1,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,2004318071,v5,v8,v2,v0] BT.lf) [4,2004318071,v8,v2,v0] (BT.nd BT.lf [4,2155905152,v5,v8,v2,v0] BT.lf)) [4,2155905152,v5,v14,v4,v0] (BT.nd (BT.nd BT.lf [4,2155905152,v3,v1,4160813056,v0] BT.lf) [4,2290124928,v3,v1,v6,v0] (BT.nd BT.lf [4,v5,v5,v8,v2,v0] BT.lf)))) [4,v5,2684395520,v1a,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v5,v7,v1a,v2,v0] BT.lf) [4,v5,v7,3368601800,v2,v0] (BT.nd BT.lf [4,v5,v7,3422604288,v6,v0] BT.lf)) [4,v5,v7,v1,4160813056,v0] (BT.nd (BT.nd BT.lf [4,v5,v7,v1,v19,v0] BT.lf) [4,v5,v7,v8,v2,v0] (BT.nd BT.lf [4,v5,v7,3959483392,v4,v0] BT.lf))) [4,v5,v7,v14,v4,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v5,v15,v1,v6,v0] BT.lf) [4,v5,v3,v18,v2,v0] (BT.nd BT.lf [4,v5,v3,3770736832,v2,v0] BT.lf)) [4,v5,v3,v8,v14,v0] (BT.nd (BT.nd BT.lf [4,v5,v3,v8,v2,v0] BT.lf) [4,v5,3758153728,v8,v2,v0] (BT.nd BT.lf [4,v5,3758153728,v4,v2,v0] BT.lf))))) [4,v5,v18,4004179626,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v5,v18,v4,v2,v0] BT.lf) [4,v5,v18,v2,v0] (BT.nd BT.lf [4,v5,v8,v8,v2,v0] BT.lf)) [4,v5,v8,3907578088,v2,v0] (BT.nd (BT.nd BT.lf [4,v5,v8,3941264106,v2,v0] BT.lf) [4,v5,v8,v14,vc,v0] (BT.nd BT.lf [4,v5,v8,v14,v4,v0] BT.lf))) [4,v5,v8,v14,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v5,v8,vc,v2,v0] BT.lf) [4,v5,v8,v6,v2,v0] (BT.nd BT.lf [4,v5,v8,v4,v2,v0] BT.lf)) [4,v5,v8,4177066232,v2,v0] (BT.nd (BT.nd BT.lf [4,v5,v8,vf,v2,v0] BT.lf) [4,v5,v8,4278124286,v2,v0] (BT.nd BT.lf [4,v5,v8,v16,v2,v0] BT.lf)))) [4,v5,v8,v2,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v5,v8,v2,4287168392,v0] BT.lf) [4,v5,v8,v2,v1b,v0] (BT.nd BT.lf [4,v5,v8,v2,4292935648,v0] BT.lf)) [4,v5,v8,v2,4293853166,v0] (BT.nd (BT.nd BT.lf [4,v5,v8,v2,va,v0] BT.lf) [4,v5,v8,v2,v0] (BT.nd BT.lf [4,v5,v8,v2,v0,v11] BT.lf))) [4,v5,3907578088,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v5,3937069738,v4,v2,v0] BT.lf) [4,v5,3938511552,v4,v2,v0] (BT.nd BT.lf [4,v5,3941264106,v4,v2,v0] BT.lf)) [4,v5,4007718624,v4,v2,v0] (BT.nd (BT.nd BT.lf [4,v5,4008373994,v4,v2,v0] BT.lf) [4,v5,vc,v6,va,v0] (BT.nd BT.lf [4,v5,vc,v1d,v2,v0] BT.lf))))))) [4,v5,vc,ve,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v5,vc,4041273568,v2,v0] BT.lf) [4,v5,vc,v4,v2,v0] BT.lf) [4,v5,vc,v4,v2,4294906129] (BT.nd BT.lf [4,v5,vc,v4,v2,4294934656] BT.lf)) [4,v5,4008640511,v4,v2,v0] (BT.nd (BT.nd BT.lf [4,2576980377,vc,v4,v2,v0] BT.lf) [4,v7,2852170240,v1,4205509290,v0] (BT.nd BT.lf [4,v7,2863311360,v1,v6,v0] BT.lf))) [4,v7,2863311360,v1,v4,v16] (BT.nd (BT.nd (BT.nd BT.lf [4,v7,v3,3364407432,v2,v0] BT.lf) [4,v7,v3,3368601800,v19,v0] (BT.nd BT.lf [4,v7,v3,3368601800,v2,v0] BT.lf)) [4,v7,v3,v1,3925928448,v0] (BT.nd (BT.nd BT.lf [4,v7,v3,v1,v10,v11] BT.lf) [4,v7,v3,v1,4026597120,v0] (BT.nd BT.lf [4,v7,v3,v1,4160813056,v0] BT.lf)))) [4,v7,v3,v1,4194347520,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v7,v3,v1,v19,4210688000] BT.lf) [4,v7,v3,v1,v19,v0] (BT.nd BT.lf [4,v7,v1,4205488810,v2,v0] BT.lf)) [4,2827520136,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [4,2827528328,v1,v6,va,v0] BT.lf) [4,2827528328,v1,4039176384,v2,v0] (BT.nd BT.lf [4,2827528328,v1,v4,4241227776,v2] BT.lf))) [4,2827528328,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,2829101216,v3,v1,v6,v0] BT.lf) [4,2829625480,v1,v4,v2,v0] (BT.nd BT.lf [4,2829625504,v1,v4,v2,v0] BT.lf)) [4,vd,3368601800,v4,v2,v0] (BT.nd (BT.nd BT.lf [4,vd,3431517320,v4,v2,v0] BT.lf) [4,vd,v1,v8,v2,v0] (BT.nd BT.lf [4,vd,v1,3959483392,v4,v0] BT.lf))))) [4,vd,v1,v14,v4,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,vd,v1,v6,va,v0] BT.lf) [4,vd,v1,ve,v2,v0] BT.lf) [4,vd,v1,4039176384,v2,v0] (BT.nd BT.lf [4,vd,v1,v4,4160813056,v0] BT.lf)) [4,vd,v1,v4,v19,v0] (BT.nd (BT.nd BT.lf [4,vd,v1,v4,4227922944,4244373504] BT.lf) [4,vd,v1,v4,4227922944,v0] (BT.nd BT.lf [4,vd,v1,v4,4261477888,v0] BT.lf))) [4,vd,v1,v4,v16,v11] (BT.nd (BT.nd (BT.nd BT.lf [4,vd,v1,v4,4278233088,v0] BT.lf) [4,vd,v1,v4,4278233600,v0] (BT.nd BT.lf [4,vd,v1,v4,4278242304,v0] BT.lf)) [4,vd,v1,v4,4278254592,v0] (BT.nd (BT.nd BT.lf [4,vd,v1,v4,v2,v0] BT.lf) [4,vd,v1,v4,v2,4294902531] (BT.nd BT.lf [4,vd,v1,4092851187,v2,v0] BT.lf)))) [4,vd,v1,4176541936,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,vd,v1,4210096880,v2,v0] BT.lf) [4,vd,3486502863,v4,v2,v0] (BT.nd BT.lf [4,2829626026,v1,v4,v2,v0] BT.lf)) [4,v15,v3,v1,v10,v0] (BT.nd (BT.nd BT.lf [4,v15,v3,v1,v6,v0] BT.lf) [4,v15,v1,v6,4205509290,v0] (BT.nd BT.lf [4,2863179944,v1,v4,v2,v0] BT.lf))) [4,2863180448,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,2863180456,v1,v6,va,v0] BT.lf) [4,2863180456,v1,4039176384,v2,v0] (BT.nd BT.lf [4,2863180456,v1,v4,4244373504,v2] BT.lf)) [4,2863180456,v1,v4,v2,4294705152] (BT.nd (BT.nd BT.lf [4,2863180456,v1,v4,v2,v0] BT.lf) [4,v12,v3,v1,v6,v0] (BT.nd BT.lf [4,v12,3435973824,v4,v2,v0] BT.lf)))))) [4,v12,v1,v6,v4,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v12,v1,v6,va,v0] BT.lf) [4,v12,v1,v6,v0] BT.lf) [4,v12,v1,v6,v0,v17] (BT.nd BT.lf [4,v12,v1,v6,v0,v13] BT.lf)) [4,v12,v1,4042321920,v2,v0] (BT.nd (BT.nd BT.lf [4,v12,v1,v4,v2,v0] BT.lf) [4,2863311528,v1,v4,v2,v0] (BT.nd BT.lf [4,v3,v1,3758153728,4277206768,v0] BT.lf))) [4,v3,v1,3758153728,va,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,3768623264,v2,v0] BT.lf) [4,v3,v1,v18,v14,v0] (BT.nd BT.lf [4,v3,v1,v18,4004118528,v2] BT.lf)) [4,v3,v1,v18,v2,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,3772833952,v2,v0] BT.lf) [4,v3,v1,v8,v14,4008574976] (BT.nd BT.lf [4,v3,v1,v8,v14,v0] BT.lf)))) [4,v3,v1,v8,v19,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,v8,4261477888,v0] BT.lf) [4,v3,v1,v8,v16,v11] (BT.nd BT.lf [4,v3,v1,v8,4278233600,v0] BT.lf)) [4,v3,v1,v8,4278251008,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,v8,v2,v0] BT.lf) [4,v3,v1,v8,v2,4294906129] (BT.nd BT.lf [4,v3,v1,3772838128,v2,v0] BT.lf))) [4,v3,v1,3938511552,v6,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,4007718624,v6,v0] BT.lf) [4,v3,v1,v10,v6,v13] (BT.nd BT.lf [4,v3,v1,v10,v4,4289396480] BT.lf)) [4,v3,v1,v10,v4,v11] (BT.nd (BT.nd BT.lf [4,v3,v1,v10,v4,v13] BT.lf) [4,v3,v1,v10,4293980400,v11] (BT.nd BT.lf [4,v3,v1,v10,va,v17] BT.lf))))) [4,v3,v1,v10,va,v13] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,v10,v13] BT.lf) [4,v3,v1,4026572800,4293982960,v0] (BT.nd BT.lf [4,v3,v1,4026572800,va,v0] BT.lf)) [4,v3,v1,v6,v1c,v13] (BT.nd (BT.nd BT.lf [4,v3,v1,v6,v4,4294905600] BT.lf) [4,v3,v1,v6,v4,4294936576] (BT.nd BT.lf [4,v3,v1,v6,4042326000,v0] BT.lf))) [4,v3,v1,v6,4176541936,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,v6,4204853920,v0] BT.lf) [4,v3,v1,v6,4205445120,va] (BT.nd BT.lf [4,v3,v1,v6,4210096880,v0] BT.lf)) [4,v3,v1,v6,4210688000,va] (BT.nd (BT.nd BT.lf [4,v3,v1,v6,4210752240,v0] BT.lf) [4,v3,v1,v6,4277206768,v0] (BT.nd BT.lf [4,v3,v1,v6,4293918720,v13] BT.lf)))) [4,v3,v1,v6,4293962400,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,v6,4293982960,v0] BT.lf) [4,v3,v1,v6,va,4294574080] (BT.nd BT.lf [4,v3,v1,v6,va,v0] BT.lf)) [4,v3,v1,v6,4294180851,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,v6,4294639600,v0] BT.lf) [4,v3,v1,v6,v0,4294945440] (BT.nd BT.lf [4,v3,v1,v6,v0,4294966000] BT.lf))) [4,v3,v1,v6,v0,v13] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,4026593440,v2,v0] BT.lf) [4,v3,v1,4026593520,v2,v0] (BT.nd BT.lf [4,v3,v1,4026593520,4278255600,v0] BT.lf)) [4,v3,v1,4026593520,va,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,4026593520,v0,v11] BT.lf) [4,v3,v1,4026597375,va,v0] (BT.nd BT.lf [4,v3,v1,4027576335,va,v0] BT.lf)))))))) [4,v3,v1,4029739248,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,4034953344,v2,v0] BT.lf) [4,v3,v1,v1d,v2,4287102976] BT.lf) [4,v3,v1,v1d,v2,v0] (BT.nd BT.lf [4,v3,v1,v1d,4286644096,v0] BT.lf)) [4,v3,v1,v1d,va,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,v1d,v0,v11] BT.lf) [4,v3,v1,4037058720,4278233600,v0] (BT.nd BT.lf [4,v3,v1,4037058720,v2,v0] BT.lf))) [4,v3,v1,4037066880,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,4037075104,4278242304,v0] BT.lf) [4,v3,v1,4037075104,v2,v0] (BT.nd BT.lf [4,v3,v1,4037079168,v2,v0] BT.lf)) [4,v3,v1,ve,v19,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,ve,4210688000,v2] BT.lf) [4,v3,v1,ve,4227922944,v0] (BT.nd BT.lf [4,v3,v1,ve,4244373504,v2] BT.lf)))) [4,v3,v1,ve,v2,4289331200] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,ve,v2,4291559424] BT.lf) [4,v3,v1,ve,v2,4293787648] (BT.nd BT.lf [4,v3,v1,ve,v2,4294574080] BT.lf)) [4,v3,v1,ve,v2,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,ve,v2,4294901845] BT.lf) [4,v3,v1,ve,4283826005,v0] (BT.nd BT.lf [4,v3,v1,ve,4286644096,v0] BT.lf))) [4,v3,v1,ve,4290838464,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,ve,4291624704,v0] BT.lf) [4,v3,v1,4037079280,v2,v0] (BT.nd BT.lf [4,v3,v1,4038127792,v2,v0] BT.lf)) [4,v3,v1,4041269472,v2,v0] (BT.nd (BT.nd BT.lf [4,v3,v1,4041273504,v2,v0] BT.lf) [4,v3,v1,4041273568,v2,4293787648] (BT.nd BT.lf [4,v3,v1,4041273568,v2,v0] BT.lf))))) [4,v3,v1,4042322048,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,4042322080,v2,v0] BT.lf) [4,v3,v1,4042322144,v2,v0] BT.lf) [4,v3,v1,v4,v2,v0] (BT.nd BT.lf [4,v3,v1,v4,v2,4294901763] BT.lf)) [4,v3,v1,v4,v2,4294901777] (BT.nd (BT.nd BT.lf [4,v3,v1,v4,v2,4294901794] BT.lf) [4,v3,v1,v4,v2,4294901808] (BT.nd BT.lf [4,v3,v1,v4,v2,4294901811] BT.lf))) [4,v3,v1,v4,v2,4294901879] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,v4,v2,4294901920] BT.lf) [4,v3,v1,v4,v2,4294902000] (BT.nd BT.lf [4,v3,v1,v4,v2,4294902579] BT.lf)) [4,v3,v1,v4,v2,4294905872] (BT.nd (BT.nd BT.lf [4,v3,v1,v4,v2,4294906129] BT.lf) [4,v3,v1,v4,v2,4294906163] (BT.nd BT.lf [4,v3,v1,v4,v2,4294934528] BT.lf)))) [4,v3,v1,v4,v2,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v3,v1,v4,v2,4294936704] BT.lf) [4,v3,v1,v4,4278451971,4294902531] (BT.nd BT.lf [4,v3,v1,v4,4279238400,4294905615] BT.lf)) [4,v3,v1,v4,4279369489,4294906129] (BT.nd (BT.nd BT.lf [4,v3,v1,v4,4286644096,4294934656] BT.lf) [4,v3,v1,v4,4287137928,v11] (BT.nd BT.lf [4,v3,v1,v4,4287168256,4294936712] BT.lf))) [4,v3,3435973839,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [4,v3,3435973853,v4,v2,v0] BT.lf) [4,v3,3435977948,v4,v2,v0] (BT.nd BT.lf [4,v3,3435978205,4042301600,v2,v0] BT.lf)) [4,v3,3435978205,v4,v2,v0] (BT.nd (BT.nd BT.lf [4,v3,3435978205,v4,4278255445,v0] BT.lf) [4,v3,3437092317,v4,v2,v0] (BT.nd BT.lf [4,v3,3722304989,v8,v2,v0] BT.lf)))))) [4,v3,3972844748,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,0,v3,v1,v4,v2,v0] BT.lf) [5,15,v3,v1,v4,v2,v0] BT.lf) [5,51,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,170,v3,v1,v4,v2,v0] BT.lf)) [5,240,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,255,v3,v1,v4,v16] BT.lf) [5,255,v3,v1,v4,v16,v11] (BT.nd BT.lf [5,255,v3,v1,v4,v2,v0] BT.lf))) [5,4095,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,4369,v3,v1,v4,v2,v0] BT.lf) [5,8738,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,12336,v3,v1,v4,v2,v0] BT.lf)) [5,13107,2863302792,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,13107,v3,v1,4042309824,v2,v0] BT.lf) [5,13107,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,13107,v3,v1,v4,4278255411,v0] BT.lf)))) [5,13107,2863315899,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,13311,v3,v1,v4,v2,v0] BT.lf) [5,30583,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,34952,v3,v1,v4,v2,v0] BT.lf)) [5,41120,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,43690,2863267840,v1,v4,v2,v0] BT.lf) [5,43690,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,43690,2863333375,v1,v4,v2,v0] BT.lf))) [5,61166,v3,v1,v4,v2] (BT.nd (BT.nd (BT.nd BT.lf [5,61166,v3,v1,v4,v2,v0] BT.lf) [5,61440,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,61680,v3,v1,v6,v2,v0] BT.lf)) [5,61680,v3,v1,v1c,v2,v0] (BT.nd (BT.nd BT.lf [5,61680,v3,v1,v4,v2,v0] BT.lf) [5,61680,v3,v1,v4,4278255600,v0] (BT.nd BT.lf [5,61680,v3,v1,4042326015,v2,v0] BT.lf))))) [5,64250,v3,v1,v4,v2] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,64250,v3,v1,v4,v2,v0] BT.lf) [5,65520,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,v9,16711935,252645135,v3,v1] BT.lf)) [5,v9,16711935,vb,v3,v4] (BT.nd (BT.nd BT.lf [5,v9,16711935,v3,v1,v4] BT.lf) [5,v9,vb,1431655765,v4,v2] (BT.nd BT.lf [5,v9,vb,v3,v4,v2] BT.lf))) [5,v9,v5,vc,v4,v2] (BT.nd (BT.nd (BT.nd BT.lf [5,v9,v5,vc,v4,v2,v0] BT.lf) [5,v9,vd,v1,v4,v2] (BT.nd BT.lf [5,v9,vd,v1,v4,v2,v0] BT.lf)) [5,v9,2863267840,v1,v4,v2,4294945450] (BT.nd (BT.nd BT.lf [5,v9,2863302792,v1,v4,v2] BT.lf) [5,v9,2863302792,v1,v4,v2,v0] (BT.nd BT.lf [5,v9,v3,v1,v8,v2] BT.lf)))) [5,v9,v3,v1,v8,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v9,v3,v1,4008574976,v4,v2] BT.lf) [5,v9,v3,v1,v6,va] (BT.nd BT.lf [5,v9,v3,v1,v6,va,v0] BT.lf)) [5,v9,v3,v1,4026593520,v2] (BT.nd (BT.nd BT.lf [5,v9,v3,v1,4026593520,v2,v0] BT.lf) [5,v9,v3,v1,ve,v2] (BT.nd BT.lf [5,v9,v3,v1,ve,v2,v0] BT.lf))) [5,v9,v3,v1,v1c,v2,v17] (BT.nd (BT.nd (BT.nd BT.lf [5,v9,v3,v1,4042301600,v2] BT.lf) [5,v9,v3,v1,4042301600,v2,v0] (BT.nd BT.lf [5,v9,v3,v1,v4,4210688000,v2] BT.lf)) [5,v9,v3,v1,v4,v2] (BT.nd (BT.nd BT.lf [5,v9,v3,v1,v4,v2,v0] BT.lf) [5,v9,v3,v1,v4,4278255600] (BT.nd BT.lf [5,v9,v3,v1,v4,4278255600,v0] BT.lf))))))) [5,1048575,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3355443,v3,v1,v4,v2,v0] BT.lf) [5,3407871,v3,v1,v4,v2] BT.lf) [5,3407871,v3,v1,v4,v2,4291559424] (BT.nd BT.lf [5,3407871,v3,v1,v4,v2,v0] BT.lf)) [5,11184810,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,15790320,v3,v1,v4,v2,v0] BT.lf) [5,16777215,v3,v1,v4,v16,v11] (BT.nd BT.lf [5,16777215,v3,v1,v4,v2,v0] BT.lf))) [5,16777215,v3,v1,v4,v11] (BT.nd (BT.nd (BT.nd BT.lf [5,268435455,v3,v1,v4,v2,v0] BT.lf) [5,269488144,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,286331153,v5,vc,v4,v2,v0] BT.lf)) [5,286331153,v5,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,286331153,v3,v1,v8,v2,v0] BT.lf) [5,286331153,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,286331153,v3,v1,v4,v2,4294906129] BT.lf)))) [5,286339891,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,286392319,v3,v1,4008574976,v4,v2] BT.lf) [5,286392319,v3,v1,v4,v2] (BT.nd BT.lf [5,286392319,v3,v1,v4,v2,v0] BT.lf)) [5,538976288,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,572662306,v5,v1,v4,v2,v0] BT.lf) [5,572662306,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,572662306,3149642683,v1,v4,v2,v0] BT.lf))) [5,572697258,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,805318656,v3,v1,v4,v2,v0] BT.lf) [5,808464432,v3,v1a,v1,v2,v0] (BT.nd BT.lf [5,808464432,v3,v1,v4,v2,v0] BT.lf)) [5,808464432,v3,v1,4092851187,v2,v0] (BT.nd (BT.nd BT.lf [5,808513776,v3,v1,v4,v2,v0] BT.lf) [5,842150450,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,842150450,v3,v4,v2,v0] BT.lf))))) [5,858796848,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,vb,1431655765,v4,v2,v0] BT.lf) [5,vb,v5,vc,v4,v2,v0] (BT.nd BT.lf [5,vb,vd,v1,v4,v2,v0] BT.lf)) [5,vb,vd,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,vb,v3,3368601800,v4,v2,v0] BT.lf) [5,vb,v3,v1,v8,v2,v0] (BT.nd BT.lf [5,vb,v3,v1,v6,va,v0] BT.lf))) [5,vb,v3,v1,ve,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,vb,v3,v1,4039176384,v2,v0] BT.lf) [5,vb,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,vb,v3,v8,v2,v0] BT.lf)) [5,vb,v3,v6,va,v0] (BT.nd (BT.nd BT.lf [5,vb,v3,ve,v2,v0] BT.lf) [5,vb,v3,4039176384,v2,v0] (BT.nd BT.lf [5,vb,v3,v4,v2,v0] BT.lf)))) [5,858993663,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,859010935,v3,3435956360,v4,v2,v0] BT.lf) [5,859010935,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,859010935,v3,v4,v2,v0] BT.lf)) [5,859045887,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,872415231,v3,v1,v4,v2,v0] BT.lf) [5,1886417008,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,2004318071,v5,vc,v4,v2,v0] BT.lf))) [5,2004318071,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,2004318071,vc,v4,v2,v0] BT.lf) [5,2004353023,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,2147516416,v3,v1,v4,v2,v0] BT.lf)) [5,2155905152,v5,vc,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,2155905152,v3,v1,v6,v2,v0] BT.lf) [5,2155905152,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,2155905152,v3,v1,v4,v2,4294934656] BT.lf)))))) [5,2155905152,v3,v1,4177066232,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290124928,v3,v1,v4,v2,v0] BT.lf) [5,v5,v5,vc,v4,v2,v0] BT.lf) [5,v5,2684395520,v1,v4,v2,v0] (BT.nd BT.lf [5,v5,v7,v3,v1a,v2,v0] BT.lf)) [5,v5,v7,v1a,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v5,v7,v1a,v2,v0] BT.lf) [5,v5,v7,3422604288,v4,v2,v0] (BT.nd BT.lf [5,v5,v7,v1,v6,v2,v0] BT.lf))) [5,v5,v7,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v5,v7,v1,4177066232,v2,v0] BT.lf) [5,v5,v7,v1,vf,v2,v0] (BT.nd BT.lf [5,v5,v7,3974950124,v4,v2,v0] BT.lf)) [5,v5,v7,vc,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v5,vd,v1,v4,v2,v0] BT.lf) [5,v5,v15,v1,v4,v2,v0] (BT.nd BT.lf [5,v5,v3,v1,v8,v2,v0] BT.lf)))) [5,v5,v3,v1,v6,va,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v5,v3,v1,v1d,v2,v0] BT.lf) [5,v5,v3,v1,ve,v2,v0] (BT.nd BT.lf [5,v5,v3,v1,v4,v2,v0] BT.lf)) [5,v5,v3,v1,v4,v2,4294934656] (BT.nd (BT.nd BT.lf [5,v5,v3,3435986943,v4,v2,v0] BT.lf) [5,v5,v3,v8,vc,v2,v0] (BT.nd BT.lf [5,v5,v3,v8,v4,v2,v0] BT.lf))) [5,v5,v3,v8,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v5,v3,3941264106,v4,v2,v0] BT.lf) [5,v5,v3,3974950124,v4,v2,v0] (BT.nd BT.lf [5,v5,v3,vc,v4,v2,v0] BT.lf)) [5,v5,v8,vc,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v5,v8,vc,v2,v0] BT.lf) [5,v5,v8,v4,v2,v0] (BT.nd BT.lf [5,v5,v8,v2,v0] BT.lf))))) [5,v5,3941264106,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v5,vc,vc,v4,v2,v0] BT.lf) [5,v5,vc,v6,v4,v2,v0] (BT.nd BT.lf [5,v5,vc,v4,v4,v2,v0] BT.lf)) [5,v5,vc,v4,4177066232,v2,v0] (BT.nd (BT.nd BT.lf [5,v5,vc,v4,vf,v2,v0] BT.lf) [5,v5,vc,v4,4278124286,v2,v0] (BT.nd BT.lf [5,v5,vc,v4,v2,va,v0] BT.lf))) [5,v5,vc,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,2290657962,v3,v1,v4,v2,v0] BT.lf) [5,2290679807,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,2684354560,v3,v1,v4,v2,v0] BT.lf)) [5,2684395520,v3,v1a,v1,v2,v0] (BT.nd (BT.nd BT.lf [5,2684395520,v3,v1,v6,va,v0] BT.lf) [5,2684395520,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,2684395520,v3,v1,v4,4288741280,v0] BT.lf)))) [5,2692784256,2861083272,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2692784256,v3,v1,4039176384,v2,v0] BT.lf) [5,2692784256,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,2694881280,v3,v1,v4,v2,v0] BT.lf)) [5,v7,vd,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v7,2852170240,v3,v1,v6,v0] BT.lf) [5,v7,2861083272,v1,v4,v2,v0] (BT.nd BT.lf [5,v7,2863311360,v1,v4,v2,v0] BT.lf))) [5,v7,v3,v1a,v1,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v7,v3,3368601800,v1,v2,v0] BT.lf) [5,v7,v3,3368601800,v4,v2,v0] (BT.nd BT.lf [5,v7,v3,3368601800,vf,v2,v0] BT.lf)) [5,v7,v3,3368601800,v2,v0] (BT.nd (BT.nd BT.lf [5,v7,v3,3422604288,v1,v6,v0] BT.lf) [5,v7,v3,3431517320,v4,v2,v0] (BT.nd BT.lf [5,v7,v3,v1,v8,v2,v0] BT.lf))))))))) [5,v7,v3,v1,3941264106,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v7,v3,v1,3959483392,v4,v0] BT.lf) [5,v7,v3,v1,v14,v4,v0] BT.lf) [5,v7,v3,v1,v10,v2,v0] (BT.nd BT.lf [5,v7,v3,v1,v6,v2,v0] BT.lf)) [5,v7,v3,v1,v6,4288741280,v0] (BT.nd (BT.nd BT.lf [5,v7,v3,v1,v6,va,v0] BT.lf) [5,v7,v3,v1,v6,v0,v11] (BT.nd BT.lf [5,v7,v3,v1,ve,v2,v0] BT.lf))) [5,v7,v3,v1,4039176384,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v7,v3,v1,4042321920,v2,v0] BT.lf) [5,v7,v3,v1,v4,v19,v0] (BT.nd BT.lf [5,v7,v3,v1,v4,4227922944,v0] BT.lf)) [5,v7,v3,v1,v4,v16,v11] (BT.nd (BT.nd BT.lf [5,v7,v3,v1,v4,4278233600,v0] BT.lf) [5,v7,v3,v1,v4,4278242304,v0] (BT.nd BT.lf [5,v7,v3,v1,v4,v2,v0] BT.lf)))) [5,v7,v3,v1,v4,v2,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v7,v3,v1,4042326015,v2,v0] BT.lf) [5,v7,v3,v1,4092851187,v2,v0] (BT.nd BT.lf [5,v7,v3,v1,4177066232,v2,v0] BT.lf)) [5,v7,v3,v1,v19,vf,v0] (BT.nd (BT.nd BT.lf [5,v7,v3,v1,v19,v2,v0] BT.lf) [5,v7,v3,v1,v19,v0] (BT.nd BT.lf [5,v7,v3,v1,4205509290,v2,v0] BT.lf))) [5,v7,v3,v1,4210096880,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v7,v3,v1,vf,v2,v0] BT.lf) [5,v7,3149642683,v1,v4,v2,v0] (BT.nd BT.lf [5,v7,3368601800,v4,v2,v0] BT.lf)) [5,2694884010,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,2694902000,v3,v1,v4,v2,v0] BT.lf) [5,2694905855,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,2728567458,v3,v1,v4,v2,v0] BT.lf))))) [5,2827528328,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2827528328,v1,v6,v4,v2,v0] BT.lf) [5,2827528328,v1,v4,4241292492,v2,v0] BT.lf) [5,2827528328,v1,v4,v2,v0] (BT.nd BT.lf [5,2829101216,v3,v1,v4,v2,v0] BT.lf)) [5,vd,vd,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,vd,v3,v1,v4,4227922944,v0] BT.lf) [5,vd,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,vd,v1,v1,v4,v2,v0] BT.lf))) [5,vd,v1,3974950124,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,vd,v1,vc,v4,v2,v0] BT.lf) [5,vd,v1,v6,v4,v2,v0] (BT.nd BT.lf [5,vd,v1,v4,v4,v2,v0] BT.lf)) [5,vd,v1,v4,4177066232,v2,v0] (BT.nd (BT.nd BT.lf [5,vd,v1,v4,vf,v2,v0] BT.lf) [5,vd,v1,v4,4227922944,4244438268,v0] (BT.nd BT.lf [5,vd,v1,v4,4227922944,v2,v0] BT.lf)))) [5,vd,v1,v4,4227922944,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,vd,v1,v4,4244438268,v2,v0] BT.lf) [5,vd,v1,v4,4278124286,v2,v0] (BT.nd BT.lf [5,vd,v1,v4,v16,v2,v0] BT.lf)) [5,vd,v1,v4,v2,v2,v0] (BT.nd (BT.nd BT.lf [5,vd,v1,v4,v2,4289265576,v0] BT.lf) [5,vd,v1,v4,v2,v1b,v0] (BT.nd BT.lf [5,vd,v1,v4,v2,4291624908,v0] BT.lf))) [5,vd,v1,v4,v2,va,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,vd,v1,v4,v2,4294770684,v0] BT.lf) [5,vd,v1,v4,v2,v0] (BT.nd BT.lf [5,vd,v1,v4,v2,v0,v11] BT.lf)) [5,2862653600,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v15,v3,v1,v6,v4,v0] BT.lf) [5,v15,v3,v1,v6,va,v0] (BT.nd BT.lf [5,v15,v3,v1,v6,v0] BT.lf)))))) [5,v15,v3,v1,v1c,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v15,v3,v1,v4,v2,v0] BT.lf) [5,2863180456,v3,v1,v4,v2,v0] BT.lf) [5,2863180456,v1,v4,4244438268,v2,v0] (BT.nd BT.lf [5,2863180456,v1,v4,v2,va,v0] BT.lf)) [5,2863180456,v1,v4,v2,4294770684,v0] (BT.nd (BT.nd BT.lf [5,2863180456,v1,v4,v2,v0] BT.lf) [5,v12,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,v12,v1,v4,v2,va,v0] BT.lf))) [5,v12,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v12,v1,v4,v2,v0,v13] BT.lf) [5,v3,v3,v1,v8,v2,v0] (BT.nd BT.lf [5,v3,v3,v1,v6,va,v0] BT.lf)) [5,v3,v3,v1,ve,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v3,v1,4039176384,v2,v0] BT.lf) [5,v3,v3,v1,v4,v2,v0] (BT.nd BT.lf [5,v3,2863311615,v1,v4,v2,v0] BT.lf)))) [5,v3,2863315899,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,2863329006,v1,v4,v2,v0] BT.lf) [5,v3,2863332090,v1,v4,v2,v0] (BT.nd BT.lf [5,v3,2863333375,v1,v4,v2,v0] BT.lf)) [5,v3,2868903935,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,2964369584,v1,v4,v2,v0] BT.lf) [5,v3,3014898611,v1,v4,v2,v0] (BT.nd BT.lf [5,v3,3132799674,v1,v4,v2,v0] BT.lf))) [5,v3,3149642683,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,3149660159,v1,v4,v2,v0] BT.lf) [5,v3,v1,3758153728,v8,v2,v0] (BT.nd BT.lf [5,v3,v1,3758153728,v4,v2,v0] BT.lf)) [5,v3,v1,v18,4004179626,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v18,v4,v2,v0] BT.lf) [5,v3,v1,v18,v2,v0] (BT.nd BT.lf [5,v3,v1,v8,v8,v2,v0] BT.lf))))) [5,v3,v1,v8,3941264106,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v8,v14,vc,v0] BT.lf) [5,v3,v1,v8,v14,v4,v0] (BT.nd BT.lf [5,v3,v1,v8,v14,v0] BT.lf)) [5,v3,v1,v8,vc,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v8,v6,v2,v0] BT.lf) [5,v3,v1,v8,v4,v2,v0] (BT.nd BT.lf [5,v3,v1,v8,vf,v2,v0] BT.lf))) [5,v3,v1,v8,4278124286,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v8,v16,v2,v0] BT.lf) [5,v3,v1,v8,v2,v2,v0] (BT.nd BT.lf [5,v3,v1,v8,v2,v1b,v0] BT.lf)) [5,v3,v1,v8,v2,4292935648,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v8,v2,4293853166,v0] BT.lf) [5,v3,v1,v8,v2,va,v0] (BT.nd BT.lf [5,v3,v1,v8,v2,v0] BT.lf)))) [5,v3,v1,v8,v2,v0,v11] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,3937069738,v4,v2,v0] BT.lf) [5,v3,v1,3938511552,v4,v2,v0] (BT.nd BT.lf [5,v3,v1,3941264106,v4,v2,v0] BT.lf)) [5,v3,v1,4007718624,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,4008373994,v4,v2,v0] BT.lf) [5,v3,v1,vc,v6,va,v0] (BT.nd BT.lf [5,v3,v1,vc,ve,v2,v0] BT.lf))) [5,v3,v1,vc,4041273568,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,vc,v4,v2,v0] BT.lf) [5,v3,v1,vc,v4,v2,4294906129] (BT.nd BT.lf [5,v3,v1,4008640511,v4,v2,v0] BT.lf)) [5,v3,v1,v10,v6,v4,v11] (BT.nd (BT.nd BT.lf [5,v3,v1,v10,v6,va,v0] BT.lf) [5,v3,v1,v10,v4,v2,v0] (BT.nd BT.lf [5,v3,v1,v10,v4,v2,4294963200] BT.lf))))))) [5,v3,v1,v10,v4,v2,v17] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v10,v4,v11] BT.lf) [5,v3,v1,4026572800,4042301600,v2,v0] BT.lf) [5,v3,v1,4026572800,v4,v2,v0] (BT.nd BT.lf [5,v3,v1,v6,v6,va,v0] BT.lf)) [5,v3,v1,v6,ve,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v6,v1c,v4,v11] BT.lf) [5,v3,v1,v6,v1c,v2,v17] (BT.nd BT.lf [5,v3,v1,v6,4042301600,v2,v0] BT.lf))) [5,v3,v1,v6,v4,4205445120,v2] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v6,v4,4210096880,v0] BT.lf) [5,v3,v1,v6,v4,4210688000,v2] (BT.nd BT.lf [5,v3,v1,v6,v4,v2,v0] BT.lf)) [5,v3,v1,v6,v4,4281597747,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v6,v4,4288741280,v0] BT.lf) [5,v3,v1,v6,v4,4289396480,v0] (BT.nd BT.lf [5,v3,v1,v6,v4,4293984000,v0] BT.lf)))) [5,v3,v1,v6,v4,va,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v6,v4,v0,4294945280] BT.lf) [5,v3,v1,v6,v4,v0,v11] (BT.nd BT.lf [5,v3,v1,v6,v4,v0,v13] BT.lf)) [5,v3,v1,v6,4205509290,va,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v6,4210096880,v0] BT.lf) [5,v3,v1,v6,vf,va,v0] (BT.nd BT.lf [5,v3,v1,v6,4293918720,va,v0] BT.lf))) [5,v3,v1,v6,va,va,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v6,va,4294639610,v0] BT.lf) [5,v3,v1,v6,va,v0] (BT.nd BT.lf [5,v3,v1,v6,va,v0,v0] BT.lf)) [5,v3,v1,v6,va,v0,4294945450] (BT.nd (BT.nd BT.lf [5,v3,v1,v6,va,v0,4294963200] BT.lf) [5,v3,v1,v6,va,v0,v17] (BT.nd BT.lf [5,v3,v1,v6,va,v0,v13] BT.lf))))) [5,v3,v1,v6,v0,v17,v11] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v6,v0,v17,v13] BT.lf) [5,v3,v1,v6,v0,v13] BT.lf) [5,v3,v1,4026593520,v4,v2,v0] (BT.nd BT.lf [5,v3,v1,4026593520,v2,4278255615,v0] BT.lf)) [5,v3,v1,4026593520,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,4026597375,v4,v2,v0] BT.lf) [5,v3,v1,4029739056,v4,v2,v0] (BT.nd BT.lf [5,v3,v1,v1d,v4,v2,v0] BT.lf))) [5,v3,v1,v1d,v2,4287168392,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v1d,v2,v0] BT.lf) [5,v3,v1,4037058720,v4,v2,v0] (BT.nd BT.lf [5,v3,v1,4037058720,v2,4289374890,v0] BT.lf)) [5,v3,v1,4037058720,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,4037079040,v4,v2,v0] BT.lf) [5,v3,v1,ve,ve,v2,v0] (BT.nd BT.lf [5,v3,v1,ve,v4,v2,4289331200] BT.lf)))) [5,v3,v1,ve,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,ve,4205509290,v2,v0] BT.lf) [5,v3,v1,ve,vf,v2,v0] (BT.nd BT.lf [5,v3,v1,ve,4243389676,v2,v0] BT.lf)) [5,v3,v1,ve,4244438268,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,ve,v2,v2,v0] BT.lf) [5,v3,v1,ve,v2,4288741280,v0] (BT.nd BT.lf [5,v3,v1,ve,v2,4289331200] BT.lf))) [5,v3,v1,ve,v2,4289331200,v1b] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,ve,v2,v1b,v0] BT.lf) [5,v3,v1,ve,v2,4291624908,v0] (BT.nd BT.lf [5,v3,v1,ve,v2,4293853166,v0] BT.lf)) [5,v3,v1,ve,v2,va,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,ve,v2,4294639610,v0] BT.lf) [5,v3,v1,ve,v2,v0] (BT.nd BT.lf [5,v3,v1,ve,v2,v0,v0] BT.lf)))))) [5,v3,v1,ve,v2,v0,4294945450] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,ve,v2,v0,4294954188] BT.lf) [5,v3,v1,ve,v2,v0,4294963360] BT.lf) [5,v3,v1,ve,v2,v0,v17] (BT.nd BT.lf [5,v3,v1,ve,v2,v0,v11] BT.lf)) [5,v3,v1,ve,v2,v0,4294967210] (BT.nd (BT.nd BT.lf [5,v3,v1,4041273568,v4,v2,v0] BT.lf) [5,v3,v1,4041273568,v2,v1b,v0] (BT.nd BT.lf [5,v3,v1,4041273568,v2,4293853166,v0] BT.lf))) [5,v3,v1,4041273568,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,4042321920,v4,v2,v0] BT.lf) [5,v3,v1,4042321920,v2,va,v0] (BT.nd BT.lf [5,v3,v1,4042321920,v2,v0,v13] BT.lf)) [5,v3,v1,4042322080,v4,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,4042322080,v2,v1b,v0] BT.lf) [5,v3,v1,4042322080,v2,v0] (BT.nd BT.lf [5,v3,v1,4042322080,v2,v0,v11] BT.lf)))) [5,v3,v1,4042322080,v2,v0,4294967210] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,v4,v2,v0] BT.lf) [5,v3,v1,v4,4042322175,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4042322931,v2,v0] BT.lf)) [5,v3,v1,v4,4042324730,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v4,4042326000,v2,v0] BT.lf) [5,v3,v1,v4,4042326015,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4043309055,v2,v0] BT.lf))) [5,v3,v1,v4,4059165169,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,4076008178,v2,v0] BT.lf) [5,v3,v1,v4,4080268083,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4092654576,v2,v0] BT.lf)) [5,v3,v1,v4,4092851187,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v4,4092854271,v2,v0] BT.lf) [5,v3,v1,v4,4160223223,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4169726088,v2,v0] BT.lf))))) [5,v3,v1,v4,4176541936,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,4177066232,v2,v0] BT.lf) [5,v3,v1,v4,4205488810,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4205506560,v2,v0] BT.lf)) [5,v3,v1,v4,4205509290,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v4,4207475400,v2,v0] BT.lf) [5,v3,v1,v4,4209703658,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4210094320,v2,v0] BT.lf))) [5,v3,v1,v4,4210096880,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,4210621176,v2,v0] BT.lf) [5,v3,v1,v4,4210752000,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4210752170,v2,v0] BT.lf)) [5,v3,v1,v4,4210752240,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v4,vf,v2,v0] BT.lf) [5,v3,v1,v4,vf,v2,4294903045] (BT.nd BT.lf [5,v3,v1,v4,4210753535,v2,v0] BT.lf)))) [5,v3,v1,v4,4227595259,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,4277075694,v2,v0] BT.lf) [5,v3,v1,v4,4277206768,v2,v0] (BT.nd BT.lf [5,v3,v1,v4,4277862138,v2,v0] BT.lf)) [5,v3,v1,v4,4278124286,v2,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v4,v2,4293980400,v0] BT.lf) [5,v3,v1,v4,v2,4293982960,v0] (BT.nd BT.lf [5,v3,v1,v4,v2,va,v0] BT.lf))) [5,v3,v1,v4,v2,4293984255,v0] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,v2,4294180851,v0] BT.lf) [5,v3,v1,v4,v2,4294508536,v0] (BT.nd BT.lf [5,v3,v1,v4,v2,4294638330,v0] BT.lf)) [5,v3,v1,v4,v2,4294639600,v0] (BT.nd (BT.nd BT.lf [5,v3,v1,v4,v2,4294639610,v0] BT.lf) [5,v3,v1,v4,v2,4294901758,v0] (BT.nd BT.lf [5,v3,v1,v4,v2,v0] BT.lf)))))))) [5,v3,v1,v4,v2,v0,v13] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,v2,v0,4294967290] BT.lf) [5,v3,v1,v4,v2,v0,4294967295] BT.lf) [5,v3,v1,v4,v2,4294901811] (BT.nd BT.lf [5,v3,v1,v4,v2,4294902000] BT.lf)) [5,v3,v1,v4,v2,4294902015,v17] (BT.nd (BT.nd BT.lf [5,v3,v1,v4,v2,4294902015,v11] BT.lf) [5,v3,v1,v4,v2,4294906129] (BT.nd BT.lf [5,v3,v1,v4,v2,4294914867,4294954188] BT.lf))) [5,v3,v1,v4,v2,4294934656] (BT.nd (BT.nd (BT.nd BT.lf [5,v3,v1,v4,v2,4294936712,v17] BT.lf) [5,v3,v1,v4,v2,4294942880,4294954188] (BT.nd BT.lf [5,v3,3435978205,v4,v2,v0] BT.lf)) [5,v3,3435978205,v4,v2,v0,4294945450] (BT.nd (BT.nd BT.lf [5,v3,3435986943,v4,v2,v0,4294954188] BT.lf) [5,v3,3722304989,vc,v4,v2,v0] (BT.nd BT.lf [6,0,v9,v3,v1,v4,v2] BT.lf)))) [6,0,v9,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,vb,v3,v1,v4,v2,v0] BT.lf) [6,0,vb,v3,v4,v2,v0] (BT.nd BT.lf [6,0,v3,v1,v4,v2,v0] BT.lf)) [6,255,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,255,v3,v1,v4,v2,v0,v11] BT.lf) [6,13107,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,13107,v3,v1,v4,v2,v0,4294954188] BT.lf))) [6,43690,v9,v3,v1,v4,v2] (BT.nd (BT.nd (BT.nd BT.lf [6,43690,v9,v3,v1,v4,v2,v0] BT.lf) [6,43690,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,61680,v9,v3,v1,v4,v2] BT.lf)) [6,61680,v9,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,61680,v3,v1,v4,v2,v0] BT.lf) [6,v9,v9,v3,v1,v4,v2] (BT.nd BT.lf [6,v9,v9,v3,v1,v4,v2,v0] BT.lf))))) [6,v9,16711935,v3,v1,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v9,16711935,v3,v1,v4,v2] BT.lf) [6,v9,16711935,v3,v1,v4,v2,v0] BT.lf) [6,v9,vb,v3,v1,v4,v2] (BT.nd BT.lf [6,v9,vb,v3,v1,v4,v2,v0] BT.lf)) [6,v9,vb,v3,v4,v2] (BT.nd (BT.nd BT.lf [6,v9,vb,v3,v4,v2,v0] BT.lf) [6,v9,v5,v3,v1,v4,v2] (BT.nd BT.lf [6,v9,v5,v3,v1,v4,v2,v0] BT.lf))) [6,v9,v7,v3,v1,v4,v2] (BT.nd (BT.nd (BT.nd BT.lf [6,v9,v7,v3,v1,v4,v2,v0] BT.lf) [6,v9,2863267840,v3,v1,v4,v2] (BT.nd BT.lf [6,v9,2863267840,v3,v1,v4,v2,v0] BT.lf)) [6,v9,v3,v3,v1,v4,v2] (BT.nd (BT.nd BT.lf [6,v9,v3,v3,v1,v4,v2,v0] BT.lf) [6,v9,v3,2863333375,v1,v4,v2] (BT.nd BT.lf [6,v9,v3,2863333375,v1,v4,v2,v0] BT.lf)))) [6,v9,v3,v1,vc,v4,v2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v9,v3,v1,vc,v4,v2,v0] BT.lf) [6,v9,v3,v1,v6,v4,v2] (BT.nd BT.lf [6,v9,v3,v1,v6,v4,v2,v0] BT.lf)) [6,v9,v3,v1,v1c,v4,v2] (BT.nd (BT.nd BT.lf [6,v9,v3,v1,v1c,v4,v2,v0] BT.lf) [6,v9,v3,v1,v4,v4,v2] (BT.nd BT.lf [6,v9,v3,v1,v4,v4,v2,v0] BT.lf))) [6,v9,v3,v1,v4,4042326015,v2] (BT.nd (BT.nd (BT.nd BT.lf [6,v9,v3,v1,v4,4042326015,v2,v0] BT.lf) [6,v9,v3,v1,v4,vf,v2] (BT.nd BT.lf [6,v9,v3,v1,v4,vf,v2,v0] BT.lf)) [6,v9,v3,v1,v4,v2] (BT.nd (BT.nd BT.lf [6,v9,v3,v1,v4,v2,va] BT.lf) [6,v9,v3,v1,v4,v2,va,v0] (BT.nd BT.lf [6,v9,v3,v1,v4,v2,v0] BT.lf)))))) [6,v9,v3,v1,v4,v2,v0,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v9,v3,v1,v4,v2,v0,4294945450] BT.lf) [6,v9,v3,v1,v4,v2,v0,v17] BT.lf) [6,v9,v3,v1,v4,v2,v0,4294967295] (BT.nd BT.lf [6,v9,v3,v1,v4,v2,4294945450] BT.lf)) [6,v9,v3,v1,v4,v2,v17] (BT.nd (BT.nd BT.lf [6,v9,v3,v1,v4,v2,4294967295] BT.lf) [6,16777215,v3,v1,v4,v16,v2,v0] (BT.nd BT.lf [6,16777215,v3,v1,v4,v2,v0] BT.lf))) [6,286331153,v3,v1,vc,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,286331153,v3,v1,v4,v2,v0] BT.lf) [6,572662306,vb,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,572662306,vb,v3,v4,v2,v0] BT.lf)) [6,572662306,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,808464432,vb,v3,v1,v4,v2,v0] BT.lf) [6,808464432,vb,v3,v4,v2,v0] (BT.nd BT.lf [6,808464432,v3,v1,v4,v2,v0] BT.lf)))) [6,vb,vb,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,vb,vb,v3,v4,v2,v0] BT.lf) [6,vb,1431655765,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,vb,1431655765,v3,v4,v2,v0] BT.lf)) [6,vb,1431655765,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,vb,v5,v3,v1,v4,v2,v0] BT.lf) [6,vb,v5,v3,v4,v2,v0] (BT.nd BT.lf [6,vb,v7,v3,v1,v4,v2,v0] BT.lf))) [6,vb,v7,v3,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,vb,v3,v3,v1,v4,v2,v0] BT.lf) [6,vb,v3,v3,v4,v2,v0] (BT.nd BT.lf [6,vb,v3,3149642683,v1,v4,v2,v0] BT.lf)) [6,vb,v3,3149642683,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,vb,v3,v1a,v1,v4,v2,v0] BT.lf) [6,vb,v3,v1a,v4,v2,v0] (BT.nd BT.lf [6,vb,v3,v1,v1,v4,v2,v0] BT.lf))))) [6,vb,v3,v1,vc,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,vb,v3,v1,v6,v4,v2,v0] BT.lf) [6,vb,v3,v1,v4,v4,v2,v0] (BT.nd BT.lf [6,vb,v3,v1,v4,4092851187,v2,v0] BT.lf)) [6,vb,v3,v1,v4,vf,v2,v0] (BT.nd (BT.nd BT.lf [6,vb,v3,v1,v4,4244438268,v2,v0] BT.lf) [6,vb,v3,v1,v4,v2,va,v0] (BT.nd BT.lf [6,vb,v3,v1,v4,v2,v0] BT.lf))) [6,vb,v3,v1,v4,v2,v0,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [6,vb,v3,vc,v4,v2,v0] BT.lf) [6,vb,v3,v6,v4,v2,v0] (BT.nd BT.lf [6,vb,v3,v4,v4,v2,v0] BT.lf)) [6,vb,v3,v4,4092851187,v2,v0] (BT.nd (BT.nd BT.lf [6,vb,v3,v4,vf,v2,v0] BT.lf) [6,vb,v3,v4,4244438268,v2,v0] (BT.nd BT.lf [6,vb,v3,v4,v2,va,v0] BT.lf)))) [6,vb,v3,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,vb,v3,v4,v2,v0,4294967295] BT.lf) [6,859045887,v3,3435921408,v1,v4,v2,v0] (BT.nd BT.lf [6,859045887,v3,v1,v4,v2,v0] BT.lf)) [6,2004318071,v5,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,2004318071,v3,v1,v4,v2,v0] BT.lf) [6,2155905152,v5,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,2155905152,v7,v3,v1,v4,v2,v0] BT.lf))) [6,2155905152,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,v5,v5,v3,v1,v4,v2,v0] BT.lf) [6,v5,v7,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,v5,v7,v1,v4,v2,v0] BT.lf)) [6,v5,v3,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,v5,v3,v1,vc,v4,v2,v0] BT.lf) [6,v5,v3,v1,v6,v4,v2,v0] (BT.nd BT.lf [6,v5,v3,v1,v4,v4,v2,v0] BT.lf))))))) [6,v5,v3,v1,v4,4177066232,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v5,v3,v1,v4,vf,v2,v0] BT.lf) [6,v5,v3,v1,v4,v2,va,v0] BT.lf) [6,v5,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,v5,v3,vc,v4,v2,v0] BT.lf)) [6,v5,vc,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,2684395520,v7,v3,v1,v4,v2,v0] BT.lf) [6,2684395520,v3,v1,v6,v4,v2,v0] (BT.nd BT.lf [6,2684395520,v3,v1,v4,v2,v0] BT.lf))) [6,v7,v7,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,v7,2852170240,v3,v1,v4,v2,v0] BT.lf) [6,v7,v3,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,v7,v3,v1a,v1,v4,v2,v0] BT.lf)) [6,v7,v3,v1a,v1,v2,v0] (BT.nd (BT.nd BT.lf [6,v7,v3,3422604288,v1,v4,v2,v0] BT.lf) [6,v7,v3,v1,v1,v4,v2,v0] (BT.nd BT.lf [6,v7,v3,v1,3974950124,v4,v2,v0] BT.lf)))) [6,v7,v3,v1,vc,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v7,v3,v1,v6,v4,v2,v0] BT.lf) [6,v7,v3,v1,v6,v2,v0] (BT.nd BT.lf [6,v7,v3,v1,v4,v4,v2,v0] BT.lf)) [6,v7,v3,v1,v4,vf,v2,v0] (BT.nd (BT.nd BT.lf [6,v7,v3,v1,v4,4244438268,v2,v0] BT.lf) [6,v7,v3,v1,v4,v16,v2,v0] (BT.nd BT.lf [6,v7,v3,v1,v4,v2,v2,v0] BT.lf))) [6,v7,v3,v1,v4,v2,4288741280,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,v7,v3,v1,v4,v2,v1b,v0] BT.lf) [6,v7,v3,v1,v4,v2,4291624908,v0] (BT.nd BT.lf [6,v7,v3,v1,v4,v2,va,v0] BT.lf)) [6,v7,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,v7,v3,v1,v4,v2,v0,v11] BT.lf) [6,v7,v3,v1,vf,v2,v0] (BT.nd BT.lf [6,v7,v1,v4,vf,v2,v0] BT.lf))))) [6,vd,v3,v1,v4,4244438268,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,vd,v3,v1,v4,v2,v0] BT.lf) [6,vd,v1,v4,4244438268,v2,v0] (BT.nd BT.lf [6,vd,v1,v4,v2,v0] BT.lf)) [6,v15,v3,v1,v4,v2,va,v0] (BT.nd (BT.nd BT.lf [6,v15,v3,v1,v4,v2,v0] BT.lf) [6,v3,v3,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,v3,v3,v1,v1,v4,v2,v0] BT.lf))) [6,v3,v3,v1,vc,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v3,v1,v6,v4,v2,v0] BT.lf) [6,v3,v3,v1,v4,v4,v2,v0] (BT.nd BT.lf [6,v3,v3,v1,v4,vf,v2,v0] BT.lf)) [6,v3,v3,v1,v4,4244438268,v2,v0] (BT.nd (BT.nd BT.lf [6,v3,v3,v1,v4,v2,va,v0] BT.lf) [6,v3,v3,v1,v4,v2,v0] (BT.nd BT.lf [6,v3,2863333375,v1,v4,v2,v0] BT.lf)))) [6,v3,3149642683,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,v8,vc,v4,v2,v0] BT.lf) [6,v3,v1,v8,vc,v2,v0] (BT.nd BT.lf [6,v3,v1,v8,v4,v2,v0] BT.lf)) [6,v3,v1,v8,v2,v0] (BT.nd (BT.nd BT.lf [6,v3,v1,3941264106,v4,v2,v0] BT.lf) [6,v3,v1,vc,vc,v4,v2,v0] (BT.nd BT.lf [6,v3,v1,vc,v6,v4,v2,v0] BT.lf))) [6,v3,v1,vc,v4,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,vc,v4,vf,v2,v0] BT.lf) [6,v3,v1,vc,v4,4278124286,v2,v0] (BT.nd BT.lf [6,v3,v1,vc,v4,v2,va,v0] BT.lf)) [6,v3,v1,vc,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,v3,v1,v10,v6,v4,v2,v0] BT.lf) [6,v3,v1,v10,v4,v2,v0] (BT.nd BT.lf [6,v3,v1,v6,v6,v4,v2,v0] BT.lf)))))) [6,v3,v1,v6,v1c,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,v6,v4,v4,v2,v0] BT.lf) [6,v3,v1,v6,v4,4205509290,v2,v0] BT.lf) [6,v3,v1,v6,v4,vf,v2,v0] (BT.nd BT.lf [6,v3,v1,v6,v4,v2,va,v0] BT.lf)) [6,v3,v1,v6,v4,v2,v0] (BT.nd (BT.nd BT.lf [6,v3,v1,v6,v4,v2,v0,v0] BT.lf) [6,v3,v1,v6,v4,v2,v0,4294945450] (BT.nd BT.lf [6,v3,v1,v6,v4,v2,v0,4294963200] BT.lf))) [6,v3,v1,v6,v4,v2,v0,v17] (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,v6,v4,va,v0] BT.lf) [6,v3,v1,v6,v4,v0,v11] (BT.nd BT.lf [6,v3,v1,v6,va,v0] BT.lf)) [6,v3,v1,ve,v4,v2,v1b,v0] (BT.nd (BT.nd BT.lf [6,v3,v1,ve,v4,v2,v0] BT.lf) [6,v3,v1,ve,v2,v1b,v0] (BT.nd BT.lf [6,v3,v1,ve,v2,v0] BT.lf)))) [6,v3,v1,4042321920,v4,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,4042321920,v4,v2,v0,v11] BT.lf) [6,v3,v1,v4,v4,v4,v2,v0] (BT.nd BT.lf [6,v3,v1,v4,v4,vf,v2,v0] BT.lf)) [6,v3,v1,v4,v4,v2,v2,v0] (BT.nd (BT.nd BT.lf [6,v3,v1,v4,v4,v2,v1b,v0] BT.lf) [6,v3,v1,v4,v4,v2,va,v0] (BT.nd BT.lf [6,v3,v1,v4,v4,v2,v0] BT.lf))) [6,v3,v1,v4,v4,v2,v0,v11] (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,v4,4042326015,v2,v0] BT.lf) [6,v3,v1,v4,4092851187,v2,v0] (BT.nd BT.lf [6,v3,v1,v4,4177066232,v2,v0] BT.lf)) [6,v3,v1,v4,4205509290,v2,v0] (BT.nd (BT.nd BT.lf [6,v3,v1,v4,4210096880,v2,v0] BT.lf) [6,v3,v1,v4,vf,vf,v2,v0] (BT.nd BT.lf [6,v3,v1,v4,vf,4244438268,v2,v0] BT.lf))))) [6,v3,v1,v4,vf,4278124286,v2,v0] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,v4,vf,v2,v1b,v0] BT.lf) [6,v3,v1,v4,vf,v2,4291624908,v0] (BT.nd BT.lf [6,v3,v1,v4,vf,v2,va,v0] BT.lf)) [6,v3,v1,v4,vf,v2,4294639610,v0] (BT.nd (BT.nd BT.lf [6,v3,v1,v4,vf,v2,v0] BT.lf) [6,v3,v1,v4,vf,v2,v0,v11] (BT.nd BT.lf [6,v3,v1,v4,4278124286,v2,v0] BT.lf))) [6,v3,v1,v4,v2,4293980400,v0] (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,v4,v2,va,va,v0] BT.lf) [6,v3,v1,v4,v2,va,4294639610,v0] (BT.nd BT.lf [6,v3,v1,v4,v2,va,v0] BT.lf)) [6,v3,v1,v4,v2,va,v0,v17] (BT.nd (BT.nd BT.lf [6,v3,v1,v4,v2,va,v0,v13] BT.lf) [6,v3,v1,v4,v2,4294639610,v0] (BT.nd BT.lf [6,v3,v1,v4,v2,v0] BT.lf)))) [6,v3,v1,v4,v2,v0,v13] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v3,v1,v4,v2,v0,4294967295] BT.lf) [7,v9,v3,v1,v4,v2] (BT.nd BT.lf [7,v9,v3,v1,v4,v2,v0] BT.lf)) [7,vb,v3,v1,v4,v2,v0] (BT.nd (BT.nd BT.lf [7,vb,v3,v4,v2,v0] BT.lf) [7,v5,v3,v1,v4,v2,v0] (BT.nd BT.lf [7,v7,v3,v1,v4,v2,v0] BT.lf))) [7,v3,v3,v1,v4,v2,v0] (BT.nd (BT.nd (BT.nd BT.lf [7,v3,v1,vc,v4,v2,v0] BT.lf) [7,v3,v1,v6,v4,v2,v0] (BT.nd BT.lf [7,v3,v1,v4,v4,v2,v0] BT.lf)) [7,v3,v1,v4,vf,v2,v0] (BT.nd (BT.nd BT.lf [7,v3,v1,v4,v2,va,v0] BT.lf) [7,v3,v1,v4,v2,v0] (BT.nd BT.lf [8,v3,v1,v4,v2,v0] BT.lf))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

def chunks : List (List (List Nat × List (Nat × Nat))) :=
  [K_0,K_1,K_2,K_3,K_4,K_5,K_6,K_7,K_8,K_9,K_10,K_11,K_12,K_13,K_14,K_15,K_16,K_17,K_18,K_19,K_20,K_21,K_22,K_23,K_24,K_25,K_26,K_27,K_28,K_29]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hAll_cert : chunks.flatten.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by
  rw [List.all_flatten, List.all_eq_true]
  intro k hk
  simp only [chunks, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c_0
  · exact c_1
  · exact c_2
  · exact c_3
  · exact c_4
  · exact c_5
  · exact c_6
  · exact c_7
  · exact c_8
  · exact c_9
  · exact c_10
  · exact c_11
  · exact c_12
  · exact c_13
  · exact c_14
  · exact c_15
  · exact c_16
  · exact c_17
  · exact c_18
  · exact c_19
  · exact c_20
  · exact c_21
  · exact c_22
  · exact c_23
  · exact c_24
  · exact c_25
  · exact c_26
  · exact c_27
  · exact c_28
  · exact c_29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = chunks.flatten.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, stepOK M_ Y_ PD_ PM_ G_ T_cert x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert chunks.flatten hK_cert hAll_cert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_idx : ∀ s : Nat, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 3901261952 (idx5 x)) s → 9 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

theorem lb : ∀ s : Nat, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 3901261952 (∑ i : Fin 5, if x i then 2 ^ i.val else 0)) s → 9 ≤ s := by
  intro s h
  simpa only [sum_eq] using lb_idx s (by simpa only [sum_eq] using h)

end RestrictionCertificate

namespace RestrictionCertificateUpper

def L_ : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

def M_ : Nat := 4294967295

def Y_ : Nat := 4277071592

def XS_ : List Nat := [2863311530,3435973836,4042322160,4278255360,4294901760]

def PD_ : List (Nat × Nat) := [(8,1048582),(1,26843548),(4,16777222),(2,22369618),(16,4102),(3,20132661),(14,70995),(15,70453),(6,18175315),(7,18035509),(17,4511),(20,262),(24,22)]

def PM_ : List (Nat × Nat) := [(12,4277071592),(2,4277071592),(24,4277071592),(1,4277071592),(20,4277071592)]

def G_ : List (List Nat) := [[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31],[0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31],[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31],[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31],[0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31],[0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31],[0,2,1,3,8,10,9,11,16,18,17,19,24,26,25,27,4,6,5,7,12,14,13,15,20,22,21,23,28,30,29,31],[0,2,1,3,16,18,17,19,4,6,5,7,20,22,21,23,8,10,9,11,24,26,25,27,12,14,13,15,28,30,29,31],[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31]]

abbrev v0 : Nat := 2863311530
abbrev v1 : Nat := 4042322160
abbrev v2 : Nat := 4278255360
abbrev v3 : Nat := 3435973836
abbrev v4 : Nat := 4294901760
abbrev v5 : Nat := 4008636142
abbrev v6 : Nat := 4026593280
abbrev v7 : Nat := 4293984240
abbrev v8 : Nat := 65535
abbrev v9 : Nat := 4294936712
abbrev va : Nat := 858993459
abbrev vb : Nat := 2290649224
abbrev vc : Nat := 2694881440
abbrev vd : Nat := 4294967040
abbrev ve : Nat := 3974950124
abbrev vf : Nat := 4210752250
abbrev v10 : Nat := 4294942880
abbrev v11 : Nat := 4294967280
abbrev v12 : Nat := 4294945450
abbrev v13 : Nat := 4287168392
abbrev v14 : Nat := 4294963440
abbrev v15 : Nat := 4241280204
abbrev v16 : Nat := 4177066232
abbrev v17 : Nat := 4288741280
abbrev v18 : Nat := 4026531840
abbrev v19 : Nat := 4294954188
abbrev v1a : Nat := 4244438268
abbrev v1b : Nat := 4041273568
abbrev v1c : Nat := 4289396650
abbrev v1d : Nat := 4037079200

def K_0 : List (List Nat × List (Nat × Nat)) := [([2,v0,v15,v11],[]),([2,v0,4241288396,v11],[]),([2,v0,4241292492,4294962912],[]),([2,v0,4243385580,v11],[]),([2,4205488810,v15,v11],[]),([3,1886417008,v5,v2,v9],[]),([3,v0,v3,v18,v11],[(72,5)]),([3,v0,v3,4026532080,vd],[]),([3,v0,v3,4026572800,v11],[(72,5)]),([3,v0,v3,v6,4294905840],[]),([3,v0,v3,v6,4294962912],[(72,5)]),([3,v0,v3,4026597360,v4],[]),([3,v0,v3,4037058720,v11],[(72,5)]),([3,v0,v3,4041269472,vd],[]),([3,v0,v3,v1b,4294962688],[]),([3,v0,v3,v1,4293848576],[]),([3,v0,v3,4205488810,v11],[(72,5)]),([3,v0,4007718624,4241292492,v4],[]),([3,v0,v18,v15,v11],[]),([3,v0,v6,v15,v11],[]),([3,v0,v1,v15,vd],[]),([3,v0,v1,v15,v11],[]),([3,v0,v1,4241288396,vd],[]),([3,v0,v1,4243385580,vd],[]),([3,v0,v1,4274834636,vd],[(104,2)]),([3,v0,v1,4274843340,vd],[(104,1)]),([3,v0,v15,4293980400,vd],[]),([3,v0,v15,v7,v14],[]),([3,v0,v15,v7,v11],[]),([3,v0,v15,v11],[]),([3,v0,4241292492,v7,4294954176],[]),([3,v0,4241292492,v19,v11],[]),([3,v0,4244438256,4291624908,v19],[]),([3,4008373994,4241292492,v7,v4],[]),([3,4008373994,v1a,4291624908,v4],[]),([3,4008636138,v1,v2,v19],[])]

def K_1 : List (List Nat × List (Nat × Nat)) := [([3,v5,v6,v7,v9],[]),([3,v5,v6,4294508536,v4],[]),([3,v5,4034982016,4294508536,v4],[]),([3,v5,v1b,v2,v9],[]),([3,v5,v1b,v13,v4],[]),([3,v5,v1,4270390920,v4],[]),([3,v5,v1,v2,4294901896],[]),([3,v5,v1,v2,v9],[]),([3,v5,v1,v2,4294944904],[]),([3,v5,v1,v2,4294944936],[]),([3,v5,v1,v2,4294945448],[]),([3,v5,v1,v2,4294961384],[]),([3,v5,v1,4286644096,v9],[]),([3,v5,v1,4287137928,vd],[]),([3,v5,v1,4287168256,v9],[]),([3,v5,v1,v13,v9],[]),([3,v5,v1,v13,v10],[]),([3,v5,v1,v13,4294945280],[]),([3,v5,v1,v13,4294945416],[]),([3,v5,v1,v13,4294959328],[]),([3,v5,v1,v13,4294962688],[]),([3,v5,v1,v13,4294962824],[]),([3,v5,v1,4289265576,4294944936],[]),([3,v5,v1,4289383560,vd],[]),([3,v5,v16,v13,v9],[]),([3,v1,4205488810,v15,vd],[]),([4,30583,v5,v1,v2],[]),([4,30583,v5,v1,v2,v9],[]),([4,34952,v5,v1,v2,v4],[(72,2),(96,0)]),([4,43690,4008627404,v1,v2,v4],[]),([4,61680,v0,v3,4026597120,v4],[]),([4,65520,v0,v3,v6,v4],[]),([4,v8,4008618666,v1,v2,v19],[]),([4,v8,v5,v1,v2,v9],[]),([4,v8,v5,v1,v13],[(2,0)]),([4,v8,v5,v1,v13,v4],[])]

def K_2 : List (List Nat × List (Nat × Nat)) := [([4,16776960,v0,v3,v1,4278190080],[(96,2)]),([4,178956970,v3,v1,v2,v4],[]),([4,269545712,v0,v3,v2,v4],[]),([4,286331153,v5,v1,v2,v9],[]),([4,286331153,v1,v2,v9],[]),([4,572662306,v3,v1,v2,v9],[]),([4,572662442,v3,v1,v2,v4],[]),([4,572697258,808513776,v3,v2,v4],[]),([4,572697258,v3,v1,v2,v4],[]),([4,572697258,v3,v1,4291624704,v4],[]),([4,581610154,v3,v1,v2,v4],[]),([4,805318656,v0,v3,v7,v4],[]),([4,808464432,v0,v3,v2,4294951104],[]),([4,808464432,v3,3941264106,v2,v4],[]),([4,808464624,v0,v3,v2,v4],[]),([4,808480880,v0,v3,v2,v4],[]),([4,808513776,855703296,v0,v3,v4],[]),([4,808513776,v0,v3,v2,v4],[]),([4,808513776,v0,v3,4291624704,v4],[]),([4,808513776,v3,4008618666,v2,v4],[]),([4,821096688,v0,v3,v2,v4],[]),([4,va,v5,v1,v2,v9],[]),([4,1717986918,vb,v1,v2,v4],[]),([4,1886417008,1996519168,v0,v3,v4],[]),([4,1886417008,vb,v5,v2,v4],[(56,2),(104,0)]),([4,1886417008,v0,v3,v2,v4],[]),([4,1886417008,v0,v3,v2,v9],[]),([4,1886449904,v0,v3,v2,v4],[]),([4,2004318071,v5,v1,v2,v9],[(100,1)]),([4,2155905152,v5,v1,v2,v9],[]),([4,2155905152,v5,v16,v2,v4],[(56,2),(72,2),(96,4),(128,2)]),([4,vb,v5,v6,v7,v4],[(72,3)]),([4,vb,v5,v1b,v2,v4],[(72,1)]),([4,vb,v5,v1,v2,v4],[(72,2),(96,0)]),([4,vb,v5,v1,v2,4294934656],[(72,2),(96,0)]),([4,vb,v5,v1,v2,v9],[(72,1)])]

def K_3 : List (List Nat × List (Nat × Nat)) := [([4,vb,v5,v1,v2,v10],[(72,1)]),([4,vb,v5,v1,v2,4294959328],[(72,1)]),([4,vb,v5,v1,v13,v9],[]),([4,2576980377,v5,v1,v2,v4],[]),([4,vc,v5,v1,v2,v9],[(96,0)]),([4,vc,v5,v16,v2,v4],[(56,2),(72,2),(96,3),(128,1)]),([4,2728569514,v3,v1,v2,v4],[]),([4,2827528328,v5,v1,v2,v4],[(72,2),(96,0)]),([4,2829625512,v5,v1,v2,v4],[(72,2),(96,0)]),([4,2829625512,v5,v1,v2,4294944936],[(72,1)]),([4,2829625512,v5,v16,v2,v4],[(56,2),(72,2),(96,3),(128,1)]),([4,2862656160,v3,4205509290,v7,v4],[(56,5),(128,5)]),([4,2862656160,v3,vf,v1c,v4],[(56,5),(128,9)]),([4,2863180456,v5,v1,v2,v4],[(72,2),(96,0)]),([4,2863311520,v3,v1,v2,v12],[(56,5)]),([4,2863311528,v3,v1,v2,v4],[]),([4,v0,2964386032,v3,v2,v4],[]),([4,v0,v3,3772834016,4261477888,v4],[(112,3),(144,1)]),([4,v0,v3,4007718624,v6,v4],[(96,5),(112,3)]),([4,v0,v3,v18,v6,v11],[(72,5)]),([4,v0,v3,v18,v1,vd],[(72,5)]),([4,v0,v3,v18,v1,v11],[(72,5)]),([4,v0,v3,v18,4293980400,vd],[(72,5)]),([4,v0,v3,v18,v7,v14],[(72,5)]),([4,v0,v3,v18,v7,v11],[(72,5)]),([4,v0,v3,v18,v11],[(72,5),(73,5),(82,5)]),([4,v0,v3,4026572800,v1,vd],[(72,5)]),([4,v0,v3,4026572800,v7,v4],[(72,9),(80,3)]),([4,v0,v3,v6,4042260480,v11],[]),([4,v0,v3,v6,v1,4294905600],[]),([4,v0,v3,v6,v1,4294962688],[]),([4,v0,v3,v6,4042326000,v4],[]),([4,v0,v3,v6,4277206768,v4],[]),([4,v0,v3,v6,4293918720,v11],[]),([4,v0,v3,v6,v7,v4],[]),([4,v0,v3,v6,v7,v9],[])]

def K_4 : List (List Nat × List (Nat × Nat)) := [([4,v0,v3,v6,v7,4294942720],[]),([4,v0,v3,v6,v7,v10],[]),([4,v0,v3,v6,v7,4294945440],[(72,5)]),([4,v0,v3,v6,4294508536,v4],[]),([4,v0,v3,v6,4294639600,v4],[]),([4,v0,v3,v6,v4,v11],[]),([4,v0,v3,v6,v12,v11],[(72,5)]),([4,v0,v3,4026593520,v2,v4],[]),([4,v0,v3,4026593520,4278255600,v4],[]),([4,v0,v3,4026593520,v7,v4],[]),([4,v0,v3,4026593520,v4,vd],[]),([4,v0,v3,4026597375,v7,v4],[]),([4,v0,v3,4027576335,v7,v4],[(148,3)]),([4,v0,v3,4029739248,v2,v4],[]),([4,v0,v3,4033933424,v2,v4],[]),([4,v0,v3,4034982016,v7,v4],[]),([4,v0,v3,4034982016,4294508536,v4],[]),([4,v0,v3,4037058720,v1,vd],[(72,5)]),([4,v0,v3,4037058720,v2,v14],[(72,7),(80,1)]),([4,v0,v3,4037079040,v7,v4],[]),([4,v0,v3,4037079040,4294639600,v4],[]),([4,v0,v3,v1d,v2,4294951104],[]),([4,v0,v3,v1d,4290838464,v4],[]),([4,v0,v3,v1d,v7,v4],[]),([4,v0,v3,v1d,v4,v11],[(116,0)]),([4,v0,v3,4037079280,v2,v4],[]),([4,v0,v3,4041269472,v2,v4],[]),([4,v0,v3,v1b,v2,4293787648],[]),([4,v0,v3,v1b,v2,v4],[]),([4,v0,v3,v1b,v17,v4],[]),([4,v0,v3,v1b,4292935648,v4],[]),([4,v0,v3,v1b,v7,v4],[]),([4,v0,v3,v1b,v4,vd],[]),([4,v0,v3,4042322144,v2,v4],[]),([4,v0,v3,v1,4205488810,vd],[(96,5)]),([4,v0,v3,v1,v2,v4],[])]

def K_5 : List (List Nat × List (Nat × Nat)) := [([4,v0,v3,v1,v2,4294901777],[]),([4,v0,v3,v1,v2,4294901808],[]),([4,v0,v3,v1,v2,4294901896],[]),([4,v0,v3,v1,v2,4294901920],[]),([4,v0,v3,v1,v2,4294902000],[]),([4,v0,v3,v1,v2,4294909984],[]),([4,v0,v3,v1,v2,4294934528],[]),([4,v0,v3,v1,v2,4294934656],[]),([4,v0,v3,v1,v2,4294936704],[]),([4,v0,v3,v1,v2,v9],[]),([4,v0,v3,v1,v2,4294942720],[]),([4,v0,v3,v1,v2,4294942848],[]),([4,v0,v3,v1,v2,v10],[]),([4,v0,v3,v1,v2,4294942960],[]),([4,v0,v3,v1,v2,4294944904],[]),([4,v0,v3,v1,v2,4294944928],[]),([4,v0,v3,v1,v2,4294944936],[]),([4,v0,v3,v1,v2,4294945440],[]),([4,v0,v3,v1,v2,4294945448],[]),([4,v0,v3,v1,v2,4294959104],[]),([4,v0,v3,v1,v2,4294959264],[]),([4,v0,v3,v1,v2,4294959328],[]),([4,v0,v3,v1,v2,4294961856],[]),([4,v0,v3,v1,v2,4294962912],[]),([4,v0,v3,v1,4279238400,4294905615],[(156,2)]),([4,v0,v3,v1,4279238400,v12],[]),([4,v0,v3,v1,4286644096,4294934656],[]),([4,v0,v3,v1,4286644096,v9],[]),([4,v0,v3,v1,4286644096,v10],[]),([4,v0,v3,v1,4287137928,vd],[]),([4,v0,v3,v1,4287168256,v9],[]),([4,v0,v3,v1,v13,v9],[]),([4,v0,v3,v1,v13,v10],[]),([4,v0,v3,v1,v13,4294945280],[]),([4,v0,v3,v1,v13,4294945416],[]),([4,v0,v3,v1,4288716960,vd],[])]

def K_6 : List (List Nat × List (Nat × Nat)) := [([4,v0,v3,v1,4288741120,v10],[]),([4,v0,v3,v1,v17,v10],[]),([4,v0,v3,v1,v17,4294945280],[]),([4,v0,v3,v1,v17,4294945440],[]),([4,v0,v3,v1,v17,4294951104],[]),([4,v0,v3,v1,v17,4294953984],[]),([4,v0,v3,v1,v17,4294954112],[]),([4,v0,v3,v1,4289265576,4294944936],[]),([4,v0,v3,v1,4289374720,vd],[]),([4,v0,v3,v1,4289374890,vd],[]),([4,v0,v3,v1,4289374890,v11],[(72,8)]),([4,v0,v3,v1,4289383560,vd],[]),([4,v0,v3,v1,4289392298,vd],[]),([4,v0,v3,v1,4289396480,4294945280],[]),([4,v0,v3,v1,4289396480,v12],[]),([4,v0,v3,v1,4289396480,4294953984],[]),([4,v0,v3,v1,4289396616,v12],[]),([4,v0,v3,v1,4289396640,v12],[(72,7)]),([4,v0,v3,v1,v1c,4294962688],[]),([4,v0,v3,v1,4292935648,4294959328],[]),([4,v0,v3,v1,4293848814,vd],[]),([4,v0,v3,v1,4293852928,4294962926],[(148,0)]),([4,v0,v3,v16,v13,v9],[]),([4,v0,v3,4210096880,v1c,4294945280],[]),([4,v0,3435982060,v1,v2,v4],[]),([4,v0,3972844748,v1,v2,v4],[]),([4,v0,3972852940,v6,v7,v4],[]),([4,v0,3972852940,v1,v2,v4],[]),([4,v0,3972852940,v1,v2,4294942720],[]),([4,v0,3972852940,v1,v2,v10],[]),([4,v0,3972852940,v1,v17,v4],[]),([4,v0,3974950092,v1,v2,v4],[]),([4,v0,ve,v6,v7,v4],[]),([4,v0,ve,4039176384,v2,v4],[]),([4,v0,ve,v1b,v2,v4],[]),([4,v0,ve,v1,4278190080,vd],[])]

def K_7 : List (List Nat × List (Nat × Nat)) := [([4,v0,ve,v1,v2,v4],[]),([4,v0,ve,v1,v2,4294934656],[]),([4,v0,ve,v1,v2,v9],[]),([4,v0,ve,v1,v2,4294942720],[]),([4,v0,ve,v1,v2,v10],[]),([4,v0,ve,v1,v2,4294944936],[]),([4,v0,ve,v1,v2,4294945280],[]),([4,v0,ve,v1,v2,4294951104],[]),([4,v0,ve,v1,v2,4294953984],[]),([4,v0,ve,v1,v2,4294959328],[]),([4,v0,ve,v1,v2,4294962176],[]),([4,v0,ve,v1,v17,v10],[]),([4,v0,ve,v16,v2,v4],[(56,2)]),([4,v0,ve,4210096880,v2,v4],[]),([4,v0,ve,vf,v2,v4],[]),([4,v0,ve,vf,v2,v10],[]),([4,v0,ve,4243651824,v2,v4],[]),([4,v0,4008504556,v1,v2,v4],[]),([4,v0,4008505068,v6,v7,v4],[(72,5)]),([4,v0,4008505068,v1,v2,v4],[]),([4,v0,4008505068,v1,v2,4294945440],[]),([4,v0,4008505068,v1,v17,v4],[]),([4,v0,4008505068,v1,v1c,v4],[(72,5)]),([4,v0,4008636140,v1,v2,v4],[(72,8),(96,6),(128,5)]),([4,v0,v5,v1,v2,v9],[]),([4,v0,v5,v1,v2,4294944936],[]),([4,v0,v5,v1,v2,4294953160],[(56,5)]),([4,v0,v5,v1,v13,v9],[]),([4,v0,v5,v1,4291611852,vd],[(140,2)]),([4,v0,v5,v1,4291624704,v19],[]),([4,v0,v5,v1,4291624908,4294962688],[]),([4,v0,v18,v1,v15,vd],[]),([4,v0,v6,v1,v15,vd],[]),([4,v0,v6,v15,v7,v4],[(104,3),(136,3)]),([4,v0,v1,v15,v2,v4],[(104,3),(136,1)]),([4,v0,v1,v15,v2,4294963200],[(104,3),(136,1)])]

def K_8 : List (List Nat × List (Nat × Nat)) := [([4,v0,v1,v15,v2,v14],[(136,1)]),([4,v0,v1,v15,vd],[(105,2)]),([4,v0,v1,4241288396,v2,v4],[(104,3),(136,1)]),([4,v0,v1,4241292492,v19,vd],[]),([4,v0,v1,4243385580,v2,v4],[(104,3),(136,1)]),([4,v0,v1,v1a,4291611852,vd],[(136,2)]),([4,3772834016,v5,v1,v2,v9],[(96,0)]),([4,3772834016,v5,v16,v2,v4],[(56,2),(72,2),(96,3),(128,1)]),([4,3907578088,v5,v1,v2,v4],[(72,2),(96,0)]),([4,3907578088,v5,v16,v2,v4],[(56,2),(72,2),(96,3),(128,1)]),([4,3941264106,ve,v1,v2,v4],[]),([4,3941264106,4006407884,v1,v2,v4],[]),([4,3941264106,v5,v1a,v2,v4],[]),([4,v5,v5,v1,v2,v9],[]),([4,v5,v6,v1,v2,v9],[]),([4,v5,v6,v1,v13,v4],[(80,0),(104,0)]),([4,v5,4034982016,v1,v13,v4],[(80,0),(104,0)]),([4,v5,v1,v1,v2,v9],[]),([4,v5,v1,4169726088,v2,v4],[(80,2),(104,3),(112,0)]),([4,v5,v1,v16,v2,v4],[(80,2)]),([4,v5,v1,v16,v2,v9],[(80,1)]),([4,v5,v1,4207475400,v2,v4],[(80,2),(104,3),(112,6)]),([4,v5,v1,4210621176,v2,v4],[(80,2)]),([4,v5,v1,vf,v2,v9],[]),([4,v5,v1,vf,v2,4294953160],[(84,5)]),([4,v5,v1,4278124286,v2,v9],[(116,1),(148,0)]),([4,v5,v1,v2,v7,v9],[]),([4,v5,v1,v2,4294508536,v4],[]),([4,v5,v1,v2,v9],[]),([4,v5,v1,v2,v9,v9],[]),([4,v5,v1,v2,v9,v12],[]),([4,v5,v1,v2,v9,4294962926],[(140,0),(148,2)]),([4,v5,v1,v2,v9,v14],[]),([4,v5,v1,v2,v9,4294965496],[(108,0)]),([4,v5,v1,v2,4294944936],[]),([4,v5,v1,v2,v12,v19],[])]

def K_9 : List (List Nat × List (Nat × Nat)) := [([4,v5,v1,v2,v12,4294966524],[]),([4,v5,v1,v13,v9],[]),([4,v5,v1,v1c,v19,vd],[]),([4,v1,4205488810,v15,v2,v4],[(96,3),(128,1)]),([5,0,v0,v3,v1,v2,v4],[]),([5,15,v0,v3,v1,v2,v4],[]),([5,51,v0,v3,v1,v2,v4],[]),([5,170,v0,v3,v1,v2,v4],[]),([5,240,v0,v3,v1,v2,v4],[(128,0)]),([5,255,v0,v3,v1,4278190080],[(2,2)]),([5,255,v0,v3,v1,4278190080,vd],[(128,2)]),([5,255,v0,v3,v1,v2,v4],[]),([5,4095,v0,v3,v1,v2,v4],[]),([5,4369,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,8738,v0,v3,v1,v2,v4],[]),([5,12336,v0,v3,v1,v2,v4],[(128,0)]),([5,13107,v0,v3,v1,v2,v4],[]),([5,13311,v0,v3,v1,v2],[(2,7)]),([5,13311,v0,v3,v1,v2,v4],[]),([5,13311,v0,v3,v1,v2,4294953984],[]),([5,30583,v0,v3,v1,v2],[]),([5,30583,v0,v3,v1,v2,v4],[]),([5,30583,v0,v3,v1,v2,v9],[]),([5,34952,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,41120,v0,v3,v1,v2,v4],[(128,0)]),([5,43690,2863267840,v3,v1,v2,v4],[]),([5,43690,v0,v3,v1,v2,v4],[]),([5,43690,2863333375,v3,v1,v2,v4],[]),([5,43690,v3,v5,v1,v2,v4],[]),([5,61166,v0,v3,v1,v2,v4],[]),([5,61440,v0,v3,v1,v2,v4],[]),([5,61680,v0,v3,v6,v2,v4],[(128,1)]),([5,61680,v0,v3,4042260480,v2,v4],[(128,3),(168,0)]),([5,61680,v0,v3,v1,v2,v4],[(128,0)]),([5,61680,v0,v3,v1,4278255600,v4],[(96,0),(128,0)]),([5,61680,v0,v3,4042326015,v2,v4],[(128,4)])]

def K_10 : List (List Nat × List (Nat × Nat)) := [([5,61680,v0,v3,vf,v2,v4],[(128,4)]),([5,64250,v0,v3,v1,v2,v4],[]),([5,65520,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,v8,16711935,252645135,v0,v3],[]),([5,v8,16711935,va,v0,v1],[]),([5,v8,16711935,v0,v3,v1],[]),([5,v8,va,1431655765,v1,v2],[]),([5,v8,va,v0,v1,v2],[]),([5,v8,vb,v5,v1,v2],[(104,1)]),([5,v8,vb,v5,v1,v2,v4],[(104,1)]),([5,v8,2863267840,v3,v1,v2,v12],[(80,5)]),([5,v8,v0,v3,v6,v7],[]),([5,v8,v0,v3,v6,v7,v4],[]),([5,v8,v0,v3,4026593520,v2],[]),([5,v8,v0,v3,4026593520,v2,v4],[(132,1)]),([5,v8,v0,v3,4042260480,v2,v14],[]),([5,v8,v0,v3,v1,v2],[]),([5,v8,v0,v3,v1,v2,v4],[]),([5,v8,v0,v3,v1,v2,v9],[]),([5,v8,v0,v3,v1,v2,v10],[]),([5,v8,v0,v3,v1,4278255600],[(2,0)]),([5,v8,v0,v3,v1,4278255600,v4],[(96,4)]),([5,v8,v0,v3,v1,v13],[(2,0)]),([5,v8,v0,v3,v1,v13,v4],[]),([5,v8,v0,v3,v1,v17],[(2,0)]),([5,v8,v0,v3,v1,v17,v4],[]),([5,v8,v0,v3,v1,4289396480],[(2,3)]),([5,v8,v0,v3,v1,4289396480,v4],[]),([5,v8,v0,ve,v1,v2],[]),([5,v8,v0,ve,v1,v2,v4],[]),([5,v8,v0,4008627404,v1,v2],[(2,3)]),([5,v8,v0,4008627404,v1,v2,v4],[(176,5)]),([5,1048575,v0,v3,v1,v2,v4],[]),([5,3355443,v0,v3,v1,v2,v4],[]),([5,3407871,v0,v3,v1,v2,v4],[]),([5,11184810,v0,v3,v1,v2,v4],[])]

def K_11 : List (List Nat × List (Nat × Nat)) := [([5,15790320,v0,v3,v1,v2,v4],[]),([5,16777215,v0,v3,v1,4278190080,vd],[]),([5,16777215,v0,v3,v1,v2,v4],[]),([5,16777215,v0,v3,v1,vd],[(2,2)]),([5,268435455,v0,v3,v1,v2,v4],[(76,5)]),([5,269488144,v0,v3,v1,v2,v4],[]),([5,286331153,vb,v5,v1,v2,v4],[(104,2),(136,0)]),([5,286331153,vb,v1,v2,v4],[(80,2),(104,0)]),([5,286331153,v0,v3,v1,v2,v4],[]),([5,286339891,v0,v3,v1,v2,v4],[]),([5,286339891,v0,4008627404,v1,v2,v4],[]),([5,286339891,v0,v1,v2,v4],[(2,3)]),([5,286392319,v0,v3,v1,v2,v4],[(132,1)]),([5,538976288,v0,v3,v1,v2,v4],[(128,0)]),([5,572662306,vb,v3,v1,v2,v4],[(104,2),(136,0)]),([5,572662306,v0,v3,v1,v2,v4],[]),([5,572662306,3149642683,v3,v1,v2,v4],[]),([5,572662306,v3,v1,vf,v2,v4],[]),([5,572697258,859045887,v3,v1,v2,v4],[(140,1)]),([5,572697258,v0,v3,v1,v2,v4],[]),([5,572697258,3435921408,v3,v1,v2,v4],[(56,9),(104,1)]),([5,572697258,v3,v1,v2,v4],[]),([5,805318656,v0,v3,v1,v2,v4],[]),([5,808464432,v0,3233857728,v3,v2,v4],[(144,0)]),([5,808464432,v0,v3,v1,v2,v4],[]),([5,808464432,v0,v3,4092851187,v2,v4],[]),([5,808464432,v0,v3,vf,v2,v4],[]),([5,808464432,v0,v3,v2,v7,v4],[]),([5,808513776,859045887,v0,v3,v2,v4],[]),([5,808513776,v0,3435921408,v3,v2,v4],[(72,10)]),([5,808513776,v0,v3,v1,v2,v4],[]),([5,808513776,v0,v3,v2,v4],[]),([5,842150450,v0,v3,v1,v2,v4],[]),([5,858796848,v0,v3,v1,v2,v4],[]),([5,va,1431655765,v1,v2,v4],[]),([5,va,vb,v5,v1,v2,v4],[(104,2),(136,0)])]

def K_12 : List (List Nat × List (Nat × Nat)) := [([5,va,v0,v3,v6,v7,v4],[]),([5,va,v0,v3,v1,v2,v4],[]),([5,va,v0,v3,v1,v2,v9],[]),([5,va,v0,v3,v1,v2,v10],[]),([5,va,v0,v3,v1,v2,4294951104],[]),([5,va,v0,ve,v1,v2,v4],[]),([5,va,v0,v6,v7,v4],[]),([5,va,v0,v1,v2,v4],[]),([5,va,v0,v1,v2,v9],[]),([5,va,v0,v1,v2,v10],[]),([5,va,v0,v1,v2,4294951104],[(2,5)]),([5,va,v3,3941264106,v1,v2,v4],[]),([5,va,3941264106,v1,v2,v4],[(2,5)]),([5,858993663,v0,v3,v1,v2,v4],[]),([5,859010935,v0,v3,v1,v2,v4],[(132,1)]),([5,859045887,v0,v3,v1,v2,v4],[(132,1)]),([5,859045887,v0,v3,v1,4291624704,v4],[(132,1),(172,3)]),([5,859045887,v3,4008618666,v1,v2,v4],[(60,5),(132,1),(172,3)]),([5,872415231,v0,v3,v1,v2,v4],[(132,1),(172,3)]),([5,1886417008,2004318071,v0,v3,v2,v4],[(180,0)]),([5,1886417008,vb,v0,v3,v2,v4],[(56,2),(136,0)]),([5,1886417008,v0,v3,v1,v2,v4],[]),([5,1886417008,v0,v3,v2,v4],[]),([5,2004318071,vb,v5,v1,v2,v4],[(104,2),(132,1),(136,0),(172,3)]),([5,2004318071,v0,v3,v1,v2,v4],[(132,1),(172,3)]),([5,2004318071,v0,v3,v1,v2,v9],[(76,5),(132,1),(172,3)]),([5,2004318071,v5,v1,v2,v4],[]),([5,2004353023,v0,v3,v1,v2,v4],[(76,5),(132,1),(172,3)]),([5,2147516416,v0,v3,v1,v2,v4],[]),([5,2155905152,vb,v5,v1,v2,v4],[(128,0),(136,0)]),([5,2155905152,v0,v3,v1,v2,v4],[(128,0)]),([5,2155905152,v0,v3,v1,v2,4294934656],[]),([5,2155905152,v0,v3,v1,v2,v9],[]),([5,2155905152,v0,v3,v1,v2,v10],[]),([5,2155905152,v0,v3,v16,v2,v4],[(56,2),(72,2),(96,2),(128,4),(168,2)]),([5,2155905152,v0,ve,v1,v2,v4],[(128,0)])]

def K_13 : List (List Nat × List (Nat × Nat)) := [([5,2290124928,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,vb,vb,v5,v1,v2,v4],[(96,2),(128,0)]),([5,vb,vc,v5,v1,v2,v4],[(128,0),(136,0)]),([5,vb,v0,v3,v6,v7,v4],[(96,3)]),([5,vb,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,vb,v0,v3,v1,v2,4294934656],[(96,2),(128,0)]),([5,vb,v0,v3,v1,v2,v9],[(96,1)]),([5,vb,v0,v3,v1,v2,v10],[(96,1)]),([5,vb,v0,v3,v1,v13,v9],[]),([5,vb,v0,ve,v1,v2,v4],[(128,0)]),([5,vb,v0,v5,v1,v2,v4],[(96,2),(128,0)]),([5,vb,v0,v5,v1,v2,v9],[(96,1)]),([5,vb,3772834016,v5,v1,v2,v4],[(128,0),(136,0)]),([5,vb,v5,v5,v1,v2,v4],[(96,2),(128,0)]),([5,vb,v5,v6,v1,v2,v4],[(96,1)]),([5,vb,v5,v1,v1,v2,v4],[(128,0)]),([5,vb,v5,v1,v16,v2,v4],[(72,2),(112,2),(128,0)]),([5,vb,v5,v1,vf,v2,v4],[(72,2),(128,0)]),([5,vb,v5,v1,4278124286,v2,v4],[(72,2),(128,0),(156,1),(196,3)]),([5,vb,v5,v1,v2,v7,v4],[(72,2),(96,0)]),([5,vb,v5,v1,v2,v4],[(72,2),(74,2),(96,0),(97,1),(98,0),(129,3)]),([5,vb,v5,v1,v2,v9],[(72,1),(74,1),(97,1),(101,1)]),([5,2290657962,v0,v3,v1,v2,v4],[]),([5,2290679807,v0,v3,v1,v2],[(2,3)]),([5,2290679807,v0,v3,v1,v2,v4],[]),([5,2684354560,v0,v3,v1,v2,v4],[]),([5,2684395520,v0,v3,v6,v7,v4],[]),([5,2684395520,v0,v3,v1,v2,v4],[]),([5,2684395520,v0,v3,v1,v2,4294942720],[]),([5,2684395520,v0,v3,v1,v2,v10],[]),([5,2684395520,v0,v3,v1,v17,v4],[(56,0),(96,0),(128,0),(168,0)]),([5,2684395520,v0,3972852940,v1,v2,v4],[]),([5,2684395520,v0,ve,v1,v2,v4],[]),([5,2692784256,v0,v3,v1,v2,v4],[(128,0)]),([5,2694881280,v0,v3,v1,v2,v4],[(128,0)]),([5,vc,v0,v3,v6,v7,v4],[])]

def K_14 : List (List Nat × List (Nat × Nat)) := [([5,vc,v0,v3,4039176384,v2,v4],[(128,5),(168,5)]),([5,vc,v0,v3,v1,4278190080,vd],[(56,2),(96,2),(168,2)]),([5,vc,v0,v3,v1,v2,v4],[(128,0)]),([5,vc,v0,v3,v1,v2,4294934656],[(128,0)]),([5,vc,v0,v3,v1,v2,v9],[(128,0)]),([5,vc,v0,v3,v1,v2,4294942720],[(128,0)]),([5,vc,v0,v3,v1,v2,v10],[]),([5,vc,v0,v3,v1,v2,4294945280],[(56,1),(96,1)]),([5,vc,v0,v3,v1,v2,4294951104],[(56,5),(96,5)]),([5,vc,v0,v3,v1,v2,4294953984],[(56,7),(96,7),(168,1)]),([5,vc,v0,v3,v1,v17,v10],[]),([5,vc,v0,v3,v16,v2,v4],[(56,2),(96,2),(128,3),(168,1)]),([5,vc,v0,v3,4210096880,v2,v4],[(56,2),(96,2),(128,3),(168,1)]),([5,vc,v0,v3,vf,v2,v4],[(128,4),(168,2)]),([5,vc,v0,v3,vf,v2,v10],[(56,2),(96,2),(128,1),(168,2)]),([5,vc,v0,v3,4243651824,v2,v4],[(56,8),(96,8),(128,4),(168,7)]),([5,vc,v0,3972852940,v1,v2,v4],[]),([5,vc,v0,ve,v1,v2,v4],[(128,0)]),([5,vc,v0,ve,v1,v2,v10],[]),([5,vc,v0,ve,vf,v2,v4],[(128,0)]),([5,vc,v0,4006407884,v1,v2,v4],[(56,1),(96,1),(128,1),(168,1)]),([5,vc,v3,3941264106,v1,v2,v4],[(72,5),(96,5),(128,6),(168,5)]),([5,vc,v3,4004179626,v1,v2,v4],[(56,1),(72,7),(96,7),(128,7),(168,7)]),([5,vc,v3,v5,vf,v2,v4],[(56,5),(128,10),(168,8)]),([5,2694884010,v0,v3,v1,v2,v4],[]),([5,2694902000,v0,v3,v1,v2,v4],[(128,0)]),([5,2694905855,v0,v3,v1,v2],[(2,10)]),([5,2694905855,v0,v3,v1,v2,v4],[]),([5,2728567458,v0,v3,v1,v2,v4],[]),([5,2827528328,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,2829101216,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,2829101216,v0,v3,4243651824,v2,v4],[(56,8),(96,8),(128,4),(168,7)]),([5,2829625512,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,2829625512,v0,v3,v1,v2,4294944936],[(96,1)]),([5,2829625512,v0,v3,v16,v2,v4],[(56,2),(96,2),(128,3),(168,1)]),([5,2829625512,v0,v3,vf,v2,v4],[(128,4),(168,2)])]

def K_15 : List (List Nat × List (Nat × Nat)) := [([5,2829625512,v0,ve,v1,v2,v4],[(128,0)]),([5,2829625512,v0,v5,v1,v2,v4],[(96,2),(128,0)]),([5,2829625512,v3,v5,v1,v2,v4],[(96,8),(128,6),(168,5)]),([5,2829625512,v5,v1,v1a,v2,v4],[(72,8),(128,6),(168,5)]),([5,2829625512,v5,v1,v2,v4],[(72,2),(96,0),(97,1),(98,0),(129,3)]),([5,2862653600,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,2862656160,v0,v3,v6,v7,v4],[(96,3)]),([5,2862656160,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,2862656160,v0,v3,v1,v2,4294945440],[(96,1)]),([5,2862656160,v0,v3,v1,v17,v4],[(56,0),(96,3),(128,0)]),([5,2862656160,v0,v3,v1,v1c,v4],[(96,3),(168,0)]),([5,2862656160,v0,4008505068,v1,v2,v4],[(96,1)]),([5,2863180456,v0,v3,v1,v2,v4],[(96,2),(128,0)]),([5,2863311520,v0,v3,v1,v2,v4],[(96,2),(104,2),(128,0),(136,0)]),([5,v0,v0,v3,v6,v7,v4],[(96,3)]),([5,v0,v0,v3,v1,v2,v4],[]),([5,v0,v0,v3,v1,v2,v9],[]),([5,v0,v0,v3,v1,v2,v10],[(96,2)]),([5,v0,v0,v3,v1,v2,4294951104],[(48,5),(52,5)]),([5,v0,v0,ve,v1,v2,v4],[]),([5,v0,2863311615,v3,v1,v2,v4],[]),([5,v0,2863315899,v3,v1,v2,v4],[]),([5,v0,2863329006,v3,v1,v2,v4],[]),([5,v0,2863332090,v3,v1,v2,v4],[]),([5,v0,2863333375,v3,v1,v2,v4],[]),([5,v0,2868903935,v3,v1,v2,v4],[]),([5,v0,2964369584,v3,v1,v2,v4],[]),([5,v0,3014898611,v3,v1,v2,v4],[]),([5,v0,3014898611,v1,v2,v4],[(6,8)]),([5,v0,3132799674,v3,v1,v2,v4],[]),([5,v0,3149642683,v3,v1,v2,v4],[]),([5,v0,3149660159,v3,v1,v2,v4],[(140,1)]),([5,v0,v3,3758153728,v1,v2,v4],[(72,5)]),([5,v0,v3,3768639648,v1,v2,v4],[(72,5),(144,0)]),([5,v0,v3,3772834016,v6,v2,v4],[(144,1),(184,1)]),([5,v0,v3,3772834016,v1,v2,v4],[(72,5),(144,0)])]

def K_16 : List (List Nat × List (Nat × Nat)) := [([5,v0,v3,3772834016,v1,v2,4294959328],[(72,5)]),([5,v0,v3,3772834016,vf,v2,v4],[(144,3),(184,1)]),([5,v0,v3,3772834016,4278124286,v2,v4],[(144,4),(184,2),(196,0)]),([5,v0,v3,3937069738,v1,v2,v4],[(72,5)]),([5,v0,v3,3938511552,v1,v2,v4],[(72,5),(80,1),(112,2),(144,6)]),([5,v0,v3,3941264106,v1,v2,v4],[(72,5)]),([5,v0,v3,3941264106,v1,v2,4294951104],[(72,5),(76,5)]),([5,v0,v3,3941264106,v1a,v2,v4],[(72,5)]),([5,v0,v3,4007718624,v1,v2,v4],[(72,5),(112,2),(144,0)]),([5,v0,v3,4008373994,v1,v2,v4],[(72,5)]),([5,v0,v3,v5,v6,v7,v4],[(96,9),(104,3),(112,3)]),([5,v0,v3,v5,v1b,v2,v4],[(148,1)]),([5,v0,v3,v5,v1,v2,v4],[]),([5,v0,v3,v5,v1,v2,v9],[(72,5)]),([5,v0,v3,v5,v1,v2,v10],[(96,8)]),([5,v0,v3,v5,v1,v2,4294959328],[(96,7),(104,1),(112,2)]),([5,v0,v3,4008640511,v1,v2,v4],[]),([5,v0,v3,v18,v6,v1,vd],[(72,5)]),([5,v0,v3,v18,v6,v7,v4],[(72,5),(116,3),(152,3),(192,3)]),([5,v0,v3,v18,v1,v2,v4],[(72,5),(152,3),(192,1)]),([5,v0,v3,v18,v1,v2,4294963200],[(72,5),(152,3),(192,1)]),([5,v0,v3,v18,v1,v2,v14],[(72,5),(116,1),(192,1)]),([5,v0,v3,v18,v1,vd],[(72,5),(73,5),(82,5),(153,2)]),([5,v0,v3,4026572800,v1,v2,v4],[(72,5),(192,1)]),([5,v0,v3,v6,v6,v7,v4],[]),([5,v0,v3,v6,4042260480,v1,vd],[]),([5,v0,v3,v6,4042260480,v2,v14],[(116,1),(144,0),(184,0)]),([5,v0,v3,v6,v1,v2,v4],[]),([5,v0,v3,v6,v1,v2,v9],[]),([5,v0,v3,v6,v1,v2,4294942720],[]),([5,v0,v3,v6,v1,v2,v10],[]),([5,v0,v3,v6,v1,v13,v4],[(112,0),(144,0)]),([5,v0,v3,v6,v1,v17,v4],[(112,0),(144,0)]),([5,v0,v3,v6,v1,4289396480,v4],[(112,3),(144,3)]),([5,v0,v3,v6,v1,4293984000,v4],[]),([5,v0,v3,v6,v1,v7,v4],[])]

def K_17 : List (List Nat × List (Nat × Nat)) := [([5,v0,v3,v6,v1,v4,vd],[]),([5,v0,v3,v6,v1,v4,v11],[]),([5,v0,v3,v6,v1,v12,vd],[(72,5)]),([5,v0,v3,v6,4205509290,v7,v4],[(112,3),(144,3)]),([5,v0,v3,v6,vf,v7,v4],[]),([5,v0,v3,v6,4293918720,v7,v4],[(116,3)]),([5,v0,v3,v6,v7,v7,v4],[]),([5,v0,v3,v6,v7,4294639610,v4],[]),([5,v0,v3,v6,v7,v4],[(74,3),(82,9),(149,3)]),([5,v0,v3,v6,v7,v4,v4],[(148,3)]),([5,v0,v3,v6,v7,v4,v12],[(72,9)]),([5,v0,v3,v6,v7,v4,4294963200],[(148,3)]),([5,v0,v3,v6,v7,v4,v14],[]),([5,v0,v3,v6,v7,v4,v11],[]),([5,v0,v3,v6,v4,v14,vd],[(116,3)]),([5,v0,v3,v6,v4,v14,v11],[(116,0)]),([5,v0,v3,v6,v4,v11],[(74,3),(82,9),(106,5),(117,3)]),([5,v0,v3,4026593520,v1,v2,v4],[(144,0)]),([5,v0,v3,4026593520,v2,4278255615,v4],[]),([5,v0,v3,4026593520,v2,v4],[]),([5,v0,v3,4026597375,v1,v2,v4],[(148,1)]),([5,v0,v3,4029739056,v1,v2,v4],[]),([5,v0,v3,4034982016,v1,v2,v4],[(144,0)]),([5,v0,v3,4034982016,v1,v13,v4],[(112,0),(144,0)]),([5,v0,v3,4037058720,v1,v2,v4],[(72,5),(144,0),(152,0)]),([5,v0,v3,4037079040,v1,v2,v4],[(144,0)]),([5,v0,v3,4037079040,v1,4289396480,v4],[(112,3),(144,3)]),([5,v0,v3,v1d,v1,v2,v4],[(144,0)]),([5,v0,v3,v1d,v1,v17,v4],[(112,0),(144,0)]),([5,v0,v3,v1d,v1,v7,v4],[]),([5,v0,v3,v1d,v1,v4,vd],[(148,0)]),([5,v0,v3,v1d,vf,v2,v4],[(144,4)]),([5,v0,v3,v1d,v2,v7,v4],[]),([5,v0,v3,v1d,v2,4294639610,v4],[]),([5,v0,v3,v1d,v2,v4,v14],[(148,0)]),([5,v0,v3,v1d,v1c,v7,v4],[])]

def K_18 : List (List Nat × List (Nat × Nat)) := [([5,v0,v3,v1d,v7,v4],[(74,3),(82,9),(149,3)]),([5,v0,v3,v1b,v1,v2,v4],[(144,0)]),([5,v0,v3,v1b,v2,v1c,v4],[]),([5,v0,v3,v1b,v2,4293853166,v4],[]),([5,v0,v3,v1b,v2,v4],[]),([5,v0,v3,4042321920,v1,v2,v4],[]),([5,v0,v3,4042321920,v2,v7,v4],[]),([5,v0,v3,4042321920,v2,v4,v11],[(148,0),(156,2)]),([5,v0,v3,4042322080,v1,v2,v4],[]),([5,v0,v3,v1,v1,v2,v4],[]),([5,v0,v3,v1,v1,v2,v9],[]),([5,v0,v3,v1,v1,v2,v10],[]),([5,v0,v3,v1,v1,v2,4294945280],[(88,1),(92,1)]),([5,v0,v3,v1,4042322175,v2,v4],[]),([5,v0,v3,v1,4042322931,v2,v4],[]),([5,v0,v3,v1,4042324730,v2,v4],[]),([5,v0,v3,v1,4042326000,v2,v4],[(112,2),(156,1)]),([5,v0,v3,v1,4042326015,v2,v4],[(156,1)]),([5,v0,v3,v1,4043309055,v2,v4],[(156,1),(196,3)]),([5,v0,v3,v1,4059165169,v2,v4],[]),([5,v0,v3,v1,4076008178,v2,v4],[]),([5,v0,v3,v1,4080268083,v2,v4],[]),([5,v0,v3,v1,4092654576,v2,v4],[]),([5,v0,v3,v1,4092851187,v2,v4],[]),([5,v0,v3,v1,4092854271,v2,v4],[(156,1)]),([5,v0,v3,v1,4160223223,v2,v4],[(156,1),(196,3)]),([5,v0,v3,v1,4169726088,v2,v4],[(112,2),(144,3),(152,0)]),([5,v0,v3,v1,4176541936,v2,v4],[(112,2)]),([5,v0,v3,v1,v16,v2,v4],[(112,2)]),([5,v0,v3,v1,v16,v2,v9],[(112,1)]),([5,v0,v3,v1,4205488810,v2,v4],[(96,5),(144,3),(184,1)]),([5,v0,v3,v1,4205506560,v2,v4],[(112,4),(144,3),(152,3)]),([5,v0,v3,v1,4205509290,v2,v4],[(144,3)]),([5,v0,v3,v1,4205509290,v7,v4],[(144,3)]),([5,v0,v3,v1,4205509290,v4,vd],[(128,5),(156,3),(184,3)]),([5,v0,v3,v1,4207475400,v2,v4],[(112,2),(144,3),(152,6)])]

def K_19 : List (List Nat × List (Nat × Nat)) := [([5,v0,v3,v1,4209703658,v2,v4],[(144,3)]),([5,v0,v3,v1,4210094320,v2,v4],[(112,2)]),([5,v0,v3,v1,4210096880,v2,v4],[(112,2)]),([5,v0,v3,v1,4210096880,v2,4294945280],[(112,1),(116,1)]),([5,v0,v3,v1,4210096880,v1c,v4],[(112,3)]),([5,v0,v3,v1,4210621176,v2,v4],[(112,2)]),([5,v0,v3,v1,4210752000,v2,v4],[(112,2)]),([5,v0,v3,v1,4210752170,v2,v4],[]),([5,v0,v3,v1,4210752240,v2,v4],[(112,2)]),([5,v0,v3,v1,vf,v2,v4],[]),([5,v0,v3,v1,vf,v2,v9],[]),([5,v0,v3,v1,vf,v2,v10],[(112,2)]),([5,v0,v3,v1,vf,v2,4294945280],[(100,1),(116,1)]),([5,v0,v3,v1,vf,v2,4294951104],[(100,5),(116,5)]),([5,v0,v3,v1,vf,v2,4294953160],[(100,5),(116,5)]),([5,v0,v3,v1,vf,v2,4294953984],[(100,7),(116,7),(156,1)]),([5,v0,v3,v1,4210753535,v2,v4],[(156,1)]),([5,v0,v3,v1,4227595259,v2,v4],[]),([5,v0,v3,v1,4277075694,v2,v4],[(144,3),(156,1),(196,3)]),([5,v0,v3,v1,4277206768,v2,v4],[(112,2),(156,1)]),([5,v0,v3,v1,4277862138,v2,v4],[(156,1)]),([5,v0,v3,v1,4278124286,v2,v4],[(156,1),(196,3)]),([5,v0,v3,v1,v2,4293980400,v4],[]),([5,v0,v3,v1,v2,4293982960,v4],[]),([5,v0,v3,v1,v2,v7,v4],[]),([5,v0,v3,v1,v2,v7,v9],[]),([5,v0,v3,v1,v2,v7,v10],[]),([5,v0,v3,v1,v2,v7,4294945440],[]),([5,v0,v3,v1,v2,4293984255,v4],[]),([5,v0,v3,v1,v2,4294180851,v4],[]),([5,v0,v3,v1,v2,4294508536,v4],[]),([5,v0,v3,v1,v2,4294638330,v4],[]),([5,v0,v3,v1,v2,4294639600,v4],[]),([5,v0,v3,v1,v2,4294639610,v4],[]),([5,v0,v3,v1,v2,4294901758,v4],[(204,3)]),([5,v0,v3,v1,v2,v4],[])]

def K_20 : List (List Nat × List (Nat × Nat)) := [([5,v0,v3,v1,v2,v4,v11],[(148,0),(156,2)]),([5,v0,v3,v1,v2,v4,4294967290],[(180,5)]),([5,v0,v3,v1,v2,v4,4294967295],[]),([5,v0,v3,v1,v2,4294902000],[(74,2),(82,8),(117,1),(149,0)]),([5,v0,v3,v1,v2,4294902015,v14],[(148,0)]),([5,v0,v3,v1,v2,4294902015,vd],[(148,0),(156,2)]),([5,v0,v3,v1,v2,4294914867,v19],[]),([5,v0,v3,v1,v2,4294934656],[]),([5,v0,v3,v1,v2,v9],[(57,5)]),([5,v0,v3,v1,v2,v9,v9],[]),([5,v0,v3,v1,v2,v9,v12],[]),([5,v0,v3,v1,v2,v9,v14],[(148,0)]),([5,v0,v3,v1,v2,v9,4294965496],[(148,0)]),([5,v0,v3,v1,v2,4294942720],[]),([5,v0,v3,v1,v2,v10],[(74,2)]),([5,v0,v3,v1,v2,v10,v10],[]),([5,v0,v3,v1,v2,v10,v12],[]),([5,v0,v3,v1,v2,v10,v19],[(188,6)]),([5,v0,v3,v1,v2,v10,4294962412],[(188,0)]),([5,v0,v3,v1,v2,v10,v14],[(148,0)]),([5,v0,v3,v1,v2,v10,vd],[(156,2)]),([5,v0,v3,v1,v2,v10,4294967200],[(156,2)]),([5,v0,v3,v1,v2,4294944936],[(57,5),(74,2)]),([5,v0,v3,v1,v2,4294945440],[(74,2),(98,0)]),([5,v0,v3,v1,v2,v12,v19],[]),([5,v0,v3,v1,v2,v12,4294963200],[]),([5,v0,v3,v1,v2,v12,v14],[(148,0)]),([5,v0,v3,v1,v2,v12,4294966524],[]),([5,v0,v3,v1,v2,v12,v11],[(148,0),(156,2)]),([5,v0,v3,v1,v2,4294959328],[(74,1),(82,7),(117,1),(149,0)]),([5,v0,v3,v1,v2,4294962926,v14],[(148,0),(156,2)]),([5,v0,v3,v1,v13,v9],[(57,5)]),([5,v0,v3,v1,v17,v10],[(74,1)]),([5,v0,v3,v1,4289374890,vd],[(57,5),(73,5),(133,2)]),([5,v0,v3,v1,4289396480,v12],[(57,5)]),([5,v0,v3,v1,v1c,v12,vd],[(172,2),(204,0)])]

def K_21 : List (List Nat × List (Nat × Nat)) := [([5,v0,v3,v1,v1c,v19,vd],[]),([5,v0,3435986943,v1,v2,v4,v19],[]),([5,v0,3722304989,v5,v1,v2,v4],[]),([5,v0,3770736832,4006407884,v1,v2,v4],[(80,1),(104,1),(136,1),(176,1)]),([5,v0,3772834016,ve,v1,v2,v4],[(136,0)]),([5,v0,3772834016,v5,v1a,v2,v4],[(136,3),(176,1)]),([5,v0,3972852940,v6,v1,v2,v4],[]),([5,v0,3972852940,v1,v2,v4],[]),([5,v0,ve,ve,v1,v2,v4],[]),([5,v0,ve,v5,v1,v2,v4],[(96,5)]),([5,v0,ve,v6,v1,v2,v4],[]),([5,v0,ve,v1,v1,v2,v4],[]),([5,v0,ve,v1,vf,v2,v4],[]),([5,v0,ve,v1,v1a,v2,v4],[]),([5,v0,ve,v1,4278190080,v2,v4],[]),([5,v0,ve,v1,v2,v2,v4],[]),([5,v0,ve,v1,v2,v17,v4],[(152,0)]),([5,v0,ve,v1,v2,v1c,v4],[]),([5,v0,ve,v1,v2,4291624908,v4],[]),([5,v0,ve,v1,v2,4293722092,v4],[]),([5,v0,ve,v1,v2,v7,v4],[]),([5,v0,ve,v1,v2,v4],[]),([5,v0,ve,v1,v2,v4,vd],[]),([5,v0,ve,v1,v2,v10],[]),([5,v0,ve,vf,v2,v4],[(57,5)]),([5,v0,4008505068,v1,v2,v7,v4],[]),([5,v0,4008505068,v1,v2,v4],[(74,1)]),([5,v0,v5,v1,v16,v2,v4],[(72,2),(112,2)]),([5,v0,v5,v1,4241292492,v2,v4],[(144,3)]),([5,v0,v5,v1,v1a,v2,v4],[(72,2)]),([5,v0,v5,v1,v2,4294770684,v4],[(72,2),(96,0)]),([5,v0,v5,v1,v2,v9],[(2,5),(97,1),(101,1),(133,3)]),([5,v0,v5,v1,v2,v12,v19],[(180,3)]),([5,v0,v5,v1,v2,v19,v14],[(72,1),(168,5)]),([5,v0,v18,v1,v15,v2,v4],[(144,3),(184,1)]),([5,v0,v6,v1,v15,v2,v4],[(184,1)])]

def K_22 : List (List Nat × List (Nat × Nat)) := [([5,v0,v1,v15,v2,v4],[(104,3),(105,2),(106,0),(136,1),(137,4),(153,3),(154,1)]),([5,v0,v1,4241292492,v2,v4,v19],[(104,3),(136,1)]),([5,3941264106,v1,v1a,v2,v4],[(6,2)]),([5,v5,v1,v16,v2,v4],[(6,2),(58,2),(80,2),(81,2),(105,2),(109,1),(137,4),(141,3),(145,0)]),([5,v5,v1,vf,v1a,v2,v4],[(80,2),(104,2)]),([5,v5,v1,vf,v2,4291624908,v4],[(104,3),(112,6),(136,2)]),([5,v5,v1,v2,v9],[(6,2),(7,2),(9,1),(10,0),(11,0),(75,1),(79,1),(103,3),(111,0),(115,1),(119,2)]),([5,v5,v1,v2,v12,v19],[(102,3),(106,5),(114,7),(134,9),(146,1),(157,5)]),([6,0,v8,v0,v3,v1,v2],[]),([6,0,v8,v0,v3,v1,v2,v4],[]),([6,0,va,v0,v3,v1,v2,v4],[]),([6,0,va,v0,v1,v2,v4],[]),([6,0,v0,v3,v1,v2,v4],[(73,5),(129,1),(169,3)]),([6,255,v0,v3,v1,v2,v4],[(2,2),(73,5),(77,5),(129,1),(169,3)]),([6,255,v0,v3,v1,v2,v4,vd],[(128,0)]),([6,13107,v0,v3,v1,v2,v4],[(2,9),(73,5),(129,1),(133,1),(169,3)]),([6,13107,v0,v3,v1,v2,v4,v19],[]),([6,43690,v8,v0,v3,v1,v2],[]),([6,43690,v8,v0,v3,v1,v2,v4],[]),([6,43690,v0,v3,v1,v2,v4],[(2,9),(73,5),(129,1),(133,1),(169,3)]),([6,61680,v8,v0,v3,v1,v2],[]),([6,61680,v8,v0,v3,v1,v2,v4],[]),([6,61680,v0,v3,v1,v2,v4],[(2,4),(73,5),(77,5),(114,5),(128,0),(129,1),(169,0)]),([6,v8,v8,v0,v3,v1,v2],[]),([6,v8,v8,v0,v3,v1,v2,v4],[]),([6,v8,16711935,v0,v3,v1],[(2,0),(10,5)]),([6,v8,16711935,v0,v3,v1,v2],[(2,0)]),([6,v8,16711935,v0,v3,v1,v2,v4],[]),([6,v8,va,v0,v3,v1,v2],[]),([6,v8,va,v0,v3,v1,v2,v4],[]),([6,v8,va,v0,v1,v2],[(14,1)]),([6,v8,va,v0,v1,v2,v4],[]),([6,v8,vb,v0,v3,v1,v2],[(136,1)]),([6,v8,vb,v0,v3,v1,v2,v4],[(136,1)]),([6,v8,vc,v0,v3,v1,v2],[]),([6,v8,vc,v0,v3,v1,v2,v4],[])]

def K_23 : List (List Nat × List (Nat × Nat)) := [([6,v8,2863267840,v0,v3,v1,v2],[(2,3),(136,1)]),([6,v8,2863267840,v0,v3,v1,v2,v4],[(136,1)]),([6,v8,v0,v0,v3,v1,v2],[]),([6,v8,v0,v0,v3,v1,v2,v4],[]),([6,v8,v0,2863333375,v3,v1,v2],[]),([6,v8,v0,2863333375,v3,v1,v2,v4],[]),([6,v8,v0,v3,v5,v1,v2],[]),([6,v8,v0,v3,v5,v1,v2,v4],[(76,5)]),([6,v8,v0,v3,v6,v1,v2],[]),([6,v8,v0,v3,v6,v1,v2,v4],[(172,1)]),([6,v8,v0,v3,4042260480,v1,v2],[(2,0)]),([6,v8,v0,v3,4042260480,v1,v2,v4],[]),([6,v8,v0,v3,v1,v1,v2],[]),([6,v8,v0,v3,v1,v1,v2,v4],[]),([6,v8,v0,v3,v1,4042326015,v2],[(204,1)]),([6,v8,v0,v3,v1,4042326015,v2,v4],[(204,1)]),([6,v8,v0,v3,v1,vf,v2],[]),([6,v8,v0,v3,v1,vf,v2,v4],[]),([6,v8,v0,v3,v1,v2],[(6,5),(14,1)]),([6,v8,v0,v3,v1,v2,v7],[]),([6,v8,v0,v3,v1,v2,v7,v4],[(96,2),(128,0)]),([6,v8,v0,v3,v1,v2,v4],[(2,3),(73,5),(77,5),(129,1),(133,1)]),([6,v8,v0,v3,v1,v2,v4,v4],[]),([6,v8,v0,v3,v1,v2,v4,v12],[(56,5)]),([6,v8,v0,v3,v1,v2,v4,v14],[(96,2)]),([6,v8,v0,v3,v1,v2,v4,4294967295],[]),([6,v8,v0,v3,v1,v2,v12],[(2,3)]),([6,v8,v0,v3,v1,v2,v14],[(2,0)]),([6,v8,v0,v3,v1,v2,4294967295],[]),([6,16777215,v0,v3,v1,4278190080,v2,v4],[(172,1),(220,3)]),([6,16777215,v0,v3,v1,v2,v4],[(2,2),(73,5),(77,5),(133,1),(173,3)]),([6,286331153,v0,v3,v5,v1,v2,v4],[(56,5)]),([6,286331153,v0,v3,v1,v2,v4],[(73,5),(129,1),(133,1),(169,3),(173,3)]),([6,572662306,va,v0,v3,v1,v2,v4],[]),([6,572662306,va,v0,v1,v2,v4],[]),([6,572662306,v0,v3,v1,v2,v4],[(2,5),(129,1),(133,1),(137,1),(169,3),(173,3),(177,3)])]

def K_24 : List (List Nat × List (Nat × Nat)) := [([6,808464432,va,v0,v3,v1,v2,v4],[]),([6,808464432,va,v0,v1,v2,v4],[]),([6,808464432,v0,v3,v1,v2,v4],[(2,8),(73,5),(129,1),(169,3),(173,0),(193,0)]),([6,va,va,v0,v3,v1,v2,v4],[]),([6,va,va,v0,v1,v2,v4],[]),([6,va,1431655765,v0,v3,v1,v2,v4],[]),([6,va,1431655765,v0,v1,v2,v4],[(2,5)]),([6,va,1431655765,v1,v2,v4],[(2,5),(10,2),(14,0)]),([6,va,vb,v0,v3,v1,v2,v4],[(136,2),(176,0)]),([6,va,vb,v0,v1,v2,v4],[(104,2),(136,0)]),([6,va,vc,v0,v3,v1,v2,v4],[(176,0)]),([6,va,vc,v0,v1,v2,v4],[(136,0)]),([6,va,v0,v0,v3,v1,v2,v4],[]),([6,va,v0,v0,v1,v2,v4],[]),([6,va,v0,3149642683,v3,v1,v2,v4],[]),([6,va,v0,3149642683,v1,v2,v4],[]),([6,va,v0,3233857728,v3,v1,v2,v4],[(184,0)]),([6,va,v0,3233857728,v1,v2,v4],[(2,5),(144,0)]),([6,va,v0,v3,v3,v1,v2,v4],[]),([6,va,v0,v3,v5,v1,v2,v4],[(56,5)]),([6,va,v0,v3,v6,v1,v2,v4],[]),([6,va,v0,v3,v1,v1,v2,v4],[]),([6,va,v0,v3,v1,4092851187,v2,v4],[]),([6,va,v0,v3,v1,vf,v2,v4],[]),([6,va,v0,v3,v1,v1a,v2,v4],[(96,2)]),([6,va,v0,v3,v1,v2,v7,v4],[(132,1)]),([6,va,v0,v3,v1,v2,v4],[(2,5),(129,1),(133,1),(169,3),(173,3)]),([6,va,v0,v3,v1,v2,v4,4294967295],[]),([6,va,v0,v5,v1,v2,v4],[]),([6,va,v0,v6,v1,v2,v4],[]),([6,va,v0,v1,v1,v2,v4],[]),([6,va,v0,v1,4092851187,v2,v4],[]),([6,va,v0,v1,vf,v2,v4],[]),([6,va,v0,v1,v1a,v2,v4],[(2,5)]),([6,va,v0,v1,v2,v7,v4],[]),([6,va,v0,v1,v2,v4],[(10,2),(14,0)])]

def K_25 : List (List Nat × List (Nat × Nat)) := [([6,va,v0,v1,v2,v4,4294967295],[]),([6,859045887,v0,3435921408,v3,v1,v2,v4],[(100,5),(144,1),(172,1),(220,3)]),([6,859045887,v0,v3,v1,v2,v4],[(2,9),(77,5),(129,1),(132,1),(133,1),(134,1),(173,3)]),([6,2004318071,vb,v0,v3,v1,v2,v4],[(100,5),(136,2),(172,1),(176,0),(220,3)]),([6,2004318071,v0,v3,v1,v2,v4],[(77,5),(129,1),(132,1),(133,1),(134,1),(169,3),(172,3),(173,3),(174,3)]),([6,2155905152,vb,v0,v3,v1,v2,v4],[(168,0),(176,0)]),([6,2155905152,vc,v0,v3,v1,v2,v4],[(168,0),(176,0)]),([6,2155905152,v0,v3,v1,v2,v4],[(2,2),(73,5),(128,0),(129,1),(130,0),(169,3),(173,0)]),([6,vb,vb,v0,v3,v1,v2,v4],[(128,2),(168,0)]),([6,vb,vc,v0,v3,v1,v2,v4],[(168,0),(176,0)]),([6,vb,v0,v0,v3,v1,v2,v4],[(128,2),(168,0)]),([6,vb,v0,v3,v5,v1,v2,v4],[(60,5),(104,5),(128,2),(168,0)]),([6,vb,v0,v3,v6,v1,v2,v4],[(128,1)]),([6,vb,v0,v3,v1,v1,v2,v4],[(168,0)]),([6,vb,v0,v3,v1,v16,v2,v4],[(96,2),(152,2),(168,0)]),([6,vb,v0,v3,v1,vf,v2,v4],[(96,2),(168,0)]),([6,vb,v0,v3,v1,v2,v7,v4],[(96,2),(128,0)]),([6,vb,v0,v3,v1,v2,v4],[(73,5),(81,5),(96,2),(98,2),(128,0),(129,1),(130,0),(133,1),(169,3),(173,3)]),([6,vb,v0,v3,v1,v2,v9],[(73,5),(81,5),(96,1),(98,1),(129,1),(133,1)]),([6,vb,v0,v5,v1,v2,v4],[(6,5),(96,2),(98,2),(128,0),(129,1),(130,0),(137,1),(141,1),(169,3),(177,3),(181,3)]),([6,vb,v5,v1,v2,v4],[(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(72,2),(74,2),(96,0),(97,1),(98,0),(99,1),(103,1),(107,1),(111,1),(129,3),(131,3),(135,3),(139,3),(143,3),(147,0),(151,0),(155,2),(159,2)]),([6,2684395520,vc,v0,v3,v1,v2,v4],[]),([6,2684395520,v0,v3,v6,v1,v2,v4],[]),([6,2684395520,v0,v3,v1,v2,v4],[(2,9),(73,5),(129,1),(169,3)]),([6,vc,vc,v0,v3,v1,v2,v4],[(168,0)]),([6,vc,2852170240,v0,v3,v1,v2,v4],[(72,1),(96,1),(128,1),(168,1),(216,1)]),([6,vc,v0,v0,v3,v1,v2,v4],[(168,0)]),([6,vc,v0,3233857728,v3,v1,v2,v4],[(56,5),(96,5),(128,5),(168,6),(184,0),(216,5)]),([6,vc,v0,3422604288,v3,v1,v2,v4],[(56,7),(72,1),(96,7),(128,7),(168,7),(216,7)]),([6,vc,v0,v3,v3,v1,v2,v4],[(56,5),(72,5),(128,5),(168,6),(216,5)]),([6,vc,v0,v3,ve,v1,v2,v4],[(56,5),(96,5),(128,5),(168,6),(216,5)]),([6,vc,v0,v3,v5,v1,v2,v4],[(168,0)]),([6,vc,v0,v3,v6,v1,v2,v4],[]),([6,vc,v0,v3,v1,v1,v2,v4],[(168,0)]),([6,vc,v0,v3,v1,vf,v2,v4],[(168,0)]),([6,vc,v0,v3,v1,v1a,v2,v4],[(56,5),(96,5),(128,5),(168,6),(216,5)])]

def K_26 : List (List Nat × List (Nat × Nat)) := [([6,vc,v0,v3,v1,4278190080,v2,v4],[(56,2),(96,2),(128,2),(168,4),(216,2)]),([6,vc,v0,v3,v1,v2,v2,v4],[(56,1),(96,1),(128,1),(216,1)]),([6,vc,v0,v3,v1,v2,v17,v4],[(56,1),(96,1),(128,0),(168,1),(200,0),(216,1)]),([6,vc,v0,v3,v1,v2,v1c,v4],[(56,1),(96,1),(128,0),(168,1),(216,1)]),([6,vc,v0,v3,v1,v2,4291624908,v4],[(56,7),(96,7),(128,0),(168,7),(216,7)]),([6,vc,v0,v3,v1,v2,v7,v4],[(128,0)]),([6,vc,v0,v3,v1,v2,v4],[(2,8),(73,5),(128,0),(129,1),(130,0),(169,3),(173,0)]),([6,vc,v0,v3,v1,v2,v4,vd],[(56,2),(96,2),(128,0),(216,2)]),([6,vc,v0,v3,v1,v2,v10],[(2,8),(73,5),(129,1)]),([6,vc,v0,v3,vf,v2,v4],[(73,5),(128,4),(129,1),(130,0),(168,2),(169,3)]),([6,vc,v0,ve,v1,v2,v4],[(2,8),(128,0),(130,0),(169,0),(173,0)]),([6,vc,v3,v1,vf,v2,v4],[(10,2),(56,5)]),([6,2829625512,v0,v3,v1,v1a,v2,v4],[(56,5),(96,8),(128,5),(168,6),(216,5)]),([6,2829625512,v0,v3,v1,v2,v4],[(2,8),(73,5),(96,2),(128,0),(129,1),(130,0),(133,1),(169,3),(173,3)]),([6,2862656160,v0,v3,v1,v2,v7,v4],[(96,2),(128,0)]),([6,2862656160,v0,v3,v1,v2,v4],[(2,9),(73,5),(96,2),(98,1),(106,1),(128,0),(129,1),(133,1),(169,3),(173,3)]),([6,v0,v0,v0,v3,v1,v2,v4],[]),([6,v0,v0,v3,v3,v1,v2,v4],[(48,5),(52,5)]),([6,v0,v0,v3,v5,v1,v2,v4],[]),([6,v0,v0,v3,v6,v1,v2,v4],[]),([6,v0,v0,v3,v1,v1,v2,v4],[]),([6,v0,v0,v3,v1,vf,v2,v4],[]),([6,v0,v0,v3,v1,v1a,v2,v4],[(48,5),(52,5),(96,2)]),([6,v0,v0,v3,v1,v2,v7,v4],[(96,2),(128,0)]),([6,v0,v0,v3,v1,v2,v4],[(2,5),(129,1),(133,1),(169,3),(173,3)]),([6,v0,2863333375,v3,v1,v2,v4],[(6,9),(85,5),(137,1),(141,1),(169,5),(181,3)]),([6,v0,3149642683,v3,v1,v2,v4],[(6,5),(73,5),(137,1),(141,1),(177,3),(181,3)]),([6,v0,v3,3772834016,v5,v1,v2,v4],[(72,5),(128,5),(184,0)]),([6,v0,v3,3772834016,v1,v2,v4],[(10,2),(72,5),(73,5),(82,5),(86,5),(106,5),(144,0),(145,1),(146,0),(185,3),(189,0),(197,0)]),([6,v0,v3,3941264106,v1,v2,v4],[(2,5),(10,8),(57,5),(61,5),(72,5),(73,5),(86,5),(97,5),(129,5),(133,1),(145,1),(149,1),(169,6),(173,3),(185,3),(189,3)]),([6,v0,v3,v5,v5,v1,v2,v4],[]),([6,v0,v3,v5,v6,v1,v2,v4],[(96,5),(188,1)]),([6,v0,v3,v5,v1,v1,v2,v4],[(96,5)]),([6,v0,v3,v5,v1,vf,v2,v4],[(72,5),(104,2),(128,5),(140,5)]),([6,v0,v3,v5,v1,4278124286,v2,v4],[(204,1),(252,3)]),([6,v0,v3,v5,v1,v2,v7,v4],[(96,8),(104,2),(112,2),(128,6),(136,0),(144,0),(168,5)])]

def K_27 : List (List Nat × List (Nat × Nat)) := [([6,v0,v3,v5,v1,v2,v4],[(61,5),(86,5),(97,5),(129,7),(137,1),(145,1),(149,1),(169,9),(177,3),(185,3),(189,3)]),([6,v0,v3,v18,v6,v1,v2,v4],[(72,5),(248,1)]),([6,v0,v3,v18,v1,v2,v4],[(72,5),(73,5),(82,5),(86,5),(145,1),(152,3),(153,2),(154,0),(185,3),(192,1),(193,4),(201,3),(202,1)]),([6,v0,v3,v6,v6,v1,v2,v4],[]),([6,v0,v3,v6,4042260480,v1,v2,v4],[(144,0),(184,0),(200,0),(232,0)]),([6,v0,v3,v6,v1,v1,v2,v4],[]),([6,v0,v3,v6,v1,4205509290,v2,v4],[]),([6,v0,v3,v6,v1,vf,v2,v4],[]),([6,v0,v3,v6,v1,v2,v7,v4],[(116,1),(192,1)]),([6,v0,v3,v6,v1,v2,v4],[(10,3),(82,5),(86,5),(145,1),(153,1),(185,3),(193,1)]),([6,v0,v3,v6,v1,v2,v4,v4],[(112,3),(144,3),(184,3),(192,1)]),([6,v0,v3,v6,v1,v2,v4,v12],[(72,5),(112,3),(144,3),(192,1),(232,3)]),([6,v0,v3,v6,v1,v2,v4,4294963200],[(112,3),(144,3),(232,3),(240,1)]),([6,v0,v3,v6,v1,v2,v4,v14],[(112,0),(116,1),(144,0),(232,0),(240,1)]),([6,v0,v3,v6,v1,v7,v4],[(14,2),(82,5),(106,5),(110,5),(189,0),(197,0)]),([6,v0,v3,v6,v1,v4,vd],[(82,5),(138,5),(149,3),(193,1)]),([6,v0,v3,v6,v7,v4],[(2,5),(3,5),(5,5),(10,3),(11,3),(14,3),(15,3),(74,3),(82,9),(83,5),(87,5),(107,5),(111,5),(135,3),(139,5),(143,9),(149,3)]),([6,v0,v3,v1d,v1,v2,v1c,v4],[(112,1),(144,0),(184,1)]),([6,v0,v3,v1d,v1,v2,v4],[(10,10),(82,5),(86,5),(110,5),(144,0),(145,1),(185,3),(189,0)]),([6,v0,v3,4042321920,v1,v2,v4],[(10,2),(82,5),(86,5),(145,1),(185,3),(189,0),(193,0)]),([6,v0,v3,4042321920,v1,v2,v4,vd],[(112,2),(188,0),(204,2),(232,2)]),([6,v0,v3,v1,v1,v1,v2,v4],[]),([6,v0,v3,v1,v1,vf,v2,v4],[]),([6,v0,v3,v1,v1,v2,v2,v4],[(88,1),(92,1)]),([6,v0,v3,v1,v1,v2,v1c,v4],[(88,1),(92,1),(144,0)]),([6,v0,v3,v1,v1,v2,v7,v4],[]),([6,v0,v3,v1,v1,v2,v4],[(10,2),(82,5),(86,5),(185,0),(189,0)]),([6,v0,v3,v1,v1,v2,v4,vd],[(88,2),(92,2),(188,0),(204,2)]),([6,v0,v3,v1,4042326015,v2,v4],[(14,4),(106,5),(110,5),(145,2),(156,1),(157,1),(158,1),(185,2),(197,0)]),([6,v0,v3,v1,4092851187,v2,v4],[(14,8),(82,2),(110,5),(157,1),(193,0),(197,3)]),([6,v0,v3,v1,v16,v2,v4],[(10,2),(14,2),(57,5),(74,2),(82,8),(86,5),(106,5),(110,5),(112,2),(113,2),(145,2),(149,1),(157,1),(185,4),(189,3),(193,0),(197,3)]),([6,v0,v3,v1,4205509290,v2,v4],[(14,9),(57,5),(110,5),(144,3),(145,1),(153,1),(157,1),(169,5),(185,1),(193,3),(197,3)]),([6,v0,v3,v1,4210096880,v2,v4],[(10,2),(14,10),(74,2),(82,2),(86,5),(106,5),(110,5),(112,2),(113,2),(145,2),(149,1),(157,1),(185,2),(189,3),(193,0),(197,3)]),([6,v0,v3,v1,vf,vf,v2,v4],[]),([6,v0,v3,v1,vf,v1a,v2,v4],[(100,5),(112,2),(116,5),(144,2)]),([6,v0,v3,v1,vf,4278124286,v2,v4],[(204,1),(252,3)])]

def K_28 : List (List Nat × List (Nat × Nat)) := [([6,v0,v3,v1,vf,v2,v1c,v4],[(100,1),(116,1),(144,3),(156,1)]),([6,v0,v3,v1,vf,v2,4291624908,v4],[(100,7),(116,7),(144,3),(152,6),(184,2)]),([6,v0,v3,v1,vf,v2,v7,v4],[(112,2),(156,1),(184,2)]),([6,v0,v3,v1,vf,v2,4294639610,v4],[(156,1)]),([6,v0,v3,v1,vf,v2,v4],[(14,8),(57,5),(82,2),(110,5),(145,2),(157,1),(185,4),(193,0),(197,3)]),([6,v0,v3,v1,vf,v2,v4,vd],[(100,2),(116,2),(156,1),(196,3),(204,2),(232,2)]),([6,v0,v3,v1,4278124286,v2,v4],[(14,2),(110,5),(145,2),(156,1),(157,1),(158,1),(185,4),(193,0),(196,3),(197,3),(198,3)]),([6,v0,v3,v1,v2,4293980400,v4],[(18,2),(74,2),(82,8),(117,1),(138,5),(142,5),(158,1),(189,3),(201,0),(205,3)]),([6,v0,v3,v1,v2,v7,v7,v4],[]),([6,v0,v3,v1,v2,v7,4294639610,v4],[]),([6,v0,v3,v1,v2,v7,v4],[(18,3),(74,2),(82,8),(98,0),(106,6),(117,1),(138,5),(142,5),(158,1),(189,3),(197,4),(205,3)]),([6,v0,v3,v1,v2,v7,v4,v14],[(148,0),(156,0),(188,0),(196,2),(204,3),(244,1)]),([6,v0,v3,v1,v2,v7,v4,v11],[(188,0),(196,2),(204,3)]),([6,v0,v3,v1,v2,4294639610,v4],[(18,9),(57,5),(82,8),(106,6),(142,5),(158,1),(205,3)]),([6,v0,v3,v1,v2,v4],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(131,3),(135,3),(139,9),(143,9),(147,0),(151,0),(155,2),(159,2)]),([6,v0,v3,v1,v2,v4,v11],[(74,2),(82,8),(98,0),(106,6),(117,1),(138,5),(148,0),(149,3),(150,0),(156,2),(157,4),(158,2),(178,5),(182,5),(198,1),(206,3)]),([6,v0,v3,v1,v2,v4,4294967295],[(182,5),(198,1),(206,3)]),([6,v0,v3,v1,v2,v9],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(57,5),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(135,3),(139,5),(143,9),(151,0),(155,1),(159,2)]),([6,v0,v3,v1,v2,v10],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(18,7),(19,7),(74,2),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(135,0),(143,9),(151,0),(159,2)]),([6,v0,v3,v1,v2,v12,v19],[(57,5),(142,9),(146,5),(154,7),(174,3),(194,1),(205,5)]),([6,v0,v3,v1,v2,v12,v14],[(57,5),(74,1),(82,2),(117,1),(148,0),(149,0),(150,0),(158,2),(174,0)]),([6,v0,ve,v1,v2,v4],[(2,5),(3,5),(6,2),(7,2),(10,2),(11,2),(14,0),(15,0),(17,0),(73,5),(103,1),(111,1),(131,0),(135,3),(139,0),(143,3),(147,0),(151,0)]),([6,v0,v5,v1,v1a,v2,v4],[(72,2),(74,2),(129,1),(145,2),(169,3),(185,4),(193,0)]),([7,v8,v0,v3,v1,v2],[(6,5),(7,5),(9,5),(14,1),(15,1),(17,1),(75,5),(79,5),(115,5),(119,5),(131,1),(135,1),(139,1),(143,1),(147,7),(151,7)]),([7,v8,v0,v3,v1,v2,v4],[(2,3),(6,5),(7,5),(9,5),(14,2),(15,1),(17,1),(18,0),(73,5),(75,5),(77,5),(79,5),(115,5),(119,5),(129,1),(131,1),(133,1),(135,1),(139,1),(143,1),(147,7),(151,7),(186,5),(187,5),(190,5),(191,5),(202,1),(203,1),(206,1),(207,1)]),([7,va,v0,v3,v1,v2,v4],[(2,5),(6,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(129,1),(131,1),(133,1),(135,1),(139,1),(143,1),(145,1),(147,1),(149,1),(151,1),(169,3),(171,3),(173,3),(175,3),(179,3),(183,3),(185,3),(187,3),(189,3),(191,3),(195,0),(199,0),(203,2),(207,2)]),([7,va,v0,v1,v2,v4],[(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(99,1),(103,1),(107,1),(111,1),(131,3),(135,3),(139,3),(143,3),(147,0),(151,0),(155,2),(159,2)]),([7,vb,v0,v3,v1,v2,v4],[(6,5),(7,5),(9,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(73,5),(75,5),(81,5),(96,2),(98,2),(115,5),(119,5),(128,0),(129,1),(130,0),(131,1),(133,1),(135,1),(139,1),(143,1),(147,7),(151,7),(169,3),(171,3),(173,3),(175,3),(179,3),(183,3),(187,9),(191,9),(195,0),(199,0),(203,2),(207,2)]),([7,vc,v0,v3,v1,v2,v4],[(2,8),(3,8),(6,5),(7,5),(14,2),(15,2),(18,0),(19,0),(21,0),(73,5),(128,0),(129,1),(130,0),(169,3),(171,0),(173,0),(175,0),(179,0),(183,0),(187,0),(191,0),(195,0),(199,0)]),([7,v0,v0,v3,v1,v2,v4],[(2,5),(3,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(119,5),(129,1),(131,1),(133,1),(135,1),(147,1),(151,7),(169,3),(171,3),(173,3),(175,3),(187,3),(191,9),(195,0),(199,0),(203,2),(207,2)]),([7,v0,v3,v5,v1,v2,v4],[(2,5),(3,5),(5,5),(14,2),(15,2),(17,1),(18,0),(19,0),(21,3),(61,5),(86,5),(87,5),(97,5),(107,5),(111,5),(129,7),(131,1),(135,1),(137,1),(139,7),(143,7),(145,1),(147,1),(149,1),(151,1),(169,9),(171,3),(175,3),(177,3),(179,9),(183,9),(185,3),(187,3),(189,3),(191,3),(195,0),(199,0),(203,2),(207,2)]),([7,v0,v3,v6,v1,v2,v4],[(2,5),(3,5),(5,5),(10,3),(11,3),(14,2),(15,2),(17,1),(18,0),(19,0),(82,5),(83,5),(86,5),(87,5),(107,5),(111,5),(131,1),(135,1),(139,7),(143,7),(145,1),(147,1),(153,1),(175,3),(179,5),(183,9),(185,3),(193,1),(203,1),(207,1)]),([7,v0,v3,v1,v1,v2,v4],[(2,5),(3,5),(5,5),(10,2),(11,2),(18,0),(19,0),(21,0),(82,5),(83,5),(86,5),(87,5),(135,1),(139,5),(143,7),(171,0),(175,3),(179,6),(183,9),(185,0),(187,0),(189,0),(191,0),(207,2)]),([7,v0,v3,v1,vf,v2,v4],[(2,5),(3,5),(5,5),(10,2),(11,2),(14,8),(15,8),(17,1),(18,0),(19,0),(21,3),(57,5),(82,2),(87,5),(110,5),(111,5),(135,1),(143,7),(145,2),(157,1),(159,1),(171,0),(175,3),(179,0),(183,9),(185,4),(187,0),(191,0),(193,0),(195,0),(197,3),(199,3),(207,2)]),([7,v0,v3,v1,v2,v7,v4],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(18,3),(19,3),(21,3),(74,2),(82,8),(83,5),(87,5),(98,0),(99,1),(103,1),(106,6),(107,7),(111,7),(117,1),(138,5),(139,5),(142,5),(143,5),(158,1),(159,1),(171,3),(175,3),(179,9),(183,9),(189,3),(191,0),(195,1),(197,4),(199,2),(205,3),(207,3)]),([7,v0,v3,v1,v2,v4],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(131,3),(135,3),(139,9),(143,9),(147,0),(151,0),(155,2),(159,2)])]

def K_29 : List (List Nat × List (Nat × Nat)) := [([8,v0,v3,v1,v2,v4],[(2,5),(3,5),(5,5),(10,2),(11,2),(13,1),(14,0),(15,0),(17,3),(83,5),(87,5),(99,1),(103,1),(107,7),(111,7),(131,3),(135,3),(139,9),(143,9),(147,0),(151,0),(155,2),(159,2)])]

def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,v0,v15,v11] BT.lf) [2,v0,4241288396,v11] BT.lf) [2,v0,4241292492,4294962912] (BT.nd BT.lf [2,v0,4243385580,v11] BT.lf)) [2,4205488810,v15,v11] (BT.nd (BT.nd BT.lf [3,1886417008,v5,v2,v9] BT.lf) [3,v0,v3,v18,v11] (BT.nd BT.lf [3,v0,v3,4026532080,vd] BT.lf))) [3,v0,v3,4026572800,v11] (BT.nd (BT.nd (BT.nd BT.lf [3,v0,v3,v6,4294905840] BT.lf) [3,v0,v3,v6,4294962912] (BT.nd BT.lf [3,v0,v3,4026597360,v4] BT.lf)) [3,v0,v3,4037058720,v11] (BT.nd (BT.nd BT.lf [3,v0,v3,4041269472,vd] BT.lf) [3,v0,v3,v1b,4294962688] (BT.nd BT.lf [3,v0,v3,v1,4293848576] BT.lf)))) [3,v0,v3,4205488810,v11] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,v0,4007718624,4241292492,v4] BT.lf) [3,v0,v18,v15,v11] (BT.nd BT.lf [3,v0,v6,v15,v11] BT.lf)) [3,v0,v1,v15,vd] (BT.nd (BT.nd BT.lf [3,v0,v1,v15,v11] BT.lf) [3,v0,v1,4241288396,vd] (BT.nd BT.lf [3,v0,v1,4243385580,vd] BT.lf))) [3,v0,v1,4274834636,vd] (BT.nd (BT.nd (BT.nd BT.lf [3,v0,v1,4274843340,vd] BT.lf) [3,v0,v15,4293980400,vd] (BT.nd BT.lf [3,v0,v15,v7,v14] BT.lf)) [3,v0,v15,v7,v11] (BT.nd (BT.nd BT.lf [3,v0,v15,v11] BT.lf) [3,v0,4241292492,v7,4294954176] (BT.nd BT.lf [3,v0,4241292492,v19,v11] BT.lf))))) [3,v0,4244438256,4291624908,v19] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,4008373994,4241292492,v7,v4] BT.lf) [3,4008373994,v1a,4291624908,v4] BT.lf) [3,4008636138,v1,v2,v19] (BT.nd BT.lf [3,v5,v6,v7,v9] BT.lf)) [3,v5,v6,4294508536,v4] (BT.nd (BT.nd BT.lf [3,v5,4034982016,4294508536,v4] BT.lf) [3,v5,v1b,v2,v9] (BT.nd BT.lf [3,v5,v1b,v13,v4] BT.lf))) [3,v5,v1,4270390920,v4] (BT.nd (BT.nd (BT.nd BT.lf [3,v5,v1,v2,4294901896] BT.lf) [3,v5,v1,v2,v9] (BT.nd BT.lf [3,v5,v1,v2,4294944904] BT.lf)) [3,v5,v1,v2,4294944936] (BT.nd (BT.nd BT.lf [3,v5,v1,v2,4294945448] BT.lf) [3,v5,v1,v2,4294961384] (BT.nd BT.lf [3,v5,v1,4286644096,v9] BT.lf)))) [3,v5,v1,4287137928,vd] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,v5,v1,4287168256,v9] BT.lf) [3,v5,v1,v13,v9] (BT.nd BT.lf [3,v5,v1,v13,v10] BT.lf)) [3,v5,v1,v13,4294945280] (BT.nd (BT.nd BT.lf [3,v5,v1,v13,4294945416] BT.lf) [3,v5,v1,v13,4294959328] (BT.nd BT.lf [3,v5,v1,v13,4294962688] BT.lf))) [3,v5,v1,v13,4294962824] (BT.nd (BT.nd (BT.nd BT.lf [3,v5,v1,4289265576,4294944936] BT.lf) [3,v5,v1,4289383560,vd] (BT.nd BT.lf [3,v5,v16,v13,v9] BT.lf)) [3,v1,4205488810,v15,vd] (BT.nd (BT.nd BT.lf [4,30583,v5,v1,v2] BT.lf) [4,30583,v5,v1,v2,v9] (BT.nd BT.lf [4,34952,v5,v1,v2,v4] BT.lf)))))) [4,43690,4008627404,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,61680,v0,v3,4026597120,v4] BT.lf) [4,65520,v0,v3,v6,v4] BT.lf) [4,v8,4008618666,v1,v2,v19] (BT.nd BT.lf [4,v8,v5,v1,v2,v9] BT.lf)) [4,v8,v5,v1,v13] (BT.nd (BT.nd BT.lf [4,v8,v5,v1,v13,v4] BT.lf) [4,16776960,v0,v3,v1,4278190080] (BT.nd BT.lf [4,178956970,v3,v1,v2,v4] BT.lf))) [4,269545712,v0,v3,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,286331153,v5,v1,v2,v9] BT.lf) [4,286331153,v1,v2,v9] (BT.nd BT.lf [4,572662306,v3,v1,v2,v9] BT.lf)) [4,572662442,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [4,572697258,808513776,v3,v2,v4] BT.lf) [4,572697258,v3,v1,v2,v4] (BT.nd BT.lf [4,572697258,v3,v1,4291624704,v4] BT.lf)))) [4,581610154,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,805318656,v0,v3,v7,v4] BT.lf) [4,808464432,v0,v3,v2,4294951104] (BT.nd BT.lf [4,808464432,v3,3941264106,v2,v4] BT.lf)) [4,808464624,v0,v3,v2,v4] (BT.nd (BT.nd BT.lf [4,808480880,v0,v3,v2,v4] BT.lf) [4,808513776,855703296,v0,v3,v4] (BT.nd BT.lf [4,808513776,v0,v3,v2,v4] BT.lf))) [4,808513776,v0,v3,4291624704,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,808513776,v3,4008618666,v2,v4] BT.lf) [4,821096688,v0,v3,v2,v4] (BT.nd BT.lf [4,va,v5,v1,v2,v9] BT.lf)) [4,1717986918,vb,v1,v2,v4] (BT.nd (BT.nd BT.lf [4,1886417008,1996519168,v0,v3,v4] BT.lf) [4,1886417008,vb,v5,v2,v4] (BT.nd BT.lf [4,1886417008,v0,v3,v2,v4] BT.lf))))) [4,1886417008,v0,v3,v2,v9] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1886449904,v0,v3,v2,v4] BT.lf) [4,2004318071,v5,v1,v2,v9] (BT.nd BT.lf [4,2155905152,v5,v1,v2,v9] BT.lf)) [4,2155905152,v5,v16,v2,v4] (BT.nd (BT.nd BT.lf [4,vb,v5,v6,v7,v4] BT.lf) [4,vb,v5,v1b,v2,v4] (BT.nd BT.lf [4,vb,v5,v1,v2,v4] BT.lf))) [4,vb,v5,v1,v2,4294934656] (BT.nd (BT.nd (BT.nd BT.lf [4,vb,v5,v1,v2,v9] BT.lf) [4,vb,v5,v1,v2,v10] (BT.nd BT.lf [4,vb,v5,v1,v2,4294959328] BT.lf)) [4,vb,v5,v1,v13,v9] (BT.nd (BT.nd BT.lf [4,2576980377,v5,v1,v2,v4] BT.lf) [4,vc,v5,v1,v2,v9] (BT.nd BT.lf [4,vc,v5,v16,v2,v4] BT.lf)))) [4,2728569514,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2827528328,v5,v1,v2,v4] BT.lf) [4,2829625512,v5,v1,v2,v4] (BT.nd BT.lf [4,2829625512,v5,v1,v2,4294944936] BT.lf)) [4,2829625512,v5,v16,v2,v4] (BT.nd (BT.nd BT.lf [4,2862656160,v3,4205509290,v7,v4] BT.lf) [4,2862656160,v3,vf,v1c,v4] (BT.nd BT.lf [4,2863180456,v5,v1,v2,v4] BT.lf))) [4,2863311520,v3,v1,v2,v12] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311528,v3,v1,v2,v4] BT.lf) [4,v0,2964386032,v3,v2,v4] (BT.nd BT.lf [4,v0,v3,3772834016,4261477888,v4] BT.lf)) [4,v0,v3,4007718624,v6,v4] (BT.nd (BT.nd BT.lf [4,v0,v3,v18,v6,v11] BT.lf) [4,v0,v3,v18,v1,vd] (BT.nd BT.lf [4,v0,v3,v18,v1,v11] BT.lf))))))) [4,v0,v3,v18,4293980400,vd] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v18,v7,v14] BT.lf) [4,v0,v3,v18,v7,v11] BT.lf) [4,v0,v3,v18,v11] (BT.nd BT.lf [4,v0,v3,4026572800,v1,vd] BT.lf)) [4,v0,v3,4026572800,v7,v4] (BT.nd (BT.nd BT.lf [4,v0,v3,v6,4042260480,v11] BT.lf) [4,v0,v3,v6,v1,4294905600] (BT.nd BT.lf [4,v0,v3,v6,v1,4294962688] BT.lf))) [4,v0,v3,v6,4042326000,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v6,4277206768,v4] BT.lf) [4,v0,v3,v6,4293918720,v11] (BT.nd BT.lf [4,v0,v3,v6,v7,v4] BT.lf)) [4,v0,v3,v6,v7,v9] (BT.nd (BT.nd BT.lf [4,v0,v3,v6,v7,4294942720] BT.lf) [4,v0,v3,v6,v7,v10] (BT.nd BT.lf [4,v0,v3,v6,v7,4294945440] BT.lf)))) [4,v0,v3,v6,4294508536,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v6,4294639600,v4] BT.lf) [4,v0,v3,v6,v4,v11] (BT.nd BT.lf [4,v0,v3,v6,v12,v11] BT.lf)) [4,v0,v3,4026593520,v2,v4] (BT.nd (BT.nd BT.lf [4,v0,v3,4026593520,4278255600,v4] BT.lf) [4,v0,v3,4026593520,v7,v4] (BT.nd BT.lf [4,v0,v3,4026593520,v4,vd] BT.lf))) [4,v0,v3,4026597375,v7,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,4027576335,v7,v4] BT.lf) [4,v0,v3,4029739248,v2,v4] (BT.nd BT.lf [4,v0,v3,4033933424,v2,v4] BT.lf)) [4,v0,v3,4034982016,v7,v4] (BT.nd (BT.nd BT.lf [4,v0,v3,4034982016,4294508536,v4] BT.lf) [4,v0,v3,4037058720,v1,vd] (BT.nd BT.lf [4,v0,v3,4037058720,v2,v14] BT.lf))))) [4,v0,v3,4037079040,v7,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,4037079040,4294639600,v4] BT.lf) [4,v0,v3,v1d,v2,4294951104] BT.lf) [4,v0,v3,v1d,4290838464,v4] (BT.nd BT.lf [4,v0,v3,v1d,v7,v4] BT.lf)) [4,v0,v3,v1d,v4,v11] (BT.nd (BT.nd BT.lf [4,v0,v3,4037079280,v2,v4] BT.lf) [4,v0,v3,4041269472,v2,v4] (BT.nd BT.lf [4,v0,v3,v1b,v2,4293787648] BT.lf))) [4,v0,v3,v1b,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1b,v17,v4] BT.lf) [4,v0,v3,v1b,4292935648,v4] (BT.nd BT.lf [4,v0,v3,v1b,v7,v4] BT.lf)) [4,v0,v3,v1b,v4,vd] (BT.nd (BT.nd BT.lf [4,v0,v3,4042322144,v2,v4] BT.lf) [4,v0,v3,v1,4205488810,vd] (BT.nd BT.lf [4,v0,v3,v1,v2,v4] BT.lf)))) [4,v0,v3,v1,v2,4294901777] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v2,4294901808] BT.lf) [4,v0,v3,v1,v2,4294901896] (BT.nd BT.lf [4,v0,v3,v1,v2,4294901920] BT.lf)) [4,v0,v3,v1,v2,4294902000] (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v2,4294909984] BT.lf) [4,v0,v3,v1,v2,4294934528] (BT.nd BT.lf [4,v0,v3,v1,v2,4294934656] BT.lf))) [4,v0,v3,v1,v2,4294936704] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v2,v9] BT.lf) [4,v0,v3,v1,v2,4294942720] (BT.nd BT.lf [4,v0,v3,v1,v2,4294942848] BT.lf)) [4,v0,v3,v1,v2,v10] (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v2,4294942960] BT.lf) [4,v0,v3,v1,v2,4294944904] (BT.nd BT.lf [4,v0,v3,v1,v2,4294944928] BT.lf)))))) [4,v0,v3,v1,v2,4294944936] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v2,4294945440] BT.lf) [4,v0,v3,v1,v2,4294945448] BT.lf) [4,v0,v3,v1,v2,4294959104] (BT.nd BT.lf [4,v0,v3,v1,v2,4294959264] BT.lf)) [4,v0,v3,v1,v2,4294959328] (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v2,4294961856] BT.lf) [4,v0,v3,v1,v2,4294962912] (BT.nd BT.lf [4,v0,v3,v1,4279238400,4294905615] BT.lf))) [4,v0,v3,v1,4279238400,v12] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1,4286644096,4294934656] BT.lf) [4,v0,v3,v1,4286644096,v9] (BT.nd BT.lf [4,v0,v3,v1,4286644096,v10] BT.lf)) [4,v0,v3,v1,4287137928,vd] (BT.nd (BT.nd BT.lf [4,v0,v3,v1,4287168256,v9] BT.lf) [4,v0,v3,v1,v13,v9] (BT.nd BT.lf [4,v0,v3,v1,v13,v10] BT.lf)))) [4,v0,v3,v1,v13,4294945280] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v13,4294945416] BT.lf) [4,v0,v3,v1,4288716960,vd] (BT.nd BT.lf [4,v0,v3,v1,4288741120,v10] BT.lf)) [4,v0,v3,v1,v17,v10] (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v17,4294945280] BT.lf) [4,v0,v3,v1,v17,4294945440] (BT.nd BT.lf [4,v0,v3,v1,v17,4294951104] BT.lf))) [4,v0,v3,v1,v17,4294953984] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v17,4294954112] BT.lf) [4,v0,v3,v1,4289265576,4294944936] (BT.nd BT.lf [4,v0,v3,v1,4289374720,vd] BT.lf)) [4,v0,v3,v1,4289374890,vd] (BT.nd (BT.nd BT.lf [4,v0,v3,v1,4289374890,v11] BT.lf) [4,v0,v3,v1,4289383560,vd] (BT.nd BT.lf [4,v0,v3,v1,4289392298,vd] BT.lf))))) [4,v0,v3,v1,4289396480,4294945280] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v1,4289396480,v12] BT.lf) [4,v0,v3,v1,4289396480,4294953984] (BT.nd BT.lf [4,v0,v3,v1,4289396616,v12] BT.lf)) [4,v0,v3,v1,4289396640,v12] (BT.nd (BT.nd BT.lf [4,v0,v3,v1,v1c,4294962688] BT.lf) [4,v0,v3,v1,4292935648,4294959328] (BT.nd BT.lf [4,v0,v3,v1,4293848814,vd] BT.lf))) [4,v0,v3,v1,4293852928,4294962926] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v3,v16,v13,v9] BT.lf) [4,v0,v3,4210096880,v1c,4294945280] (BT.nd BT.lf [4,v0,3435982060,v1,v2,v4] BT.lf)) [4,v0,3972844748,v1,v2,v4] (BT.nd (BT.nd BT.lf [4,v0,3972852940,v6,v7,v4] BT.lf) [4,v0,3972852940,v1,v2,v4] (BT.nd BT.lf [4,v0,3972852940,v1,v2,4294942720] BT.lf)))) [4,v0,3972852940,v1,v2,v10] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,3972852940,v1,v17,v4] BT.lf) [4,v0,3974950092,v1,v2,v4] (BT.nd BT.lf [4,v0,ve,v6,v7,v4] BT.lf)) [4,v0,ve,4039176384,v2,v4] (BT.nd (BT.nd BT.lf [4,v0,ve,v1b,v2,v4] BT.lf) [4,v0,ve,v1,4278190080,vd] (BT.nd BT.lf [4,v0,ve,v1,v2,v4] BT.lf))) [4,v0,ve,v1,v2,4294934656] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,ve,v1,v2,v9] BT.lf) [4,v0,ve,v1,v2,4294942720] (BT.nd BT.lf [4,v0,ve,v1,v2,v10] BT.lf)) [4,v0,ve,v1,v2,4294944936] (BT.nd (BT.nd BT.lf [4,v0,ve,v1,v2,4294945280] BT.lf) [4,v0,ve,v1,v2,4294951104] (BT.nd BT.lf [4,v0,ve,v1,v2,4294953984] BT.lf)))))))) [4,v0,ve,v1,v2,4294959328] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,ve,v1,v2,4294962176] BT.lf) [4,v0,ve,v1,v17,v10] BT.lf) [4,v0,ve,v16,v2,v4] (BT.nd BT.lf [4,v0,ve,4210096880,v2,v4] BT.lf)) [4,v0,ve,vf,v2,v4] (BT.nd (BT.nd BT.lf [4,v0,ve,vf,v2,v10] BT.lf) [4,v0,ve,4243651824,v2,v4] (BT.nd BT.lf [4,v0,4008504556,v1,v2,v4] BT.lf))) [4,v0,4008505068,v6,v7,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,4008505068,v1,v2,v4] BT.lf) [4,v0,4008505068,v1,v2,4294945440] (BT.nd BT.lf [4,v0,4008505068,v1,v17,v4] BT.lf)) [4,v0,4008505068,v1,v1c,v4] (BT.nd (BT.nd BT.lf [4,v0,4008636140,v1,v2,v4] BT.lf) [4,v0,v5,v1,v2,v9] (BT.nd BT.lf [4,v0,v5,v1,v2,4294944936] BT.lf)))) [4,v0,v5,v1,v2,4294953160] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v5,v1,v13,v9] BT.lf) [4,v0,v5,v1,4291611852,vd] (BT.nd BT.lf [4,v0,v5,v1,4291624704,v19] BT.lf)) [4,v0,v5,v1,4291624908,4294962688] (BT.nd (BT.nd BT.lf [4,v0,v18,v1,v15,vd] BT.lf) [4,v0,v6,v1,v15,vd] (BT.nd BT.lf [4,v0,v6,v15,v7,v4] BT.lf))) [4,v0,v1,v15,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,v0,v1,v15,v2,4294963200] BT.lf) [4,v0,v1,v15,v2,v14] (BT.nd BT.lf [4,v0,v1,v15,vd] BT.lf)) [4,v0,v1,4241288396,v2,v4] (BT.nd (BT.nd BT.lf [4,v0,v1,4241292492,v19,vd] BT.lf) [4,v0,v1,4243385580,v2,v4] (BT.nd BT.lf [4,v0,v1,v1a,4291611852,vd] BT.lf))))) [4,3772834016,v5,v1,v2,v9] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,3772834016,v5,v16,v2,v4] BT.lf) [4,3907578088,v5,v1,v2,v4] BT.lf) [4,3907578088,v5,v16,v2,v4] (BT.nd BT.lf [4,3941264106,ve,v1,v2,v4] BT.lf)) [4,3941264106,4006407884,v1,v2,v4] (BT.nd (BT.nd BT.lf [4,3941264106,v5,v1a,v2,v4] BT.lf) [4,v5,v5,v1,v2,v9] (BT.nd BT.lf [4,v5,v6,v1,v2,v9] BT.lf))) [4,v5,v6,v1,v13,v4] (BT.nd (BT.nd (BT.nd BT.lf [4,v5,4034982016,v1,v13,v4] BT.lf) [4,v5,v1,v1,v2,v9] (BT.nd BT.lf [4,v5,v1,4169726088,v2,v4] BT.lf)) [4,v5,v1,v16,v2,v4] (BT.nd (BT.nd BT.lf [4,v5,v1,v16,v2,v9] BT.lf) [4,v5,v1,4207475400,v2,v4] (BT.nd BT.lf [4,v5,v1,4210621176,v2,v4] BT.lf)))) [4,v5,v1,vf,v2,v9] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,v5,v1,vf,v2,4294953160] BT.lf) [4,v5,v1,4278124286,v2,v9] (BT.nd BT.lf [4,v5,v1,v2,v7,v9] BT.lf)) [4,v5,v1,v2,4294508536,v4] (BT.nd (BT.nd BT.lf [4,v5,v1,v2,v9] BT.lf) [4,v5,v1,v2,v9,v9] (BT.nd BT.lf [4,v5,v1,v2,v9,v12] BT.lf))) [4,v5,v1,v2,v9,4294962926] (BT.nd (BT.nd (BT.nd BT.lf [4,v5,v1,v2,v9,v14] BT.lf) [4,v5,v1,v2,v9,4294965496] (BT.nd BT.lf [4,v5,v1,v2,4294944936] BT.lf)) [4,v5,v1,v2,v12,v19] (BT.nd (BT.nd BT.lf [4,v5,v1,v2,v12,4294966524] BT.lf) [4,v5,v1,v13,v9] (BT.nd BT.lf [4,v5,v1,v1c,v19,vd] BT.lf)))))) [4,v1,4205488810,v15,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,0,v0,v3,v1,v2,v4] BT.lf) [5,15,v0,v3,v1,v2,v4] BT.lf) [5,51,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,170,v0,v3,v1,v2,v4] BT.lf)) [5,240,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,255,v0,v3,v1,4278190080] BT.lf) [5,255,v0,v3,v1,4278190080,vd] (BT.nd BT.lf [5,255,v0,v3,v1,v2,v4] BT.lf))) [5,4095,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,4369,v0,v3,v1,v2,v4] BT.lf) [5,8738,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,12336,v0,v3,v1,v2,v4] BT.lf)) [5,13107,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,13311,v0,v3,v1,v2] BT.lf) [5,13311,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,13311,v0,v3,v1,v2,4294953984] BT.lf)))) [5,30583,v0,v3,v1,v2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,30583,v0,v3,v1,v2,v4] BT.lf) [5,30583,v0,v3,v1,v2,v9] (BT.nd BT.lf [5,34952,v0,v3,v1,v2,v4] BT.lf)) [5,41120,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,43690,2863267840,v3,v1,v2,v4] BT.lf) [5,43690,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,43690,2863333375,v3,v1,v2,v4] BT.lf))) [5,43690,v3,v5,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,61166,v0,v3,v1,v2,v4] BT.lf) [5,61440,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,61680,v0,v3,v6,v2,v4] BT.lf)) [5,61680,v0,v3,4042260480,v2,v4] (BT.nd (BT.nd BT.lf [5,61680,v0,v3,v1,v2,v4] BT.lf) [5,61680,v0,v3,v1,4278255600,v4] (BT.nd BT.lf [5,61680,v0,v3,4042326015,v2,v4] BT.lf))))) [5,61680,v0,v3,vf,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,64250,v0,v3,v1,v2,v4] BT.lf) [5,65520,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,v8,16711935,252645135,v0,v3] BT.lf)) [5,v8,16711935,va,v0,v1] (BT.nd (BT.nd BT.lf [5,v8,16711935,v0,v3,v1] BT.lf) [5,v8,va,1431655765,v1,v2] (BT.nd BT.lf [5,v8,va,v0,v1,v2] BT.lf))) [5,v8,vb,v5,v1,v2] (BT.nd (BT.nd (BT.nd BT.lf [5,v8,vb,v5,v1,v2,v4] BT.lf) [5,v8,2863267840,v3,v1,v2,v12] (BT.nd BT.lf [5,v8,v0,v3,v6,v7] BT.lf)) [5,v8,v0,v3,v6,v7,v4] (BT.nd (BT.nd BT.lf [5,v8,v0,v3,4026593520,v2] BT.lf) [5,v8,v0,v3,4026593520,v2,v4] (BT.nd BT.lf [5,v8,v0,v3,4042260480,v2,v14] BT.lf)))) [5,v8,v0,v3,v1,v2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v8,v0,v3,v1,v2,v4] BT.lf) [5,v8,v0,v3,v1,v2,v9] (BT.nd BT.lf [5,v8,v0,v3,v1,v2,v10] BT.lf)) [5,v8,v0,v3,v1,4278255600] (BT.nd (BT.nd BT.lf [5,v8,v0,v3,v1,4278255600,v4] BT.lf) [5,v8,v0,v3,v1,v13] (BT.nd BT.lf [5,v8,v0,v3,v1,v13,v4] BT.lf))) [5,v8,v0,v3,v1,v17] (BT.nd (BT.nd (BT.nd BT.lf [5,v8,v0,v3,v1,v17,v4] BT.lf) [5,v8,v0,v3,v1,4289396480] (BT.nd BT.lf [5,v8,v0,v3,v1,4289396480,v4] BT.lf)) [5,v8,v0,ve,v1,v2] (BT.nd (BT.nd BT.lf [5,v8,v0,ve,v1,v2,v4] BT.lf) [5,v8,v0,4008627404,v1,v2] (BT.nd BT.lf [5,v8,v0,4008627404,v1,v2,v4] BT.lf))))))) [5,1048575,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3355443,v0,v3,v1,v2,v4] BT.lf) [5,3407871,v0,v3,v1,v2,v4] BT.lf) [5,11184810,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,15790320,v0,v3,v1,v2,v4] BT.lf)) [5,16777215,v0,v3,v1,4278190080,vd] (BT.nd (BT.nd BT.lf [5,16777215,v0,v3,v1,v2,v4] BT.lf) [5,16777215,v0,v3,v1,vd] (BT.nd BT.lf [5,268435455,v0,v3,v1,v2,v4] BT.lf))) [5,269488144,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,286331153,vb,v5,v1,v2,v4] BT.lf) [5,286331153,vb,v1,v2,v4] (BT.nd BT.lf [5,286331153,v0,v3,v1,v2,v4] BT.lf)) [5,286339891,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,286339891,v0,4008627404,v1,v2,v4] BT.lf) [5,286339891,v0,v1,v2,v4] (BT.nd BT.lf [5,286392319,v0,v3,v1,v2,v4] BT.lf)))) [5,538976288,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,572662306,vb,v3,v1,v2,v4] BT.lf) [5,572662306,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,572662306,3149642683,v3,v1,v2,v4] BT.lf)) [5,572662306,v3,v1,vf,v2,v4] (BT.nd (BT.nd BT.lf [5,572697258,859045887,v3,v1,v2,v4] BT.lf) [5,572697258,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,572697258,3435921408,v3,v1,v2,v4] BT.lf))) [5,572697258,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,805318656,v0,v3,v1,v2,v4] BT.lf) [5,808464432,v0,3233857728,v3,v2,v4] (BT.nd BT.lf [5,808464432,v0,v3,v1,v2,v4] BT.lf)) [5,808464432,v0,v3,4092851187,v2,v4] (BT.nd (BT.nd BT.lf [5,808464432,v0,v3,vf,v2,v4] BT.lf) [5,808464432,v0,v3,v2,v7,v4] (BT.nd BT.lf [5,808513776,859045887,v0,v3,v2,v4] BT.lf))))) [5,808513776,v0,3435921408,v3,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,808513776,v0,v3,v1,v2,v4] BT.lf) [5,808513776,v0,v3,v2,v4] (BT.nd BT.lf [5,842150450,v0,v3,v1,v2,v4] BT.lf)) [5,858796848,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,va,1431655765,v1,v2,v4] BT.lf) [5,va,vb,v5,v1,v2,v4] (BT.nd BT.lf [5,va,v0,v3,v6,v7,v4] BT.lf))) [5,va,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,va,v0,v3,v1,v2,v9] BT.lf) [5,va,v0,v3,v1,v2,v10] (BT.nd BT.lf [5,va,v0,v3,v1,v2,4294951104] BT.lf)) [5,va,v0,ve,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,va,v0,v6,v7,v4] BT.lf) [5,va,v0,v1,v2,v4] (BT.nd BT.lf [5,va,v0,v1,v2,v9] BT.lf)))) [5,va,v0,v1,v2,v10] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,va,v0,v1,v2,4294951104] BT.lf) [5,va,v3,3941264106,v1,v2,v4] (BT.nd BT.lf [5,va,3941264106,v1,v2,v4] BT.lf)) [5,858993663,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,859010935,v0,v3,v1,v2,v4] BT.lf) [5,859045887,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,859045887,v0,v3,v1,4291624704,v4] BT.lf))) [5,859045887,v3,4008618666,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,872415231,v0,v3,v1,v2,v4] BT.lf) [5,1886417008,2004318071,v0,v3,v2,v4] (BT.nd BT.lf [5,1886417008,vb,v0,v3,v2,v4] BT.lf)) [5,1886417008,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,1886417008,v0,v3,v2,v4] BT.lf) [5,2004318071,vb,v5,v1,v2,v4] (BT.nd BT.lf [5,2004318071,v0,v3,v1,v2,v4] BT.lf)))))) [5,2004318071,v0,v3,v1,v2,v9] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2004318071,v5,v1,v2,v4] BT.lf) [5,2004353023,v0,v3,v1,v2,v4] BT.lf) [5,2147516416,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,2155905152,vb,v5,v1,v2,v4] BT.lf)) [5,2155905152,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,2155905152,v0,v3,v1,v2,4294934656] BT.lf) [5,2155905152,v0,v3,v1,v2,v9] (BT.nd BT.lf [5,2155905152,v0,v3,v1,v2,v10] BT.lf))) [5,2155905152,v0,v3,v16,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,2155905152,v0,ve,v1,v2,v4] BT.lf) [5,2290124928,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,vb,vb,v5,v1,v2,v4] BT.lf)) [5,vb,vc,v5,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,vb,v0,v3,v6,v7,v4] BT.lf) [5,vb,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,vb,v0,v3,v1,v2,4294934656] BT.lf)))) [5,vb,v0,v3,v1,v2,v9] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,vb,v0,v3,v1,v2,v10] BT.lf) [5,vb,v0,v3,v1,v13,v9] (BT.nd BT.lf [5,vb,v0,ve,v1,v2,v4] BT.lf)) [5,vb,v0,v5,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,vb,v0,v5,v1,v2,v9] BT.lf) [5,vb,3772834016,v5,v1,v2,v4] (BT.nd BT.lf [5,vb,v5,v5,v1,v2,v4] BT.lf))) [5,vb,v5,v6,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,vb,v5,v1,v1,v2,v4] BT.lf) [5,vb,v5,v1,v16,v2,v4] (BT.nd BT.lf [5,vb,v5,v1,vf,v2,v4] BT.lf)) [5,vb,v5,v1,4278124286,v2,v4] (BT.nd (BT.nd BT.lf [5,vb,v5,v1,v2,v7,v4] BT.lf) [5,vb,v5,v1,v2,v4] (BT.nd BT.lf [5,vb,v5,v1,v2,v9] BT.lf))))) [5,2290657962,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290679807,v0,v3,v1,v2] BT.lf) [5,2290679807,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,2684354560,v0,v3,v1,v2,v4] BT.lf)) [5,2684395520,v0,v3,v6,v7,v4] (BT.nd (BT.nd BT.lf [5,2684395520,v0,v3,v1,v2,v4] BT.lf) [5,2684395520,v0,v3,v1,v2,4294942720] (BT.nd BT.lf [5,2684395520,v0,v3,v1,v2,v10] BT.lf))) [5,2684395520,v0,v3,v1,v17,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,2684395520,v0,3972852940,v1,v2,v4] BT.lf) [5,2684395520,v0,ve,v1,v2,v4] (BT.nd BT.lf [5,2692784256,v0,v3,v1,v2,v4] BT.lf)) [5,2694881280,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,vc,v0,v3,v6,v7,v4] BT.lf) [5,vc,v0,v3,4039176384,v2,v4] (BT.nd BT.lf [5,vc,v0,v3,v1,4278190080,vd] BT.lf)))) [5,vc,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,vc,v0,v3,v1,v2,4294934656] BT.lf) [5,vc,v0,v3,v1,v2,v9] (BT.nd BT.lf [5,vc,v0,v3,v1,v2,4294942720] BT.lf)) [5,vc,v0,v3,v1,v2,v10] (BT.nd (BT.nd BT.lf [5,vc,v0,v3,v1,v2,4294945280] BT.lf) [5,vc,v0,v3,v1,v2,4294951104] (BT.nd BT.lf [5,vc,v0,v3,v1,v2,4294953984] BT.lf))) [5,vc,v0,v3,v1,v17,v10] (BT.nd (BT.nd (BT.nd BT.lf [5,vc,v0,v3,v16,v2,v4] BT.lf) [5,vc,v0,v3,4210096880,v2,v4] (BT.nd BT.lf [5,vc,v0,v3,vf,v2,v4] BT.lf)) [5,vc,v0,v3,vf,v2,v10] (BT.nd (BT.nd BT.lf [5,vc,v0,v3,4243651824,v2,v4] BT.lf) [5,vc,v0,3972852940,v1,v2,v4] (BT.nd BT.lf [5,vc,v0,ve,v1,v2,v4] BT.lf))))))))) [5,vc,v0,ve,v1,v2,v10] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,vc,v0,ve,vf,v2,v4] BT.lf) [5,vc,v0,4006407884,v1,v2,v4] BT.lf) [5,vc,v3,3941264106,v1,v2,v4] (BT.nd BT.lf [5,vc,v3,4004179626,v1,v2,v4] BT.lf)) [5,vc,v3,v5,vf,v2,v4] (BT.nd (BT.nd BT.lf [5,2694884010,v0,v3,v1,v2,v4] BT.lf) [5,2694902000,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,2694905855,v0,v3,v1,v2] BT.lf))) [5,2694905855,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,2728567458,v0,v3,v1,v2,v4] BT.lf) [5,2827528328,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,2829101216,v0,v3,v1,v2,v4] BT.lf)) [5,2829101216,v0,v3,4243651824,v2,v4] (BT.nd (BT.nd BT.lf [5,2829625512,v0,v3,v1,v2,v4] BT.lf) [5,2829625512,v0,v3,v1,v2,4294944936] (BT.nd BT.lf [5,2829625512,v0,v3,v16,v2,v4] BT.lf)))) [5,2829625512,v0,v3,vf,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,v0,ve,v1,v2,v4] BT.lf) [5,2829625512,v0,v5,v1,v2,v4] (BT.nd BT.lf [5,2829625512,v3,v5,v1,v2,v4] BT.lf)) [5,2829625512,v5,v1,v1a,v2,v4] (BT.nd (BT.nd BT.lf [5,2829625512,v5,v1,v2,v4] BT.lf) [5,2862653600,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,2862656160,v0,v3,v6,v7,v4] BT.lf))) [5,2862656160,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,2862656160,v0,v3,v1,v2,4294945440] BT.lf) [5,2862656160,v0,v3,v1,v17,v4] (BT.nd BT.lf [5,2862656160,v0,v3,v1,v1c,v4] BT.lf)) [5,2862656160,v0,4008505068,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,2863180456,v0,v3,v1,v2,v4] BT.lf) [5,2863311520,v0,v3,v1,v2,v4] (BT.nd BT.lf [5,v0,v0,v3,v6,v7,v4] BT.lf))))) [5,v0,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v0,v3,v1,v2,v9] BT.lf) [5,v0,v0,v3,v1,v2,v10] BT.lf) [5,v0,v0,v3,v1,v2,4294951104] (BT.nd BT.lf [5,v0,v0,ve,v1,v2,v4] BT.lf)) [5,v0,2863311615,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,2863315899,v3,v1,v2,v4] BT.lf) [5,v0,2863329006,v3,v1,v2,v4] (BT.nd BT.lf [5,v0,2863332090,v3,v1,v2,v4] BT.lf))) [5,v0,2863333375,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,2868903935,v3,v1,v2,v4] BT.lf) [5,v0,2964369584,v3,v1,v2,v4] (BT.nd BT.lf [5,v0,3014898611,v3,v1,v2,v4] BT.lf)) [5,v0,3014898611,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,3132799674,v3,v1,v2,v4] BT.lf) [5,v0,3149642683,v3,v1,v2,v4] (BT.nd BT.lf [5,v0,3149660159,v3,v1,v2,v4] BT.lf)))) [5,v0,v3,3758153728,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,3768639648,v1,v2,v4] BT.lf) [5,v0,v3,3772834016,v6,v2,v4] (BT.nd BT.lf [5,v0,v3,3772834016,v1,v2,v4] BT.lf)) [5,v0,v3,3772834016,v1,v2,4294959328] (BT.nd (BT.nd BT.lf [5,v0,v3,3772834016,vf,v2,v4] BT.lf) [5,v0,v3,3772834016,4278124286,v2,v4] (BT.nd BT.lf [5,v0,v3,3937069738,v1,v2,v4] BT.lf))) [5,v0,v3,3938511552,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,3941264106,v1,v2,v4] BT.lf) [5,v0,v3,3941264106,v1,v2,4294951104] (BT.nd BT.lf [5,v0,v3,3941264106,v1a,v2,v4] BT.lf)) [5,v0,v3,4007718624,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,4008373994,v1,v2,v4] BT.lf) [5,v0,v3,v5,v6,v7,v4] (BT.nd BT.lf [5,v0,v3,v5,v1b,v2,v4] BT.lf)))))) [5,v0,v3,v5,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v5,v1,v2,v9] BT.lf) [5,v0,v3,v5,v1,v2,v10] BT.lf) [5,v0,v3,v5,v1,v2,4294959328] (BT.nd BT.lf [5,v0,v3,4008640511,v1,v2,v4] BT.lf)) [5,v0,v3,v18,v6,v1,vd] (BT.nd (BT.nd BT.lf [5,v0,v3,v18,v6,v7,v4] BT.lf) [5,v0,v3,v18,v1,v2,v4] (BT.nd BT.lf [5,v0,v3,v18,v1,v2,4294963200] BT.lf))) [5,v0,v3,v18,v1,v2,v14] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v18,v1,vd] BT.lf) [5,v0,v3,4026572800,v1,v2,v4] (BT.nd BT.lf [5,v0,v3,v6,v6,v7,v4] BT.lf)) [5,v0,v3,v6,4042260480,v1,vd] (BT.nd (BT.nd BT.lf [5,v0,v3,v6,4042260480,v2,v14] BT.lf) [5,v0,v3,v6,v1,v2,v4] (BT.nd BT.lf [5,v0,v3,v6,v1,v2,v9] BT.lf)))) [5,v0,v3,v6,v1,v2,4294942720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v6,v1,v2,v10] BT.lf) [5,v0,v3,v6,v1,v13,v4] (BT.nd BT.lf [5,v0,v3,v6,v1,v17,v4] BT.lf)) [5,v0,v3,v6,v1,4289396480,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v6,v1,4293984000,v4] BT.lf) [5,v0,v3,v6,v1,v7,v4] (BT.nd BT.lf [5,v0,v3,v6,v1,v4,vd] BT.lf))) [5,v0,v3,v6,v1,v4,v11] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v6,v1,v12,vd] BT.lf) [5,v0,v3,v6,4205509290,v7,v4] (BT.nd BT.lf [5,v0,v3,v6,vf,v7,v4] BT.lf)) [5,v0,v3,v6,4293918720,v7,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v6,v7,v7,v4] BT.lf) [5,v0,v3,v6,v7,4294639610,v4] (BT.nd BT.lf [5,v0,v3,v6,v7,v4] BT.lf))))) [5,v0,v3,v6,v7,v4,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v6,v7,v4,v12] BT.lf) [5,v0,v3,v6,v7,v4,4294963200] (BT.nd BT.lf [5,v0,v3,v6,v7,v4,v14] BT.lf)) [5,v0,v3,v6,v7,v4,v11] (BT.nd (BT.nd BT.lf [5,v0,v3,v6,v4,v14,vd] BT.lf) [5,v0,v3,v6,v4,v14,v11] (BT.nd BT.lf [5,v0,v3,v6,v4,v11] BT.lf))) [5,v0,v3,4026593520,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,4026593520,v2,4278255615,v4] BT.lf) [5,v0,v3,4026593520,v2,v4] (BT.nd BT.lf [5,v0,v3,4026597375,v1,v2,v4] BT.lf)) [5,v0,v3,4029739056,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,4034982016,v1,v2,v4] BT.lf) [5,v0,v3,4034982016,v1,v13,v4] (BT.nd BT.lf [5,v0,v3,4037058720,v1,v2,v4] BT.lf)))) [5,v0,v3,4037079040,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,4037079040,v1,4289396480,v4] BT.lf) [5,v0,v3,v1d,v1,v2,v4] (BT.nd BT.lf [5,v0,v3,v1d,v1,v17,v4] BT.lf)) [5,v0,v3,v1d,v1,v7,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v1d,v1,v4,vd] BT.lf) [5,v0,v3,v1d,vf,v2,v4] (BT.nd BT.lf [5,v0,v3,v1d,v2,v7,v4] BT.lf))) [5,v0,v3,v1d,v2,4294639610,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1d,v2,v4,v14] BT.lf) [5,v0,v3,v1d,v1c,v7,v4] (BT.nd BT.lf [5,v0,v3,v1d,v7,v4] BT.lf)) [5,v0,v3,v1b,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v1b,v2,v1c,v4] BT.lf) [5,v0,v3,v1b,v2,4293853166,v4] (BT.nd BT.lf [5,v0,v3,v1b,v2,v4] BT.lf))))))) [5,v0,v3,4042321920,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,4042321920,v2,v7,v4] BT.lf) [5,v0,v3,4042321920,v2,v4,v11] BT.lf) [5,v0,v3,4042322080,v1,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,v1,v2,v4] BT.lf)) [5,v0,v3,v1,v1,v2,v9] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v1,v2,v10] BT.lf) [5,v0,v3,v1,v1,v2,4294945280] (BT.nd BT.lf [5,v0,v3,v1,4042322175,v2,v4] BT.lf))) [5,v0,v3,v1,4042322931,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4042324730,v2,v4] BT.lf) [5,v0,v3,v1,4042326000,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,4042326015,v2,v4] BT.lf)) [5,v0,v3,v1,4043309055,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4059165169,v2,v4] BT.lf) [5,v0,v3,v1,4076008178,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,4080268083,v2,v4] BT.lf)))) [5,v0,v3,v1,4092654576,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4092851187,v2,v4] BT.lf) [5,v0,v3,v1,4092854271,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,4160223223,v2,v4] BT.lf)) [5,v0,v3,v1,4169726088,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4176541936,v2,v4] BT.lf) [5,v0,v3,v1,v16,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,v16,v2,v9] BT.lf))) [5,v0,v3,v1,4205488810,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4205506560,v2,v4] BT.lf) [5,v0,v3,v1,4205509290,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,4205509290,v7,v4] BT.lf)) [5,v0,v3,v1,4205509290,v4,vd] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4207475400,v2,v4] BT.lf) [5,v0,v3,v1,4209703658,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,4210094320,v2,v4] BT.lf))))) [5,v0,v3,v1,4210096880,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4210096880,v2,4294945280] BT.lf) [5,v0,v3,v1,4210096880,v1c,v4] BT.lf) [5,v0,v3,v1,4210621176,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,4210752000,v2,v4] BT.lf)) [5,v0,v3,v1,4210752170,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4210752240,v2,v4] BT.lf) [5,v0,v3,v1,vf,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,vf,v2,v9] BT.lf))) [5,v0,v3,v1,vf,v2,v10] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,vf,v2,4294945280] BT.lf) [5,v0,v3,v1,vf,v2,4294951104] (BT.nd BT.lf [5,v0,v3,v1,vf,v2,4294953160] BT.lf)) [5,v0,v3,v1,vf,v2,4294953984] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4210753535,v2,v4] BT.lf) [5,v0,v3,v1,4227595259,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,4277075694,v2,v4] BT.lf)))) [5,v0,v3,v1,4277206768,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4277862138,v2,v4] BT.lf) [5,v0,v3,v1,4278124286,v2,v4] (BT.nd BT.lf [5,v0,v3,v1,v2,4293980400,v4] BT.lf)) [5,v0,v3,v1,v2,4293982960,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,v7,v4] BT.lf) [5,v0,v3,v1,v2,v7,v9] (BT.nd BT.lf [5,v0,v3,v1,v2,v7,v10] BT.lf))) [5,v0,v3,v1,v2,v7,4294945440] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,4293984255,v4] BT.lf) [5,v0,v3,v1,v2,4294180851,v4] (BT.nd BT.lf [5,v0,v3,v1,v2,4294508536,v4] BT.lf)) [5,v0,v3,v1,v2,4294638330,v4] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,4294639600,v4] BT.lf) [5,v0,v3,v1,v2,4294639610,v4] (BT.nd BT.lf [5,v0,v3,v1,v2,4294901758,v4] BT.lf)))))) [5,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,v4,v11] BT.lf) [5,v0,v3,v1,v2,v4,4294967290] BT.lf) [5,v0,v3,v1,v2,v4,4294967295] (BT.nd BT.lf [5,v0,v3,v1,v2,4294902000] BT.lf)) [5,v0,v3,v1,v2,4294902015,v14] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,4294902015,vd] BT.lf) [5,v0,v3,v1,v2,4294914867,v19] (BT.nd BT.lf [5,v0,v3,v1,v2,4294934656] BT.lf))) [5,v0,v3,v1,v2,v9] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,v9,v9] BT.lf) [5,v0,v3,v1,v2,v9,v12] (BT.nd BT.lf [5,v0,v3,v1,v2,v9,v14] BT.lf)) [5,v0,v3,v1,v2,v9,4294965496] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,4294942720] BT.lf) [5,v0,v3,v1,v2,v10] (BT.nd BT.lf [5,v0,v3,v1,v2,v10,v10] BT.lf)))) [5,v0,v3,v1,v2,v10,v12] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,v10,v19] BT.lf) [5,v0,v3,v1,v2,v10,4294962412] (BT.nd BT.lf [5,v0,v3,v1,v2,v10,v14] BT.lf)) [5,v0,v3,v1,v2,v10,vd] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,v10,4294967200] BT.lf) [5,v0,v3,v1,v2,4294944936] (BT.nd BT.lf [5,v0,v3,v1,v2,4294945440] BT.lf))) [5,v0,v3,v1,v2,v12,v19] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,v12,4294963200] BT.lf) [5,v0,v3,v1,v2,v12,v14] (BT.nd BT.lf [5,v0,v3,v1,v2,v12,4294966524] BT.lf)) [5,v0,v3,v1,v2,v12,v11] (BT.nd (BT.nd BT.lf [5,v0,v3,v1,v2,4294959328] BT.lf) [5,v0,v3,v1,v2,4294962926,v14] (BT.nd BT.lf [5,v0,v3,v1,v13,v9] BT.lf))))) [5,v0,v3,v1,v17,v10] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v3,v1,4289374890,vd] BT.lf) [5,v0,v3,v1,4289396480,v12] (BT.nd BT.lf [5,v0,v3,v1,v1c,v12,vd] BT.lf)) [5,v0,v3,v1,v1c,v19,vd] (BT.nd (BT.nd BT.lf [5,v0,3435986943,v1,v2,v4,v19] BT.lf) [5,v0,3722304989,v5,v1,v2,v4] (BT.nd BT.lf [5,v0,3770736832,4006407884,v1,v2,v4] BT.lf))) [5,v0,3772834016,ve,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,3772834016,v5,v1a,v2,v4] BT.lf) [5,v0,3972852940,v6,v1,v2,v4] (BT.nd BT.lf [5,v0,3972852940,v1,v2,v4] BT.lf)) [5,v0,ve,ve,v1,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,ve,v5,v1,v2,v4] BT.lf) [5,v0,ve,v6,v1,v2,v4] (BT.nd BT.lf [5,v0,ve,v1,v1,v2,v4] BT.lf)))) [5,v0,ve,v1,vf,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,ve,v1,v1a,v2,v4] BT.lf) [5,v0,ve,v1,4278190080,v2,v4] (BT.nd BT.lf [5,v0,ve,v1,v2,v2,v4] BT.lf)) [5,v0,ve,v1,v2,v17,v4] (BT.nd (BT.nd BT.lf [5,v0,ve,v1,v2,v1c,v4] BT.lf) [5,v0,ve,v1,v2,4291624908,v4] (BT.nd BT.lf [5,v0,ve,v1,v2,4293722092,v4] BT.lf))) [5,v0,ve,v1,v2,v7,v4] (BT.nd (BT.nd (BT.nd BT.lf [5,v0,ve,v1,v2,v4] BT.lf) [5,v0,ve,v1,v2,v4,vd] (BT.nd BT.lf [5,v0,ve,v1,v2,v10] BT.lf)) [5,v0,ve,vf,v2,v4] (BT.nd (BT.nd BT.lf [5,v0,4008505068,v1,v2,v7,v4] BT.lf) [5,v0,4008505068,v1,v2,v4] (BT.nd BT.lf [5,v0,v5,v1,v16,v2,v4] BT.lf)))))))) [5,v0,v5,v1,4241292492,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,v0,v5,v1,v1a,v2,v4] BT.lf) [5,v0,v5,v1,v2,4294770684,v4] BT.lf) [5,v0,v5,v1,v2,v9] (BT.nd BT.lf [5,v0,v5,v1,v2,v12,v19] BT.lf)) [5,v0,v5,v1,v2,v19,v14] (BT.nd (BT.nd BT.lf [5,v0,v18,v1,v15,v2,v4] BT.lf) [5,v0,v6,v1,v15,v2,v4] (BT.nd BT.lf [5,v0,v1,v15,v2,v4] BT.lf))) [5,v0,v1,4241292492,v2,v4,v19] (BT.nd (BT.nd (BT.nd BT.lf [5,3941264106,v1,v1a,v2,v4] BT.lf) [5,v5,v1,v16,v2,v4] (BT.nd BT.lf [5,v5,v1,vf,v1a,v2,v4] BT.lf)) [5,v5,v1,vf,v2,4291624908,v4] (BT.nd (BT.nd BT.lf [5,v5,v1,v2,v9] BT.lf) [5,v5,v1,v2,v12,v19] (BT.nd BT.lf [6,0,v8,v0,v3,v1,v2] BT.lf)))) [6,0,v8,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,0,va,v0,v3,v1,v2,v4] BT.lf) [6,0,va,v0,v1,v2,v4] (BT.nd BT.lf [6,0,v0,v3,v1,v2,v4] BT.lf)) [6,255,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,255,v0,v3,v1,v2,v4,vd] BT.lf) [6,13107,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,13107,v0,v3,v1,v2,v4,v19] BT.lf))) [6,43690,v8,v0,v3,v1,v2] (BT.nd (BT.nd (BT.nd BT.lf [6,43690,v8,v0,v3,v1,v2,v4] BT.lf) [6,43690,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,61680,v8,v0,v3,v1,v2] BT.lf)) [6,61680,v8,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,61680,v0,v3,v1,v2,v4] BT.lf) [6,v8,v8,v0,v3,v1,v2] (BT.nd BT.lf [6,v8,v8,v0,v3,v1,v2,v4] BT.lf))))) [6,v8,16711935,v0,v3,v1] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v8,16711935,v0,v3,v1,v2] BT.lf) [6,v8,16711935,v0,v3,v1,v2,v4] BT.lf) [6,v8,va,v0,v3,v1,v2] (BT.nd BT.lf [6,v8,va,v0,v3,v1,v2,v4] BT.lf)) [6,v8,va,v0,v1,v2] (BT.nd (BT.nd BT.lf [6,v8,va,v0,v1,v2,v4] BT.lf) [6,v8,vb,v0,v3,v1,v2] (BT.nd BT.lf [6,v8,vb,v0,v3,v1,v2,v4] BT.lf))) [6,v8,vc,v0,v3,v1,v2] (BT.nd (BT.nd (BT.nd BT.lf [6,v8,vc,v0,v3,v1,v2,v4] BT.lf) [6,v8,2863267840,v0,v3,v1,v2] (BT.nd BT.lf [6,v8,2863267840,v0,v3,v1,v2,v4] BT.lf)) [6,v8,v0,v0,v3,v1,v2] (BT.nd (BT.nd BT.lf [6,v8,v0,v0,v3,v1,v2,v4] BT.lf) [6,v8,v0,2863333375,v3,v1,v2] (BT.nd BT.lf [6,v8,v0,2863333375,v3,v1,v2,v4] BT.lf)))) [6,v8,v0,v3,v5,v1,v2] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v8,v0,v3,v5,v1,v2,v4] BT.lf) [6,v8,v0,v3,v6,v1,v2] (BT.nd BT.lf [6,v8,v0,v3,v6,v1,v2,v4] BT.lf)) [6,v8,v0,v3,4042260480,v1,v2] (BT.nd (BT.nd BT.lf [6,v8,v0,v3,4042260480,v1,v2,v4] BT.lf) [6,v8,v0,v3,v1,v1,v2] (BT.nd BT.lf [6,v8,v0,v3,v1,v1,v2,v4] BT.lf))) [6,v8,v0,v3,v1,4042326015,v2] (BT.nd (BT.nd (BT.nd BT.lf [6,v8,v0,v3,v1,4042326015,v2,v4] BT.lf) [6,v8,v0,v3,v1,vf,v2] (BT.nd BT.lf [6,v8,v0,v3,v1,vf,v2,v4] BT.lf)) [6,v8,v0,v3,v1,v2] (BT.nd (BT.nd BT.lf [6,v8,v0,v3,v1,v2,v7] BT.lf) [6,v8,v0,v3,v1,v2,v7,v4] (BT.nd BT.lf [6,v8,v0,v3,v1,v2,v4] BT.lf)))))) [6,v8,v0,v3,v1,v2,v4,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v8,v0,v3,v1,v2,v4,v12] BT.lf) [6,v8,v0,v3,v1,v2,v4,v14] BT.lf) [6,v8,v0,v3,v1,v2,v4,4294967295] (BT.nd BT.lf [6,v8,v0,v3,v1,v2,v12] BT.lf)) [6,v8,v0,v3,v1,v2,v14] (BT.nd (BT.nd BT.lf [6,v8,v0,v3,v1,v2,4294967295] BT.lf) [6,16777215,v0,v3,v1,4278190080,v2,v4] (BT.nd BT.lf [6,16777215,v0,v3,v1,v2,v4] BT.lf))) [6,286331153,v0,v3,v5,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,286331153,v0,v3,v1,v2,v4] BT.lf) [6,572662306,va,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,572662306,va,v0,v1,v2,v4] BT.lf)) [6,572662306,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,808464432,va,v0,v3,v1,v2,v4] BT.lf) [6,808464432,va,v0,v1,v2,v4] (BT.nd BT.lf [6,808464432,v0,v3,v1,v2,v4] BT.lf)))) [6,va,va,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,va,va,v0,v1,v2,v4] BT.lf) [6,va,1431655765,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,va,1431655765,v0,v1,v2,v4] BT.lf)) [6,va,1431655765,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,va,vb,v0,v3,v1,v2,v4] BT.lf) [6,va,vb,v0,v1,v2,v4] (BT.nd BT.lf [6,va,vc,v0,v3,v1,v2,v4] BT.lf))) [6,va,vc,v0,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,va,v0,v0,v3,v1,v2,v4] BT.lf) [6,va,v0,v0,v1,v2,v4] (BT.nd BT.lf [6,va,v0,3149642683,v3,v1,v2,v4] BT.lf)) [6,va,v0,3149642683,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,va,v0,3233857728,v3,v1,v2,v4] BT.lf) [6,va,v0,3233857728,v1,v2,v4] (BT.nd BT.lf [6,va,v0,v3,v3,v1,v2,v4] BT.lf))))) [6,va,v0,v3,v5,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,va,v0,v3,v6,v1,v2,v4] BT.lf) [6,va,v0,v3,v1,v1,v2,v4] (BT.nd BT.lf [6,va,v0,v3,v1,4092851187,v2,v4] BT.lf)) [6,va,v0,v3,v1,vf,v2,v4] (BT.nd (BT.nd BT.lf [6,va,v0,v3,v1,v1a,v2,v4] BT.lf) [6,va,v0,v3,v1,v2,v7,v4] (BT.nd BT.lf [6,va,v0,v3,v1,v2,v4] BT.lf))) [6,va,v0,v3,v1,v2,v4,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [6,va,v0,v5,v1,v2,v4] BT.lf) [6,va,v0,v6,v1,v2,v4] (BT.nd BT.lf [6,va,v0,v1,v1,v2,v4] BT.lf)) [6,va,v0,v1,4092851187,v2,v4] (BT.nd (BT.nd BT.lf [6,va,v0,v1,vf,v2,v4] BT.lf) [6,va,v0,v1,v1a,v2,v4] (BT.nd BT.lf [6,va,v0,v1,v2,v7,v4] BT.lf)))) [6,va,v0,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,va,v0,v1,v2,v4,4294967295] BT.lf) [6,859045887,v0,3435921408,v3,v1,v2,v4] (BT.nd BT.lf [6,859045887,v0,v3,v1,v2,v4] BT.lf)) [6,2004318071,vb,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,2004318071,v0,v3,v1,v2,v4] BT.lf) [6,2155905152,vb,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,2155905152,vc,v0,v3,v1,v2,v4] BT.lf))) [6,2155905152,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,vb,vb,v0,v3,v1,v2,v4] BT.lf) [6,vb,vc,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,vb,v0,v0,v3,v1,v2,v4] BT.lf)) [6,vb,v0,v3,v5,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,vb,v0,v3,v6,v1,v2,v4] BT.lf) [6,vb,v0,v3,v1,v1,v2,v4] (BT.nd BT.lf [6,vb,v0,v3,v1,v16,v2,v4] BT.lf))))))) [6,vb,v0,v3,v1,vf,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,vb,v0,v3,v1,v2,v7,v4] BT.lf) [6,vb,v0,v3,v1,v2,v4] BT.lf) [6,vb,v0,v3,v1,v2,v9] (BT.nd BT.lf [6,vb,v0,v5,v1,v2,v4] BT.lf)) [6,vb,v5,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,2684395520,vc,v0,v3,v1,v2,v4] BT.lf) [6,2684395520,v0,v3,v6,v1,v2,v4] (BT.nd BT.lf [6,2684395520,v0,v3,v1,v2,v4] BT.lf))) [6,vc,vc,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,vc,2852170240,v0,v3,v1,v2,v4] BT.lf) [6,vc,v0,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,vc,v0,3233857728,v3,v1,v2,v4] BT.lf)) [6,vc,v0,3422604288,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,vc,v0,v3,v3,v1,v2,v4] BT.lf) [6,vc,v0,v3,ve,v1,v2,v4] (BT.nd BT.lf [6,vc,v0,v3,v5,v1,v2,v4] BT.lf)))) [6,vc,v0,v3,v6,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,vc,v0,v3,v1,v1,v2,v4] BT.lf) [6,vc,v0,v3,v1,vf,v2,v4] (BT.nd BT.lf [6,vc,v0,v3,v1,v1a,v2,v4] BT.lf)) [6,vc,v0,v3,v1,4278190080,v2,v4] (BT.nd (BT.nd BT.lf [6,vc,v0,v3,v1,v2,v2,v4] BT.lf) [6,vc,v0,v3,v1,v2,v17,v4] (BT.nd BT.lf [6,vc,v0,v3,v1,v2,v1c,v4] BT.lf))) [6,vc,v0,v3,v1,v2,4291624908,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,vc,v0,v3,v1,v2,v7,v4] BT.lf) [6,vc,v0,v3,v1,v2,v4] (BT.nd BT.lf [6,vc,v0,v3,v1,v2,v4,vd] BT.lf)) [6,vc,v0,v3,v1,v2,v10] (BT.nd (BT.nd BT.lf [6,vc,v0,v3,vf,v2,v4] BT.lf) [6,vc,v0,ve,v1,v2,v4] (BT.nd BT.lf [6,vc,v3,v1,vf,v2,v4] BT.lf))))) [6,2829625512,v0,v3,v1,v1a,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2829625512,v0,v3,v1,v2,v4] BT.lf) [6,2862656160,v0,v3,v1,v2,v7,v4] (BT.nd BT.lf [6,2862656160,v0,v3,v1,v2,v4] BT.lf)) [6,v0,v0,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,v0,v0,v3,v3,v1,v2,v4] BT.lf) [6,v0,v0,v3,v5,v1,v2,v4] (BT.nd BT.lf [6,v0,v0,v3,v6,v1,v2,v4] BT.lf))) [6,v0,v0,v3,v1,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v0,v3,v1,vf,v2,v4] BT.lf) [6,v0,v0,v3,v1,v1a,v2,v4] (BT.nd BT.lf [6,v0,v0,v3,v1,v2,v7,v4] BT.lf)) [6,v0,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,v0,2863333375,v3,v1,v2,v4] BT.lf) [6,v0,3149642683,v3,v1,v2,v4] (BT.nd BT.lf [6,v0,v3,3772834016,v5,v1,v2,v4] BT.lf)))) [6,v0,v3,3772834016,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,3941264106,v1,v2,v4] BT.lf) [6,v0,v3,v5,v5,v1,v2,v4] (BT.nd BT.lf [6,v0,v3,v5,v6,v1,v2,v4] BT.lf)) [6,v0,v3,v5,v1,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,v0,v3,v5,v1,vf,v2,v4] BT.lf) [6,v0,v3,v5,v1,4278124286,v2,v4] (BT.nd BT.lf [6,v0,v3,v5,v1,v2,v7,v4] BT.lf))) [6,v0,v3,v5,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,v18,v6,v1,v2,v4] BT.lf) [6,v0,v3,v18,v1,v2,v4] (BT.nd BT.lf [6,v0,v3,v6,v6,v1,v2,v4] BT.lf)) [6,v0,v3,v6,4042260480,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,v0,v3,v6,v1,v1,v2,v4] BT.lf) [6,v0,v3,v6,v1,4205509290,v2,v4] (BT.nd BT.lf [6,v0,v3,v6,v1,vf,v2,v4] BT.lf)))))) [6,v0,v3,v6,v1,v2,v7,v4] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,v6,v1,v2,v4] BT.lf) [6,v0,v3,v6,v1,v2,v4,v4] BT.lf) [6,v0,v3,v6,v1,v2,v4,v12] (BT.nd BT.lf [6,v0,v3,v6,v1,v2,v4,4294963200] BT.lf)) [6,v0,v3,v6,v1,v2,v4,v14] (BT.nd (BT.nd BT.lf [6,v0,v3,v6,v1,v7,v4] BT.lf) [6,v0,v3,v6,v1,v4,vd] (BT.nd BT.lf [6,v0,v3,v6,v7,v4] BT.lf))) [6,v0,v3,v1d,v1,v2,v1c,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,v1d,v1,v2,v4] BT.lf) [6,v0,v3,4042321920,v1,v2,v4] (BT.nd BT.lf [6,v0,v3,4042321920,v1,v2,v4,vd] BT.lf)) [6,v0,v3,v1,v1,v1,v2,v4] (BT.nd (BT.nd BT.lf [6,v0,v3,v1,v1,vf,v2,v4] BT.lf) [6,v0,v3,v1,v1,v2,v2,v4] (BT.nd BT.lf [6,v0,v3,v1,v1,v2,v1c,v4] BT.lf)))) [6,v0,v3,v1,v1,v2,v7,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,v1,v1,v2,v4] BT.lf) [6,v0,v3,v1,v1,v2,v4,vd] (BT.nd BT.lf [6,v0,v3,v1,4042326015,v2,v4] BT.lf)) [6,v0,v3,v1,4092851187,v2,v4] (BT.nd (BT.nd BT.lf [6,v0,v3,v1,v16,v2,v4] BT.lf) [6,v0,v3,v1,4205509290,v2,v4] (BT.nd BT.lf [6,v0,v3,v1,4210096880,v2,v4] BT.lf))) [6,v0,v3,v1,vf,vf,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,v1,vf,v1a,v2,v4] BT.lf) [6,v0,v3,v1,vf,4278124286,v2,v4] (BT.nd BT.lf [6,v0,v3,v1,vf,v2,v1c,v4] BT.lf)) [6,v0,v3,v1,vf,v2,4291624908,v4] (BT.nd (BT.nd BT.lf [6,v0,v3,v1,vf,v2,v7,v4] BT.lf) [6,v0,v3,v1,vf,v2,4294639610,v4] (BT.nd BT.lf [6,v0,v3,v1,vf,v2,v4] BT.lf))))) [6,v0,v3,v1,vf,v2,v4,vd] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,v1,4278124286,v2,v4] BT.lf) [6,v0,v3,v1,v2,4293980400,v4] (BT.nd BT.lf [6,v0,v3,v1,v2,v7,v7,v4] BT.lf)) [6,v0,v3,v1,v2,v7,4294639610,v4] (BT.nd (BT.nd BT.lf [6,v0,v3,v1,v2,v7,v4] BT.lf) [6,v0,v3,v1,v2,v7,v4,v14] (BT.nd BT.lf [6,v0,v3,v1,v2,v7,v4,v11] BT.lf))) [6,v0,v3,v1,v2,4294639610,v4] (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v3,v1,v2,v4] BT.lf) [6,v0,v3,v1,v2,v4,v11] (BT.nd BT.lf [6,v0,v3,v1,v2,v4,4294967295] BT.lf)) [6,v0,v3,v1,v2,v9] (BT.nd (BT.nd BT.lf [6,v0,v3,v1,v2,v10] BT.lf) [6,v0,v3,v1,v2,v12,v19] (BT.nd BT.lf [6,v0,v3,v1,v2,v12,v14] BT.lf)))) [6,v0,ve,v1,v2,v4] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,v0,v5,v1,v1a,v2,v4] BT.lf) [7,v8,v0,v3,v1,v2] (BT.nd BT.lf [7,v8,v0,v3,v1,v2,v4] BT.lf)) [7,va,v0,v3,v1,v2,v4] (BT.nd (BT.nd BT.lf [7,va,v0,v1,v2,v4] BT.lf) [7,vb,v0,v3,v1,v2,v4] (BT.nd BT.lf [7,vc,v0,v3,v1,v2,v4] BT.lf))) [7,v0,v0,v3,v1,v2,v4] (BT.nd (BT.nd (BT.nd BT.lf [7,v0,v3,v5,v1,v2,v4] BT.lf) [7,v0,v3,v6,v1,v2,v4] (BT.nd BT.lf [7,v0,v3,v1,v1,v2,v4] BT.lf)) [7,v0,v3,v1,vf,v2,v4] (BT.nd (BT.nd BT.lf [7,v0,v3,v1,v2,v7,v4] BT.lf) [7,v0,v3,v1,v2,v4] (BT.nd BT.lf [8,v0,v3,v1,v2,v4] BT.lf))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel

def chunks : List (List (List Nat × List (Nat × Nat))) :=
  [K_0,K_1,K_2,K_3,K_4,K_5,K_6,K_7,K_8,K_9,K_10,K_11,K_12,K_13,K_14,K_15,K_16,K_17,K_18,K_19,K_20,K_21,K_22,K_23,K_24,K_25,K_26,K_27,K_28,K_29]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hAll_cert : chunks.flatten.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by
  rw [List.all_flatten, List.all_eq_true]
  intro k hk
  simp only [chunks, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c_0
  · exact c_1
  · exact c_2
  · exact c_3
  · exact c_4
  · exact c_5
  · exact c_6
  · exact c_7
  · exact c_8
  · exact c_9
  · exact c_10
  · exact c_11
  · exact c_12
  · exact c_13
  · exact c_14
  · exact c_15
  · exact c_16
  · exact c_17
  · exact c_18
  · exact c_19
  · exact c_20
  · exact c_21
  · exact c_22
  · exact c_23
  · exact c_24
  · exact c_25
  · exact c_26
  · exact c_27
  · exact c_28
  · exact c_29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hK_cert : T_cert.toList = chunks.flatten.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, stepOK M_ Y_ PD_ PM_ G_ T_cert x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert chunks.flatten hK_cert hAll_cert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lb_idx : ∀ s : Nat, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 4277071592 (idx5 x)) s → 9 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

theorem lb : ∀ s : Nat, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 4277071592 (∑ i : Fin 5, if x i then 2 ^ i.val else 0)) s → 9 ≤ s := by
  intro s h
  simpa only [sum_eq] using lb_idx s (by simpa only [sum_eq] using h)

end RestrictionCertificateUpper

end PEqualNP.Outside.L_meta_12302_aux.Cofactor

namespace PEqualNP.Outside.L_meta_12302_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676840 * 2 ^ 32 + 3907577984)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit := ⟨[
  ⟨.or, [0, 2]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 8]⟩,
  ⟨.and, [3, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [7, 11]⟩,
  ⟨.or, [1, 12]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [15, 16]⟩], 17⟩

theorem checkWitness : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem essential : ∀ i : Fin 6, ∃ u : Fin 6 → Bool,
    target (Function.update u i (!u i)) ≠ target u := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem nonconstant : ∀ (i : Fin 6) (b : Bool), ∃ y y' : Fin 5 → Bool,
    target (FirstGate.ins i b y) ≠ target (FirstGate.ins i b y') := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pivotalLow : ∀ i : Fin 6, i.val < 3 → ∀ u : Fin 6 → Bool, ∃ v : Fin 6 → Bool,
    (∀ j : Fin 6, ¬ j.val < 3 → v j = u j) ∧ target (Function.update v i (!v i)) ≠ target v := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pivotalPair : ∀ (i : Fin 6), i.val < 3 → ∀ j : Fin 6, j.val < 3 → i ≠ j →
    ∀ b : Bool, ∃ u : Fin 6 → Bool, u j = b ∧ target (Function.update u i (!u i)) ≠ target u := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tables : ∀ i : Fin 6, i.val < 3 → ∀ (b : Bool) (x : Fin 5 → Bool),
    target (FirstGate.ins i b x) =
      Nat.testBit (if b then 4277071592 else 3901261952) (∑ j : Fin 5, if x j then 2 ^ j.val else 0) := by
  decide +kernel

theorem restrictedLower (i : Fin 6) (hi : i.val < 3) (b : Bool) (s : ℕ)
    (h : HasCircuitSize 5 (fun x => target (FirstGate.ins i b x)) s) : 11 < s + 3 := by
  have hEq : (fun x : Fin 5 → Bool => target (FirstGate.ins i b x)) =
      (fun x : Fin 5 → Bool =>
        Nat.testBit (if b then 4277071592 else 3901261952)
          (∑ j : Fin 5, if x j then 2 ^ j.val else 0)) := funext (tables i hi b)
  rw [hEq] at h
  have h9 : 9 ≤ s := by
    cases b
    · exact Cofactor.RestrictionCertificate.lb s h
    · exact Cofactor.RestrictionCertificateUpper.lb s h
  omega

theorem lower11 : ¬ HasCircuitSize 6 target 11 :=
  FirstGate.unrestrictedHeavyLower 5 11 target (fun i => i.val < 3)
    ⟨0, by decide⟩ essential nonconstant pivotalLow pivotalPair restrictedLower

theorem witnessSize : witness.size = 12 := by decide

theorem witnessMono : Monotone2 witness := by simp [Monotone2, witness]

end PEqualNP.Outside.L_meta_12302_aux

open PEqualNP.Outside.L_meta_12302_aux in
theorem PEqualNP.Outside.L_meta_12302 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 3907577984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 3907577984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  change PEqualNP.MetaComplexity.HasCircuitSize 6 target s at h
  have h12 : 12 <= s := by
    by_contra hn
    apply lower11
    obtain ⟨C, hC, hSize, hEval⟩ := h
    exact ⟨C, hC, hSize.trans (by omega), hEval⟩
  exact ⟨witness, witnessMono, by rw [witnessSize]; exact h12, checkWitness⟩
