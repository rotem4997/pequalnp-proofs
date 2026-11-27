import PEqualNP.Defs
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_3694

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

private def Shaped (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ a b, gs[j].inputs = [a, b] ∧
    (gs[j].op = .and ∨ gs[j].op = .or) ∧ a < n + j ∧ b < n + j

private lemma shaped_iff (n : ℕ) (C : Circuit) : Shaped n C.gates ↔ IsAO2 n C := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      exact (h j hj).choose_spec.choose_spec.2.1
    · intro j hj i hi
      obtain ⟨a, b, hi', _, ha, hb⟩ := h j hj
      simp only [gateAt, List.getD_eq_getElem _ _ hj, hi', List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a, b, hab, _⟩ := h j hj
      rw [hab]
      rfl
  · rintro ⟨hop, hback, hlen⟩ j hj
    have hmem := List.getElem_mem (l := C.gates) hj
    have htwo := hlen _ hmem
    obtain ⟨a, b, hab⟩ : ∃ a b, C.gates[j].inputs = [a, b] := by
      cases hi : C.gates[j].inputs with
      | nil => simp [hi] at htwo
      | cons a rest =>
        cases rest with
        | nil => simp [hi] at htwo
        | cons b tail =>
          have ht : tail = [] := List.length_eq_zero_iff.mp (by simp only [hi, List.length_cons] at htwo; omega)
          exact ⟨a, b, by simp [ht]⟩
    have hgate : (gateAt C j).inputs = [a, b] := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact hab
    exact ⟨a, b, hab, hop _ hmem, hback j hj a (by simp [hgate]),
      hback j hj b (by simp [hgate])⟩

private lemma shaped_snoc {n : ℕ} {gs : List Gate} {g : Gate} {a b : ℕ}
    (h : Shaped n gs) (hg : g.inputs = [a, b])
    (hop : g.op = .and ∨ g.op = .or) (ha : a < n + gs.length) (hb : b < n + gs.length) :
    Shaped n (gs ++ [g]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · simpa [List.getElem_append_left hlt] using h j hlt
  · have hj' : j = gs.length := by simp at hj; omega
    subst j
    simpa using ⟨a, b, hg, hop, ha, hb⟩

private lemma shaped_init {n : ℕ} {gs : List Gate} {g : Gate}
    (h : Shaped n (gs ++ [g])) : Shaped n gs := by
  intro j hj
  have hh := h j (by simp; omega)
  rw [List.getElem_append_left hj] at hh
  exact hh

private lemma shaped_last {n : ℕ} {gs : List Gate} {g : Gate}
    (h : Shaped n (gs ++ [g])) :
    ∃ a b, g.inputs = [a, b] ∧ (g.op = .and ∨ g.op = .or) ∧
      a < n + gs.length ∧ b < n + gs.length := by
  simpa using h gs.length (by simp)

-- The second component maps old wires to surviving wires, with none for a false wire.
private abbrev State := List Gate × List (Option ℕ)

private def inputMap (n v : ℕ) : List (Option ℕ) :=
  (List.range n).map fun i => if i = v then none else some i

private def operand (r : State) (i : ℕ) : Option ℕ := r.2.getD i none

private def addGate (n : ℕ) (r : State) (g : Gate) : State :=
  let a := operand r (g.inputs[0]?.getD 0)
  let b := operand r (g.inputs[1]?.getD 0)
  match a, b with
  | some a, some b => (r.1 ++ [⟨g.op, [a, b]⟩], r.2 ++ [some (n + r.1.length)])
  | none, none => (r.1, r.2 ++ [none])
  | some a, none | none, some a =>
    (r.1, r.2 ++ [match g.op with | .or => some a | _ => none])

private def compile (n v : ℕ) (gs : List Gate) : State :=
  gs.foldl (addGate n) ([], inputMap n v)

private lemma compile_snoc (n v : ℕ) (gs : List Gate) (g : Gate) :
    compile n v (gs ++ [g]) = addGate n (compile n v gs) g := by
  simp [compile, List.foldl_append]

private lemma getD_snoc {α : Type} (xs : List α) (x d : α) (i : ℕ) :
    (xs ++ [x]).getD i d = if i < xs.length then xs.getD i d
      else if i = xs.length then x else d := by
  split
  · exact List.getD_append _ _ _ _ ‹_›
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    split
    · simp [‹i = xs.length›, List.getD_eq_getElem?_getD]
    · have hn : 1 ≤ i - xs.length := by omega
      exact List.getD_eq_default _ _ hn

private lemma inputMap_getD (n v i : ℕ) :
    (inputMap n v).getD i none = if i < n ∧ i ≠ v then some i else none := by
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa [inputMap] using hi)]
    simp [inputMap, hi]
  · rw [List.getD_eq_default _ _ (by simpa [inputMap] using Nat.le_of_not_gt hi)]
    simp [hi]

private def uses (v : ℕ) (g : Gate) : Bool := decide (v ∈ g.inputs)

private def Bounded (n : ℕ) (r : State) : Prop :=
  ∀ i j, operand r i = some j → j < n + r.1.length

private lemma bounded_snoc {n : ℕ} {r : State} {a : Option ℕ}
    (h : Bounded n r) (ha : ∀ j, a = some j → j < n + r.1.length) :
    Bounded n (r.1, r.2 ++ [a]) := by
  intro i j hj
  simp only [operand, getD_snoc] at hj
  split at hj
  · exact h i j hj
  · split at hj
    · exact ha j hj
    · contradiction

set_option maxHeartbeats 800000 in
private lemma compile_shape {n v : ℕ} {gs : List Gate} (hvIn : v < n) (h : Shaped n gs) :
    let r := compile n v gs
    Shaped n r.1 ∧ Bounded n r ∧ r.2.length = n + gs.length ∧
      operand r v = none ∧ r.1.length + gs.countP (uses v) ≤ gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    have hlen : (inputMap n v).length = n := by simp [inputMap]
    refine ⟨by simp [Shaped, compile], ?_, by simp [compile, hlen], ?_, by simp [compile]⟩
    · intro i j hj
      change (inputMap n v).getD i none = some j at hj
      rw [inputMap_getD] at hj
      split at hj
      · cases hj
        exact ‹i < n ∧ i ≠ v›.1
      · contradiction
    · change (inputMap n v).getD v none = none
      rw [inputMap_getD]
      simp
  | append_singleton gs g ih =>
    obtain ⟨a, b, hab, hop, ha, hb⟩ := shaped_last h
    obtain ⟨hshape, hbd, hlen, hv, hcount⟩ := ih (shaped_init h)
    let r := compile n v gs
    change Shaped n r.1 at hshape
    change Bounded n r at hbd
    change r.2.length = n + gs.length at hlen
    change operand r v = none at hv
    change r.1.length + gs.countP (uses v) ≤ gs.length at hcount
    have hvlt : v < r.2.length := by omega
    have retainNone (D : List Gate) (o : Option ℕ) :
        operand (D, r.2 ++ [o]) v = none := by
      simpa only [operand, List.getD_append _ _ _ _ hvlt] using hv
    have dropGate (o : Option ℕ) (ho : ∀ j, o = some j → j < n + r.1.length) :
        Shaped n r.1 ∧ Bounded n (r.1, r.2 ++ [o]) ∧
        (r.2 ++ [o]).length = n + (gs ++ [g]).length ∧
        operand (r.1, r.2 ++ [o]) v = none ∧
        r.1.length + (gs ++ [g]).countP (uses v) ≤ (gs ++ [g]).length := by
      refine ⟨hshape, bounded_snoc hbd ho, by simp [hlen, Nat.add_assoc], retainNone _ _, ?_⟩
      simp only [List.countP_append, List.countP_singleton, List.length_append,
        List.length_singleton]
      split <;> omega
    simp only [compile_snoc]
    change (let r' := addGate n r g; Shaped n r'.1 ∧ Bounded n r' ∧
      r'.2.length = n + (gs ++ [g]).length ∧ operand r' v = none ∧
      r'.1.length + (gs ++ [g]).countP (uses v) ≤ (gs ++ [g]).length)
    simp only [addGate, hab, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rcases hma : operand r a with _ | a' <;> rcases hmb : operand r b with _ | b'
    · exact dropGate none (by simp)
    · rcases hop with hop | hop
      · simpa [hop] using dropGate none (by simp)
      · simpa [hop] using dropGate (some b') (by intro j hj; cases hj; exact hbd _ _ hmb)
    · rcases hop with hop | hop
      · simpa [hop] using dropGate none (by simp)
      · simpa [hop] using dropGate (some a') (by intro j hj; cases hj; exact hbd _ _ hma)
    · have ha' := hbd _ _ hma
      have hb' := hbd _ _ hmb
      let g' : Gate := ⟨g.op, [a', b']⟩
      have oldBound : Bounded n (r.1 ++ [g'], r.2) := by
        intro i j hij
        have := hbd i j hij
        simp only [List.length_append, List.length_singleton]
        omega
      have newBound : ∀ j, some (n + r.1.length) = some j →
          j < n + (r.1 ++ [g']).length := by
        intro j hj
        cases hj
        simp
      have huv : uses v g = false := by
        have hna : v ≠ a := fun e => by subst a; simp [hv] at hma
        have hnb : v ≠ b := fun e => by subst b; simp [hv] at hmb
        simp [uses, hab, hna, hnb]
      refine ⟨shaped_snoc hshape rfl hop ha' hb', bounded_snoc oldBound newBound,
        by simp [hlen, Nat.add_assoc], retainNone _ _, ?_⟩
      simp only [List.countP_append, List.countP_singleton, huv, Bool.false_eq_true,
        ite_false, Nat.add_zero, List.length_append, List.length_singleton]
      omega

private def scan {α : Type} (zero : α) (op : GateOp → List α → α)
    (gs : List Gate) (xs : List α) : List α :=
  gs.foldl (fun w g => w ++ [op g.op (g.inputs.map fun i => w.getD i zero)]) xs

private lemma scan_snoc {α : Type} (zero : α) (op : GateOp → List α → α)
    (gs : List Gate) (g : Gate) (xs : List α) :
    scan zero op (gs ++ [g]) xs =
      scan zero op gs xs ++ [op g.op (g.inputs.map fun i => (scan zero op gs xs).getD i zero)] := by
  simp [scan, List.foldl_append]

private lemma scan_len {α : Type} (zero : α) (op : GateOp → List α → α)
    (gs : List Gate) (xs : List α) :
    (scan zero op gs xs).length = xs.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [scan]
  | append_singleton gs g ih => simp [scan_snoc, ih, Nat.add_assoc]

private def lookup {α : Type} (zero : α) (w : List α) (i : Option ℕ) : α :=
  (i.map fun j => w.getD j zero).getD zero

-- The same rewrite applies to Boolean evaluation and to the two linear parts.
set_option maxHeartbeats 900000 in
private lemma compile_eval {α : Type} (zero : α) (op : GateOp → List α → α)
    (horl : ∀ a, op .or [zero, a] = a) (horr : ∀ a, op .or [a, zero] = a)
    (handl : ∀ a, op .and [zero, a] = zero) (handr : ∀ a, op .and [a, zero] = zero)
    {n v : ℕ} (hv : v < n) (xs ys : List α) (hx : xs.length = n) (hy : ys.length = n)
    (hrel : ∀ i < n, xs.getD i zero = if i = v then zero else ys.getD i zero)
    {gs : List Gate} (h : Shaped n gs) (i : ℕ) :
    let r := compile n v gs
    (scan zero op gs xs).getD i zero =
      lookup zero (scan zero op r.1 ys) (operand r i) := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change xs.getD i zero = lookup zero ys ((inputMap n v).getD i none)
    rw [inputMap_getD]
    by_cases hi : i < n
    · rw [hrel i hi]
      by_cases hiv : i = v <;> simp [lookup, hi, hiv]
    · rw [List.getD_eq_default _ _ (by rw [hx]; omega)]
      simp [hi, lookup]
  | append_singleton gs g ih =>
    obtain ⟨a, b, hab, hop, ha, hb⟩ := shaped_last h
    have hgs := shaped_init h
    let r := compile n v gs
    have hstruct := compile_shape (v := v) hv hgs
    change Shaped n r.1 ∧ Bounded n r ∧ r.2.length = n + gs.length ∧ _ at hstruct
    obtain ⟨_, hbd, hlen, _, _⟩ := hstruct
    let W := scan zero op gs xs
    let V := scan zero op r.1 ys
    have hw : W.length = r.2.length := by simp [W, scan_len, hx, hlen]
    have hV : V.length = n + r.1.length := by simp [V, scan_len, hy]
    have hleft : W.getD a zero = lookup zero V (operand r a) := ih hgs a
    have hright : W.getD b zero = lookup zero V (operand r b) := ih hgs b
    simp only [compile_snoc, scan_snoc, hab, List.map_cons, List.map_nil]
    change (W ++ [op g.op [W.getD a zero, W.getD b zero]]).getD i zero =
      lookup zero (scan zero op (addGate n r g).1 ys) (operand (addGate n r g) i)
    simp only [addGate, hab, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [hleft, hright]
    have reuse (o : Option ℕ)
        (hoe : op g.op [lookup zero V (operand r a), lookup zero V (operand r b)] =
          lookup zero V o) :
        (W ++ [lookup zero V o]).getD i zero =
          lookup zero V ((r.2 ++ [o]).getD i none) := by
      rw [getD_snoc, hw, getD_snoc]
      by_cases hi : i < r.2.length
      · simp only [ite_eq_left hi]
        exact ih hgs i
      · by_cases he : i = r.2.length <;> simp [hi, he, lookup]
    rcases hma : operand r a with _ | a' <;> rcases hmb : operand r b with _ | b'
    · have he : op g.op [zero, zero] = zero := by
        rcases hop with hop | hop
        · simpa [hop] using handl zero
        · simpa [hop] using horl zero
      simpa [operand, lookup, he] using reuse none (by simp [lookup, hma, hmb, he])
    · rcases hop with hop | hop
      · simpa [operand, lookup, hop, handl] using reuse none (by simp [lookup, hma, hmb, hop, handl])
      · simpa [operand, lookup, hop, horl] using reuse (some b') (by simp [lookup, hma, hmb, hop, horl])
    · rcases hop with hop | hop
      · simpa [operand, lookup, hop, handr] using reuse none (by simp [lookup, hma, hmb, hop, handr])
      · simpa [operand, lookup, hop, horr] using reuse (some a') (by simp [lookup, hma, hmb, hop, horr])
    · let next := op g.op [V.getD a' zero, V.getD b' zero]
      have keep (j : Option ℕ) (hj : ∀ x, j = some x → x < V.length) :
          lookup zero (V ++ [next]) j = lookup zero V j := by
        cases j with
        | none => rfl
        | some x =>
          change (V ++ [next]).getD x zero = V.getD x zero
          exact List.getD_append _ _ _ _ (hj x rfl)
      rw [scan_snoc]
      change (W ++ [next]).getD i zero =
        lookup zero (V ++ [next]) ((r.2 ++ [some (n + r.1.length)]).getD i none)
      rw [getD_snoc, hw, getD_snoc]
      by_cases hi : i < r.2.length
      · simp only [ite_eq_left hi]
        change W.getD i zero = lookup zero (V ++ [next]) (operand r i)
        rw [keep (operand r i) (fun j hj => by rw [hV]; exact hbd i j hj)]
        exact ih hgs i
      · by_cases he : i = r.2.length
        · simp only [ite_eq_right hi, ite_eq_left he]
          change next = (V ++ [next]).getD (n + r.1.length) zero
          rw [← hV]
          simp
        · simp [hi, he, lookup]

private def result (n v : ℕ) (C : Circuit) : Circuit :=
  let r := compile n v C.gates
  ⟨r.1, (operand r C.output).getD (n + r.1.length)⟩

private lemma result_eval {α : Type} (zero : α) (op : GateOp → List α → α)
    (horl : ∀ a, op .or [zero, a] = a) (horr : ∀ a, op .or [a, zero] = a)
    (handl : ∀ a, op .and [zero, a] = zero) (handr : ∀ a, op .and [a, zero] = zero)
    {n v : ℕ} (hv : v < n) (xs ys : List α) (hx : xs.length = n) (hy : ys.length = n)
    (hrel : ∀ i < n, xs.getD i zero = if i = v then zero else ys.getD i zero)
    {C : Circuit} (h : IsAO2 n C) :
    (scan zero op (result n v C).gates ys).getD (result n v C).output zero =
      (scan zero op C.gates xs).getD C.output zero := by
  rw [compile_eval zero op horl horr handl handr hv xs ys hx hy hrel ((shaped_iff _ _).2 h)]
  let r := compile n v C.gates
  change (scan zero op r.1 ys).getD ((operand r C.output).getD (n + r.1.length)) zero =
    lookup zero (scan zero op r.1 ys) (operand r C.output)
  cases hm : operand r C.output with
  | none =>
    change (scan zero op r.1 ys).getD (n + r.1.length) zero = zero
    exact List.getD_eq_default _ _ (by simp [scan_len, hy])
  | some i => rfl

private def pinned {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = v then false else x i

private lemma result_bool {n : ℕ} (v : Fin n) (C : Circuit) (h : IsAO2 n C)
    (x : Fin n → Bool) : circuitFun n (result n v.val C) x = circuitFun n C (pinned v x) := by
  apply result_eval false GateOp.eval
    (by intro a; cases a <;> decide) (by intro a; cases a <;> decide)
    (by intro a; cases a <;> decide) (by intro a; cases a <;> decide)
    v.isLt (List.ofFn (pinned v x)) (List.ofFn x) (by simp) (by simp) ?_ h
  intro i hi
  have h₂ : i < (List.ofFn x).length := by simpa using hi
  have h₁ : i < (List.ofFn (pinned v x)).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂]
  simp [pinned, Fin.ext_iff]

private def linearOp (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | .or => (ins.any (·.1), ins.any (·.2))
  | .and => ins.foldl (fun a p => (a.1 && p.1, (a.1 && p.2) || (a.2 && p.1))) (true, false)
  | _ => (false, false)

private def linearSeed (line : ℕ → Bool) (n a b : ℕ) : List (Bool × Bool) :=
  (((List.range n).map fun i => i == a || i == b).zipIdx).map fun (x, i) =>
    if line i then (false, x) else (x, false)

private lemma result_single {n : ℕ} (v : Fin n) (C : Circuit) (h : IsAO2 n C)
    (line : ℕ → Bool) (a b : ℕ) (ha : v.val ≠ a) (hb : v.val ≠ b) :
    lineSingle (result n v.val C) n line a b = lineSingle C n line a b := by
  let input := linearSeed line n a b
  have hlen : input.length = n := by simp [input, linearSeed]
  have hzero : input.getD v.val (false, false) = (false, false) := by
    have hba : (v.val == a) = false := Bool.eq_false_iff.mpr fun h => ha (by simpa using h)
    have hbb : (v.val == b) = false := Bool.eq_false_iff.mpr fun h => hb (by simpa using h)
    simp [input, linearSeed, List.getD_eq_getElem?_getD, v.isLt, hba, hbb]
  have hi : ∀ i < n, input.getD i (false, false) =
      if i = v.val then (false, false) else input.getD i (false, false) := by
    intro i _
    split
    · rename_i hi
      rwa [hi]
    · rfl
  have he := result_eval (false, false) linearOp
    (by rintro ⟨a,b⟩; cases a <;> cases b <;> decide)
    (by rintro ⟨a,b⟩; cases a <;> cases b <;> decide)
    (by rintro ⟨a,b⟩; cases a <;> cases b <;> decide)
    (by rintro ⟨a,b⟩; cases a <;> cases b <;> decide)
    v.isLt input input hlen hlen hi h
  exact congrArg Prod.snd he

private lemma count_uses (C : Circuit) (i : ℕ) :
    Fintype.card {j : Fin C.size // i ∈ (C.gates.get j).inputs} = C.gates.countP (uses i) := by
  calc
    _ = (List.ofFn fun j : Fin C.size => C.gates.get j).countP (uses i) := by
      rw [List.countP_ofFn, Fintype.card_subtype]
      simp [uses]
    _ = _ := by
      change (List.ofFn fun j : Fin C.gates.length => C.gates[j.val]).countP (uses i) = _
      rw [List.ofFn_getElem]

private lemma result_size {n : ℕ} (v : Fin n) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 n (result n v.val C) ∧
      (result n v.val C).size + Fintype.card {j : Fin C.size // v.val ∈ (C.gates.get j).inputs}
        ≤ C.size := by
  obtain ⟨hshape, _, _, _, hcount⟩ := compile_shape v.isLt ((shaped_iff _ _).2 h)
  exact ⟨(shaped_iff _ _).1 hshape, (count_uses C v.val).symm ▸ hcount⟩

private lemma scan_unused (gs : List Gate) (x y : List Bool) (v : ℕ)
    (hxy : x.length = y.length) (hun : gs.countP (uses v) = 0)
    (he : ∀ i, i ≠ v → x.getD i false = y.getD i false) (i : ℕ) (hi : i ≠ v) :
    (scan false GateOp.eval gs x).getD i false =
      (scan false GateOp.eval gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing i with
  | nil => exact he i hi
  | append_singleton gs g ih =>
    have hn : gs.countP (uses v) = 0 := by
      simp only [List.countP_append, Nat.add_eq_zero_iff] at hun
      exact hun.1
    have hg : v ∉ g.inputs := by
      by_contra hv
      simp [List.countP_append, uses, hv] at hun
    have hp : ∀ j ∈ g.inputs, (scan false GateOp.eval gs x).getD j false =
        (scan false GateOp.eval gs y).getD j false := by
      intro j hj
      exact ih hn j (fun h => hg (h ▸ hj))
    rw [scan_snoc, scan_snoc, getD_snoc, getD_snoc, scan_len, scan_len, hxy]
    simp only [List.map_congr_left hp, ih hn i hi]

private lemma unused_result {n : ℕ} (v : Fin n) (C : Circuit)
    (hcount : Fintype.card {j : Fin C.size // v.val ∈ (C.gates.get j).inputs} = 0)
    (hout : C.output ≠ v.val) (x : Fin n → Bool) :
    circuitFun n C x = circuitFun n C (pinned v x) := by
  apply scan_unused C.gates (List.ofFn x) (List.ofFn (pinned v x)) v.val
    (by simp) (count_uses C v.val ▸ hcount) ?_ _ hout
  intro i hi
  by_cases hin : i < n
  · have h₁ : i < (List.ofFn x).length := by simpa using hin
    have h₂ : i < (List.ofFn (pinned v x)).length := by simpa using hin
    rw [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂]
    simp [pinned, Fin.ext_iff, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma scan_input {n : ℕ} (x : Fin n → Bool) (gs : List Gate) (i : Fin n) :
    (scan false GateOp.eval gs (List.ofFn x)).getD i.val false = x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    change (List.ofFn x).getD i.val false = x i
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  | append_singleton gs g ih =>
    rw [scan_snoc, List.getD_append _ _ _ _ (by simp [scan_len]; omega)]
    exact ih

private abbrev hits {N : ℕ} (v : Fin (N + N)) (e : Fin N × Fin N) : Prop :=
  v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2

private def pairInput {N : ℕ} (e : Fin N × Fin N) (v : Fin (N + N)) : Bool :=
  decide (v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2)

private def pairs {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter fun e => I e.1 e.2 ∧ circuitFun (N + N) C (pairInput e) = true ∧
    lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false

private def Sound {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
  ∀ x : Fin (N + N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
    (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
    circuitFun (N + N) C x = false

private def degree {N : ℕ} (E : Finset (Fin N × Fin N)) (v : Fin (N + N)) : ℕ :=
  (E.filter fun e => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2).card

private def fanout (C : Circuit) (v : ℕ) : ℕ :=
  Fintype.card {j : Fin C.size // v ∈ (C.gates.get j).inputs}

private def Dense {N : ℕ} (E : Finset (Fin N × Fin N)) (C : Circuit) : Prop :=
  ∀ v : Fin (N + N), 0 < degree E v → 24 * max 1 (fanout C v.val) < degree E v

private lemma different_sides {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

private lemma singleton_false {q N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hq : 1 ≤ q) (hs : Sound q I C) (v : Fin (N + N)) :
    circuitFun (N + N) C (fun i => decide (i = v)) = false := by
  apply hs
  · apply Nat.le_trans _ hq
    rw [Fintype.card_subtype]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : Fin.natAdd N a = v := by simpa using (Finset.mem_filter.mp ha).2
    have hb' : Fin.natAdd N b = v := by simpa using (Finset.mem_filter.mp hb).2
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha'.trans hb'.symm)))
  · rintro ⟨p, l, _, hp, hl⟩
    exact different_sides p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)

private lemma pin_on {n : ℕ} (v : Fin n) (x : Fin n → Bool) {i : Fin n}
    (hi : pinned v x i = true) : x i = true := by
  unfold pinned at hi
  split at hi
  · contradiction
  · exact hi

private lemma result_sound {q N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hs : Sound q I C) (hao : IsAO2 (N + N) C) (v : Fin (N + N)) :
    Sound q I (result (N + N) v.val C) := by
  intro x hx hno
  rw [result_bool v C hao x]
  apply hs
  · refine Nat.le_trans (Fintype.card_le_of_injective
      (fun l : {l : Fin N // pinned v x (Fin.natAdd N l) = true} =>
        (⟨l.val, pin_on v x l.property⟩ : {l : Fin N // x (Fin.natAdd N l) = true})) ?_) hx
    intro a b he
    apply Subtype.ext
    exact congrArg (fun z : {l : Fin N // x (Fin.natAdd N l) = true} => z.val) he
  · rintro ⟨p, l, hI, hp, hl⟩
    exact hno ⟨p, l, hI, pin_on v x hp, pin_on v x hl⟩

private lemma pairs_keep {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hao : IsAO2 (N + N) C) (v : Fin (N + N)) (e : Fin N × Fin N)
    (he : e ∈ pairs I C) (hmiss : ¬ hits v e) :
    e ∈ pairs I (result (N + N) v.val C) := by
  have ha : v.val ≠ e.1.val := fun h => hmiss (Or.inl (Fin.ext h))
  have hb : v.val ≠ N + e.2.val := fun h => hmiss (Or.inr (Fin.ext h))
  have hx : pinned v (pairInput e) = pairInput e := by
    funext i
    by_cases hi : i = v
    · subst i
      change (if v = v then false else pairInput e v) = pairInput e v
      simp [pairInput, hits] at hmiss ⊢
      exact hmiss
    · simp [pinned, hi]
  change e ∈ Finset.univ.filter _ at he ⊢
  obtain ⟨_, hI, heval, hL, hP⟩ := Finset.mem_filter.mp he
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, ?_, ?_, ?_⟩
  · rw [result_bool v C hao, hx]
    exact heval
  · rw [result_single v C hao _ _ _ ha hb]
    exact hL
  · rw [result_single v C hao _ _ _ ha hb]
    exact hP

private lemma fanout_pos {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit}
    (hq : 1 ≤ q) (hs : Sound q I C) (v : Fin (N + N)) (e : Fin N × Fin N)
    (he : e ∈ pairs I C) (hve : hits v e) : 0 < fanout C v.val := by
  by_contra! hzero
  have hzero' : fanout C v.val = 0 := by omega
  have hout : C.output ≠ v.val := by
    intro hOut
    have hs' := singleton_false hq hs v
    change (scan false GateOp.eval C.gates (List.ofFn fun i => decide (i = v))).getD
      C.output false = false at hs'
    rw [hOut, scan_input] at hs'
    simp at hs'
  have htrue : circuitFun (N + N) C (pairInput e) = true :=
    (Finset.mem_filter.mp he).2.2.1
  have same := unused_result v C hzero' hout (pairInput e)
  have heq : pinned v (pairInput e) =
      if v = Fin.castAdd N e.1 then (fun i => decide (i = Fin.natAdd N e.2))
      else (fun i => decide (i = Fin.castAdd N e.1)) := by
    rcases hve with rfl | rfl
    · have hv := different_sides e.1 e.2
      funext i
      rw [ite_eq_left rfl]
      by_cases hi : i = Fin.castAdd N e.1
      · subst i
        rw [pinned, ite_eq_left rfl]
        exact (decide_eq_false_iff_not.mpr hv).symm
      · rw [pinned, ite_eq_right hi, pairInput]
        simp only [or_iff_right hi]
    · have hv := (different_sides e.1 e.2).symm
      funext i
      rw [ite_eq_right hv]
      by_cases hi : i = Fin.natAdd N e.2
      · subst i
        rw [pinned, ite_eq_left rfl]
        exact (decide_eq_false_iff_not.mpr hv).symm
      · rw [pinned, ite_eq_right hi, pairInput]
        simp only [or_iff_left hi]
  rw [htrue, heq] at same
  split at same
  · rw [singleton_false hq hs] at same
    contradiction
  · rw [singleton_false hq hs] at same
    contradiction

-- Charge the lost pairs to the gates removed by fixing one input.
set_option maxHeartbeats 1000000 in
private lemma densify {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q)
    (C : Circuit) (hao : IsAO2 (N + N) C) (hs : Sound q I C)
    (hmore : 24 * C.size < (pairs I C).card) :
    ∃ D, IsAO2 (N + N) D ∧ Sound q I D ∧
      24 * D.size < (pairs I D).card ∧ Dense (pairs I D) D := by
  suffices aux : ∀ k (C : Circuit), C.size = k → IsAO2 (N + N) C → Sound q I C →
      24 * C.size < (pairs I C).card →
      ∃ D, IsAO2 (N + N) D ∧ Sound q I D ∧ 24 * D.size < (pairs I D).card ∧ Dense (pairs I D) D by
    exact aux C.size C rfl hao hs hmore
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro C hsize hao hs hmore
    by_cases hd : Dense (pairs I C) C
    · exact ⟨C, hao, hs, hmore, hd⟩
    unfold Dense at hd
    push Not at hd
    obtain ⟨v, hp, hloss⟩ := hd
    have hp' : 0 < ((pairs I C).filter fun e => hits v e).card := hp
    obtain ⟨e, he⟩ := Finset.card_pos.mp hp'
    obtain ⟨he, hve⟩ := Finset.mem_filter.mp he
    have hread := fanout_pos hq hs v e he hve
    rw [max_eq_right (Nat.succ_le_of_lt hread)] at hloss
    let D := result (N + N) v.val C
    obtain ⟨hDao, hsave⟩ := result_size v C hao
    change D.size + fanout C v.val ≤ C.size at hsave
    let F := (pairs I C).filter fun f => ¬ hits v f
    have hF : F ⊆ pairs I D := by
      intro f hf
      obtain ⟨hpair, hmiss⟩ := Finset.mem_filter.mp hf
      exact pairs_keep hao v f hpair hmiss
    have hcards : degree (pairs I C) v + F.card = (pairs I C).card := by
      change ((pairs I C).filter fun e => hits v e).card + F.card = _
      exact Finset.card_filter_add_card_filter_not (s := pairs I C) (hits v)
    have hsub := Finset.card_le_card hF
    exact ih D.size (by omega) D rfl hDao (result_sound hs hao v) (by omega)

end PEqualNP.Outside.L_meta_3694

theorem PEqualNP.Outside.L_meta_3694 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     have x6 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => {x7 : Fin x2 × Fin x2 | x3 x7.1 x7.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x6 fun (x8 : Fin (x2 + x2)) => Decidable.decide (x8 = Fin.castAdd x2 x7.1 ∨ x8 = Fin.natAdd x2 x7.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x6 (x2 + x2) (fun (x8 : ℕ) => Decidable.decide (x2 ≤ x8)) (↑x7.1) (x2 + ↑x7.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x6 (x2 + x2) (fun (x8 : ℕ) => Decidable.decide (x8 < x2)) (↑x7.1) (x2 + ↑x7.2) = Bool.false};     have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin (x2 + x2) → Bool), Fintype.card { x9 : Fin x2 // x8 (Fin.natAdd x2 x9) = Bool.true } ≤ x1 → (¬∃ (x10 : Fin x2) (x11 : Fin x2), x3 x10 x11 ∧ x8 (Fin.castAdd x2 x10) = Bool.true ∧ x8 (Fin.natAdd x2 x11) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 x8 = Bool.false;     have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) =>       ∀ (x9 : Fin (x2 + x2)),         have x10 : ℕ := {x10 ∈ x6 x8 | x9 = Fin.castAdd x2 x10.1 ∨ x9 = Fin.natAdd x2 x10.2}.card;         (0 : ℕ) < x10 → (24 : ℕ) * Max.max (1 : ℕ) (Fintype.card { x12 : Fin x8.size // ↑x9 ∈ (x8.gates.get x12).inputs }) < x10;     ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x9 → x7 x9 → (24 : ℕ) * x9.size < (x6 x9).card → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x13 ∧ x7 x13 ∧ (24 : ℕ) * x13.size < (x6 x13).card ∧ x8 x13 := by
  intro q N I _ hq
  dsimp only
  intro C hao hs hmore
  exact PEqualNP.Outside.L_meta_3694.densify I hq C hao hs hmore
