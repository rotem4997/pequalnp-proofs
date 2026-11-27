import Mathlib
import PEqualNP.Defs

/-! Removing the unique reader of input zero in a binary AND/OR circuit. -/
namespace PEqualNP.Outside.L_meta_7889.PetersenPeel

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership TopForm

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem prefix_value (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step, Nat.add_comm, Nat.add_left_comm]

private theorem getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false = if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  by_cases he : i = w.length
  · subst i
    simp [step]
  · by_cases hi : i < w.length
    · simpa only [step, ite_eq_right he] using
        List.getD_append w [g.op.eval (g.inputs.map fun j => w.getD j false)] false i hi
    · rw [ite_eq_right he, List.getD_eq_default (step w g) false (by simp [step]; omega),
        List.getD_eq_default w false (by omega)]

private theorem map_values {l : List ℕ} {a b : ℕ → Bool}
    (h : ∀ k ∈ l, a k = b k) : l.map a = l.map b := List.map_congr_left h

private theorem prefix_unchanged (pre : List Gate) (a b : List Bool) (ha : a.length = b.length)
    (eq : ∀ i ≠ 0, a.getD i false = b.getD i false)
    (noZero : ∀ g ∈ pre, 0 ∉ g.inputs) :
    ∀ i ≠ 0, (pre.foldl step a).getD i false = (pre.foldl step b).getD i false := by
  induction pre generalizing a b with
  | nil => exact eq
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [step, ha]
    · intro i hi
      have hread := map_values (l := g.inputs) (fun k hk => eq k (fun e => noZero g (by simp) (e ▸ hk)))
      simp only [getD_step, ha, hread, eq i hi]
    · exact fun h hh => noZero h (by simp [hh])

private def remap (cut i : ℕ) : ℕ :=
  if i < cut then i else if i = cut then 0 else i - 1

private def remapGate (cut : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap cut)⟩

private theorem remap_output (cut l : ℕ) (h : cut < l) : remap cut l = l - 1 := by
  rw [remap, ite_eq_right (by omega : ¬ l < cut), ite_eq_right (by omega : l ≠ cut)]

private theorem suffix_unchanged (post : List Gate) (cut : ℕ) (a b : List Bool)
    (hcut : cut < a.length) (hlen : a.length = b.length + 1)
    (agree : ∀ i ≠ 0, a.getD i false = b.getD (remap cut i) false)
    (noZero : ∀ g ∈ post, 0 ∉ g.inputs) :
    ∀ i ≠ 0, (post.foldl step a).getD i false =
      ((post.map (remapGate cut)).foldl step b).getD (remap cut i) false := by
  induction post generalizing a b with
  | nil => exact agree
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [step]; omega
    · simp [step, hlen]
    · intro i hi
      have hop := map_values (l := g.inputs) (fun j hj =>
        agree j (fun e => noZero g (by simp) (e ▸ hj)))
      have ri : remap cut i = b.length ↔ i = a.length := by
        by_cases hc : i < cut
        · simp only [remap, ite_eq_left hc]; omega
        · by_cases he : i = cut
          · simp only [remap, ite_eq_right hc, ite_eq_left he]; omega
          · simp only [remap, ite_eq_right hc, ite_eq_right he]; omega
      simp only [getD_step, remapGate, List.map_map, Function.comp_def, ri, hop, agree i hi]
    · exact fun h hh => noZero h (by simp [hh])

private theorem initial_value (x : Fin 10 → Bool) (i : ℕ) (hi : i < 10) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi]
  rfl

private theorem updated_prefix (pre : List Gate) (noZero : ∀ g ∈ pre, 0 ∉ g.inputs)
    (x : Fin 10 → Bool) (b : Bool) :
    ∀ i ≠ 0, (pre.foldl step (List.ofFn x)).getD i false =
      (pre.foldl step (List.ofFn (Function.update x 0 b))).getD i false := by
  apply prefix_unchanged _ _ _ (by simp) _ noZero
  intro i hi
  by_cases hin : i < 10
  · rw [initial_value x i hin, initial_value _ i hin, Function.update_of_ne]
    exact fun e => hi (congrArg Fin.val e)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private def peeled (pre post : List Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ post.map (remapGate (10 + pre.length)), remap (10 + pre.length) out⟩

private def combine (isAnd : Bool) (a b : Bool) := if isAnd then a && b else a || b

def marked (isAnd swapped : Bool) (w : ℕ) : Gate :=
  ⟨if isAnd then GateOp.and else GateOp.or, if swapped then [w, 0] else [0, w]⟩

/-- Replace the removed gate by input zero and update that input with the gate's old value. -/
theorem peel_eval (pre post : List Gate) (out w : ℕ) (isAnd swapped : Bool)
    (hw0 : w ≠ 0) (hw : w < 10 + pre.length) (ho : out ≠ 0)
    (hpre : ∀ g ∈ pre, 0 ∉ g.inputs) (hpost : ∀ g ∈ post, 0 ∉ g.inputs)
    (x : Fin 10 → Bool) :
    let C : Circuit := ⟨pre ++ marked isAnd swapped w :: post, out⟩
    let D := peeled pre post out
    let v := (D.wires (List.ofFn (Function.update x 0 false))).getD w false
    D.eval (List.ofFn (Function.update x 0 (combine isAnd (x 0) v))) = C.eval (List.ofFn x) := by
  dsimp only
  let cut := 10 + pre.length
  let before := pre.foldl step (List.ofFn x)
  have hb : before.length = cut := by simp [before, cut, length_fold]
  have v_eq : ((peeled pre post out).wires (List.ofFn (Function.update x 0 false))).getD w false =
      before.getD w false := by
    change (((pre ++ post.map (remapGate cut)).foldl step (List.ofFn (Function.update x 0 false))).getD w false) = _
    rw [List.foldl_append, prefix_value]
    · exact (updated_prefix pre hpre x false w hw0).symm
    · simpa [length_fold, cut] using hw
  rw [v_eq]
  let val := combine isAnd (x 0) (before.getD w false)
  let after := pre.foldl step (List.ofFn (Function.update x 0 val))
  have ha : after.length = cut := by simp [after, cut, length_fold]
  have oldZero : before.getD 0 false = x 0 := by
    dsimp [before]
    rw [prefix_value _ _ _ (by simp), initial_value _ 0 (by decide)]
    rfl
  have newZero : after.getD 0 false = val := by
    dsimp [after]
    rw [prefix_value _ _ _ (by simp), initial_value _ 0 (by decide)]
    exact Function.update_self _ _ _
  have hgate : (marked isAnd swapped w).op.eval
      ((marked isAnd swapped w).inputs.map fun j => before.getD j false) = val := by
    simp only [List.getD_eq_getElem?_getD] at oldZero
    cases isAnd <;> cases swapped <;>
      simp [marked, GateOp.eval, val, combine, oldZero, Bool.and_comm, Bool.or_comm]
  have hpair : ∀ i ≠ 0, (step before (marked isAnd swapped w)).getD i false = after.getD (remap cut i) false := by
    intro i hi
    rcases lt_trichotomy i cut with hlt | rfl | hgt
    · simp only [getD_step, hb, ite_eq_right (ne_of_lt hlt), remap, ite_eq_left hlt]
      exact updated_prefix pre hpre x val i hi
    · rw [getD_step, hb, ite_eq_left rfl, hgate]
      simpa [remap] using newZero.symm
    · rw [getD_step, hb, ite_eq_right (ne_of_gt hgt), remap_output cut i hgt,
        List.getD_eq_default _ _ (by omega : before.length ≤ i),
        List.getD_eq_default _ _ (by omega : after.length ≤ i - 1)]
  change ((pre ++ post.map (remapGate cut)).foldl step _).getD (remap cut out) false =
    ((pre ++ marked isAnd swapped w :: post).foldl step _).getD out false
  simp only [List.foldl_append, List.foldl_cons]
  exact (suffix_unchanged post cut (step before (marked isAnd swapped w)) after
    (by simp [step, hb]) (by simp [step, hb, ha]) hpair hpost out ho).symm

private def good (bound : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < bound

private theorem shape (C : Circuit) : IsAO2 10 C ↔
    ∀ j g, C.gates[j]? = some g → good (10 + j) g := by
  constructor
  · rintro ⟨ops, back, length⟩ j g hj
    have he : gateAt C j = g := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
    have hlt := (List.getElem?_eq_some_iff.mp hj).1
    refine ⟨ops g (List.mem_of_getElem? hj), length g (List.mem_of_getElem? hj), ?_⟩
    simpa only [he] using back j hlt
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      exact (h j _ (List.getElem?_eq_getElem hj)).1
    · intro j hj
      have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      simpa only [he] using (h j _ (List.getElem?_eq_getElem hj)).2.2
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
      exact (h j _ (List.getElem?_eq_getElem hj)).2.1

private theorem remap_lt (cut i bound : ℕ) (hc : 0 < cut) (hb : cut < bound) (hi : i < bound) :
    remap cut i < bound - 1 := by
  unfold remap
  split <;> try omega
  split <;> omega

private theorem peeled_shape (pre post : List Gate) (out : ℕ) (g : Gate)
    (hC : IsAO2 10 ⟨pre ++ g :: post, out⟩) : IsAO2 10 (peeled pre post out) := by
  rw [shape] at hC ⊢
  intro j a hj
  change (pre ++ post.map (remapGate (10 + pre.length)))[j]? = some a at hj
  by_cases hpre : j < pre.length
  · rw [List.getElem?_append_left hpre] at hj
    exact hC j a (by simpa only [List.getElem?_append_left hpre] using hj)
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at hj
    cases he : post[j - pre.length]? with
    | none => simp [he] at hj
    | some b =>
      simp only [he, Option.map_some, Option.some.injEq] at hj
      subst a
      have hb : (pre ++ g :: post)[j + 1]? = some b := by
        rw [List.getElem?_append_right (by omega),
          show j + 1 - pre.length = (j - pre.length) + 1 by omega]
        simpa using he
      obtain ⟨hop, hlen, hbounded⟩ := hC (j + 1) b hb
      refine ⟨hop, by simpa [remapGate] using hlen, ?_⟩
      intro i hi
      rw [remapGate, List.mem_map] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      have hlt := remap_lt (10 + pre.length) k (10 + (j + 1)) (by omega) (by omega) (hbounded k hk)
      omega

private def padGate : Gate := ⟨GateOp.and, [1, 1]⟩

private def pad (D : Circuit) : Circuit :=
  ⟨D.gates ++ List.replicate (18 - D.size) padGate, D.output⟩

private theorem pad_shape (D : Circuit) (hD : IsAO2 10 D) : IsAO2 10 (pad D) := by
  rw [shape] at hD ⊢
  intro j g hj
  change (D.gates ++ List.replicate (18 - D.size) padGate)[j]? = some g at hj
  by_cases h : j < D.gates.length
  · rw [List.getElem?_append_left h] at hj
    exact hD j g hj
  · rw [List.getElem?_append_right (by omega)] at hj
    have hm := List.mem_of_getElem? hj
    obtain rfl := List.eq_of_mem_replicate hm
    simp [good, padGate]
    omega

private theorem pad_value (D : Circuit) (x : Fin 10 → Bool) (w : ℕ) (hw : w < 10 + D.size) :
    ((pad D).wires (List.ofFn x)).getD w false = (D.wires (List.ofFn x)).getD w false := by
  change ((D.gates ++ List.replicate (18 - D.size) padGate).foldl step (List.ofFn x)).getD w false = _
  rw [List.foldl_append]
  exact prefix_value _ _ _ (by simpa only [length_fold, List.length_ofFn, Circuit.size] using hw)

/-- Factor out the unique reader of input zero, preserving evaluation on every input. -/
theorem peel (pre post : List Gate) (out w : ℕ) (isAnd swapped : Bool)
    (hw0 : w ≠ 0) (hw : w < 10 + pre.length) (ho : out ≠ 0)
    (hpre : ∀ g ∈ pre, 0 ∉ g.inputs) (hpost : ∀ g ∈ post, 0 ∉ g.inputs)
    (hAO : IsAO2 10 ⟨pre ++ marked isAnd swapped w :: post, out⟩)
    (hout : out < 10 + (pre ++ marked isAnd swapped w :: post).length)
    (budget : (pre ++ marked isAnd swapped w :: post).length ≤ 19) :
    ∃ D : Circuit, IsAO2 10 D ∧ (16 ≤ D.size ∧ D.size ≤ 18) ∧
      (w ≠ 0 ∧ w < 10 + D.size ∧ ∀ j g, 10 + j ≤ w → D.gates[j]? = some g → 0 ∉ g.inputs) ∧
      ∀ x : Fin 10 → Bool,
        let v := (D.wires (List.ofFn (Function.update x 0 false))).getD w false
        circuitFun 10 D (Function.update x 0 (if isAnd = true then x 0 && v else x 0 || v)) =
          circuitFun 10 ⟨pre ++ marked isAnd swapped w :: post, out⟩ x := by
  let D := peeled pre post out
  have hlen : D.size = pre.length + post.length := by simp [D, peeled, Circuit.size]
  have hsmall : D.size ≤ 18 := by simp only [List.length_append, List.length_cons] at budget; omega
  have padSize : (pad D).size = 18 := by
    change (D.gates ++ List.replicate (18 - D.size) padGate).length = 18
    simp only [List.length_append, List.length_replicate]
    change D.size + (18 - D.size) = 18
    omega
  have hwd : w < 10 + D.size := by omega
  have houtD : D.output < 10 + D.size := by
    simp only [List.length_append, List.length_cons] at hout
    change remap (10 + pre.length) out < 10 + D.size
    unfold remap
    split <;> try omega
    split <;> omega
  refine ⟨pad D, pad_shape D (peeled_shape pre post out (marked isAnd swapped w) hAO),
    ⟨by omega, by omega⟩, ⟨hw0, by omega, ?_⟩, ?_⟩
  · intro j g hj hg
    have hjp : j < pre.length := by omega
    have hjd : j < (pre ++ post.map (remapGate (10 + pre.length))).length := by
      simpa [List.length_append] using (show j < pre.length + post.length by omega)
    change ((pre ++ post.map (remapGate (10 + pre.length))) ++ List.replicate (18 - D.size) padGate)[j]? = some g at hg
    rw [List.getElem?_append_left hjd, List.getElem?_append_left hjp] at hg
    exact hpre g (List.mem_of_getElem? hg)
  · intro x
    dsimp only
    rw [pad_value D _ w hwd]
    change ((pad D).wires _).getD D.output false = _
    rw [pad_value D _ D.output houtD]
    exact peel_eval pre post out w isAnd swapped hw0 hw ho hpre hpost x

end PEqualNP.Outside.L_meta_7889.PetersenPeel

/- Generic strict-live normalization, counting and relabeling adapted from L-meta-971. -/

namespace PEqualNP.Outside.L_meta_7889.PetersenNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## Core: strict binary DAGs, evaluation, and the shared definitions -/

/-- Gate operation: `true` is AND, `false` is OR. -/
def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

/-- A binary DAG: gate `j` is `(isAnd, a, b)` and, with `n` inputs, drives wire `n + j`. -/
abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

/-- One evaluation step: append the value of gate `g` read on the current wire list. -/
def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

/-- The wire list of `D` started from the wire list `w`. -/
def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

/-- Value of wire `w` of `D` on input `x` (`false` beyond the last wire). -/
def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

/-- Strict binary DAG on `n` inputs: both operands are earlier wires and they differ. -/
def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

/-- The gates reading wire `w`. -/
def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

/-- Every wire except the last one has a reader. -/
def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

/-- Strict, live, nonempty; the output is the last wire `n + D.length - 1`. -/
def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

/-- The output wire. -/
def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

/-- Singleton assignment. -/
def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

/-- Singleton support of a wire. -/
def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

/-- Surplus carried by a set of wires. -/
def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

/-- The wires other than the output. -/
def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

/-- Branching wires. -/
def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

/-- Eligible labels: carried by some branching wire. -/
def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

/-- Multiplicity-aware surplus units `⟨w, i⟩` with `i + 1 < fanout w`. -/
def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

/-- Arcs are operand positions `(gate, side)`; `false` is the first operand. -/
def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

/-- Union carrier of a label set `T`. -/
def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

/-- Difference carrier: wires carrying `x` and not `y`. -/
def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

/-- A choice of one pure branching carrier for every eligible label. -/
def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

/-! ### Evaluation lemmas -/

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

/-- The value of the gate `j` wire in terms of the wire list of the first `j` gates. -/
theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

/-- Wires of an initial segment agree with the full wire list below its length. -/
theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

/-- Values of an initial segment of a DAG. -/
theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

/-- The gate equation of a strict DAG. -/
theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

/-- A strict DAG has exactly one solution of its input and gate equations. -/
theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

/-! ## Block A: official Monotone2 circuits to strict live binary DAGs -/

/-- Symbolic reference: a Boolean constant or an emitted wire index. -/
abbrev Ref := Bool ⊕ ℕ

/-- Value of a symbolic reference on a wire list. -/
def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

/-- Stage-dependent lookup: an index not yet mapped reads constant false. -/
def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

/-- Two-operand simplifier: a reference, or two distinct emitted wires needing a gate. -/
def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

/-- One translation step for an official gate; the state is (map of old wires, emitted DAG). -/
def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

/-- A reference is valid below the bound `B`. -/
def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

/-- Structural invariant of the translation state. -/
def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

/-- One step keeps the invariant, emits at most one gate, and tracks the official fold. -/
theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

/-- The whole translation fold keeps the invariant and tracks the official wire list. -/
theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

/-- Translation: a constant, an input projection, or a strict DAG no larger than `C`. -/
theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

/-- Shift an operand index down past a deleted wire `c`. -/
def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

/-- Inverse shift: the old index of a new wire or gate. -/
def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

/-- Delete gate `j` and shift larger operand indices down by one. -/
def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

/-- Liveness by minimality: a strict DAG for a function with all inputs essential can be
replaced by a strict live one that is no larger. -/
theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

/-- The bridge from the official model to strict live binary DAGs. -/
theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

/-! ## Block B: surplus identity, supports, carrier flow, units -/

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

/-! ### Fanout and the global surplus identity -/

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

/-- Fanout counts the operand positions reading the wire. -/
theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem sum_fanout (hS : Strict n D) :
    ∑ w ∈ Finset.range (n + D.length), fanout D w = 2 * D.length := by
  rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
  intro e he
  have := sb_src_lt hS e he
  exact Finset.mem_range.mpr (by omega)

/-- The global identity `B = s - n + 1`, in addition form. -/
theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega

theorem Bplus_le_twelve (h13 : totalSurplus n D ≤ 13) (h0 : 1 ≤ Bzero n D) :
    Bplus n D ≤ 12 := by
  rw [totalSurplus_split] at h13; omega


end SurplusFlow

/-- The action of `σ` on wires: input wires are permuted, gate wires are fixed. -/
def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

/-- The DAG with every operand moved by `liftP σ`. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

/-- The relabelled DAG on `x` has the values of the old DAG on `x ∘ σ`. -/
theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]


end PEqualNP.Outside.L_meta_7889.PetersenNormalize

namespace PEqualNP.Outside.L_meta_7889.PetersenNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- If every input is read at least twice, a 19-gate strict live DAG has no shared gate. -/
theorem tight_readers {D : Dag} (live : StrictLive 10 D) (small : D.length ≤ 19)
    (repeated : ∀ i < 10, fanout D i ≠ 1) :
    D.length = 19 ∧ (∀ i < 10, fanout D i = 2) ∧
      (∀ w, 10 ≤ w → w + 1 < 10 + D.length → fanout D w = 1) := by
  classical
  let K := inner 10 D
  let needed (w : ℕ) : ℕ := if w < 10 then 1 else 0
  have hpos : 0 < D.length := List.length_pos_iff.mpr live.2.2
  have hfilter : K.filter (fun w => w < 10) = Finset.range 10 := by
    ext w
    simp only [K, Finset.mem_filter, sb_mem_inner, Finset.mem_range]
    omega
  have hneeded : ∑ w ∈ K, needed w = 10 := by
    change (∑ w ∈ K, if w < 10 then 1 else 0) = 10
    rw [← Finset.sum_filter, hfilter]
    simp
  have hp : ∀ w ∈ K, needed w ≤ fanout D w - 1 := by
    intro w hw
    by_cases h : w < 10
    · have hl := live.2.1 w (sb_mem_inner.mp hw)
      have hr := repeated w h
      simpa only [needed, if_pos h] using (show 1 ≤ fanout D w - 1 by omega)
    · simp [needed, h]
  have hid := surplus_identity live
  have hlo := Finset.sum_le_sum hp
  change (∑ w ∈ K, needed w) ≤ totalSurplus 10 D at hlo
  have heq : totalSurplus 10 D = 10 := by omega
  have hpoint : ∀ w ∈ K, needed w = fanout D w - 1 := by
    intro w hw
    by_contra hn
    have hl : needed w < fanout D w - 1 := lt_of_le_of_ne (hp w hw) hn
    have hs : (∑ i ∈ K, needed i) < totalSurplus 10 D :=
      Finset.sum_lt_sum hp ⟨w, hw, hl⟩
    omega
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    have hiK : i ∈ K := sb_mem_inner.mpr (by omega)
    have hiOne := hpoint i hiK
    simp only [needed, if_pos hi] at hiOne
    omega
  · intro w hw hlast
    have hwK : w ∈ K := sb_mem_inner.mpr hlast
    have hwZero := hpoint w hwK
    have hl := live.2.1 w hlast
    simp only [needed, if_neg (Nat.not_lt.mpr hw)] at hwZero
    omega

/-- Transfer the unique reader, using a target-preserving input permutation. -/
theorem normalize_dichotomy (F : (Fin 10 → Bool) → Bool)
    (hnc : ∀ b : Bool, ∃ x : Fin 10 → Bool, F x ≠ b)
    (hnp : ∀ i : Fin 10, ∃ x : Fin 10 → Bool, F x ≠ x i)
    (hess : ∀ i : Fin 10, ∃ x y : Fin 10 → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (haut : ∀ i : Fin 10, ∃ σ : Equiv.Perm (Fin 10), σ i = 0 ∧
      ∀ x : Fin 10 → Bool, F (fun j => x (σ j)) = F x)
    (C : Circuit) (mono : Monotone2 C) (size : C.size ≤ 19) (correct : circuitFun 10 C = F) :
    ∃ D : Dag, StrictLive 10 D ∧ D.length ≤ 19 ∧
      (∀ x : Fin 10 → Bool, val D x (outW 10 D) = F x) ∧
      (fanout D 0 = 1 ∨ (D.length = 19 ∧ (∀ i < 10, fanout D i = 2) ∧
        ∀ w, 10 ≤ w → w + 1 < 10 + D.length → fanout D w = 1)) := by
  have eq (x : Fin 10 → Bool) : C.eval (List.ofFn x) = F x := congrFun correct x
  obtain ⟨D, live, len, eval⟩ := normalize_strictLive C mono
    (fun b => by
      obtain ⟨x, hx⟩ := hnc b
      exact ⟨x, by rwa [eq]⟩)
    (fun i => by
      obtain ⟨x, hx⟩ := hnp i
      exact ⟨x, by rwa [eq]⟩)
    (fun i => by
      obtain ⟨x, y, hxy, hne⟩ := hess i
      exact ⟨x, y, hxy, by rwa [eq, eq]⟩)
  have hsmall : D.length ≤ 19 := len.trans size
  have hF (x : Fin 10 → Bool) : val D x (outW 10 D) = F x := (eval x).trans (eq x)
  by_cases h : ∃ i : Fin 10, fanout D i.val = 1
  · obtain ⟨i, hi⟩ := h
    obtain ⟨σ, hσ, hσF⟩ := haut i
    refine ⟨relabel σ D, relabel_strictLive σ live, by rwa [relabel_length], ?_, Or.inl ?_⟩
    · intro x
      rw [relabel_out σ live.1 live.2.2, hF, hσF]
    · have he : liftP σ i.val = 0 := by
        rw [tr_liftP_lt σ i.isLt]
        exact congrArg Fin.val hσ
      rw [← he, relabel_fanout, hi]
  · refine ⟨D, live, hsmall, hF, Or.inr (tight_readers live hsmall ?_)⟩
    intro i hi hr
    exact h ⟨⟨i, hi⟩, hr⟩

def toGate (g : Bool × ℕ × ℕ) : Gate :=
  ⟨if g.1 then .and else .or, [g.2.1, g.2.2]⟩

def toCircuit (n : ℕ) (D : Dag) : Circuit :=
  ⟨D.map toGate, outW n D⟩

theorem toCircuit_size (n : ℕ) (D : Dag) : (toCircuit n D).size = D.length := by
  simp [toCircuit, Circuit.size]

theorem toCircuit_eval (n : ℕ) (D : Dag) (x : Fin n → Bool) :
    circuitFun n (toCircuit n D) x = val D x (outW n D) := by
  unfold circuitFun Circuit.eval Circuit.wires toCircuit val wl
  simp only [List.foldl_map]
  congr 2
  funext w g
  obtain ⟨op, a, b⟩ := g
  cases op <;> simp [toGate, wstep, gop, GateOp.eval]

theorem toCircuit_AO2 (n : ℕ) (D : Dag) (strict : Strict n D) :
    PEqualNP.TopForm.IsAO2 n (toCircuit n D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ D.map toGate at hg
    obtain ⟨⟨op, a, b⟩, _, rfl⟩ := List.mem_map.mp hg
    cases op <;> simp [toGate]
  · intro j hj i hi
    change j < (D.map toGate).length at hj
    rw [List.length_map] at hj
    have ho := strict j hj
    have aux : PEqualNP.MetaComplexity.NestedCover.gateAt (toCircuit n D) j =
        toGate D[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, toCircuit, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]
    rw [aux] at hi
    simp [toGate] at hi
    have ha : opA D j = D[j].2.1 := opA_eq D j hj
    have hb : opB D j = D[j].2.2 := opB_eq D j hj
    rw [ha, hb] at ho
    rcases hi with rfl | rfl
    · exact ho.1
    · exact ho.2.1
  · intro g hg
    change g ∈ D.map toGate at hg
    obtain ⟨⟨op, a, b⟩, _, rfl⟩ := List.mem_map.mp hg
    rfl

/-- The unique direct reader of input zero exposes an ordered gate-list split. -/
theorem reader_split {D : Dag} (live : StrictLive 10 D) (only : fanout D 0 = 1) :
    ∃ (pre post : List Gate) (w : ℕ) (isAnd swapped : Bool),
      (toCircuit 10 D).gates = pre ++
        (⟨if isAnd then .and else .or, if swapped then [w, 0] else [0, w]⟩ : Gate) :: post ∧
      w ≠ 0 ∧ w < 10 + pre.length ∧
      (∀ g ∈ pre, 0 ∉ g.inputs) ∧ (∀ g ∈ post, 0 ∉ g.inputs) := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp only
  have hjmem : j ∈ readers D 0 := by rw [hj]; exact Finset.mem_singleton_self j
  obtain ⟨hjlt, hoperand⟩ := Finset.mem_filter.mp hjmem
  have hjlen : j < D.length := Finset.mem_range.mp hjlt
  let L := (toCircuit 10 D).gates
  have hL : L.length = D.length := by simp [L, toCircuit]
  have hjL : j < L.length := by rwa [hL]
  have hMap (k : ℕ) (hk : k < L.length) (hkD : k < D.length) :
      L[k] = toGate D[k] := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem hk]
    change (D.map toGate)[k]? = some _
    simp only [List.getElem?_map, List.getElem?_eq_getElem hkD, Option.map_some]
  have hGet (k : ℕ) (hk : k < L.length) :
      L[k].inputs = [opA D k, opB D k] := by
    have hkD : k < D.length := by rwa [← hL]
    rw [hMap k hk hkD, opA_eq D k hkD, opB_eq D k hkD]
    rfl
  have hUnique (k : ℕ) (hk : k < L.length) (hs : 0 ∈ L[k].inputs) : k = j := by
    rw [hGet k hk] at hs
    have hm : k ∈ readers D 0 := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by rwa [← hL]), ?_⟩
      simpa [eq_comm] using hs
    rwa [hj, Finset.mem_singleton] at hm
  let pre := L.take j
  let post := L.drop (j + 1)
  have hpreLen : pre.length = j := List.length_take_of_le hjL.le
  have hsplit : L = pre ++ L[j] :: post := by
    dsimp only [pre, post]
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hpre : ∀ g ∈ pre, 0 ∉ g.inputs := by
    intro g hg hbad
    obtain ⟨k, hk, hkg⟩ := List.mem_take_iff_getElem.mp hg
    have hkL : k < L.length := by omega
    have he := hUnique k hkL (hkg.symm ▸ hbad)
    omega
  have hpost : ∀ g ∈ post, 0 ∉ g.inputs := by
    intro g hg hbad
    obtain ⟨k, hk, hkg⟩ := List.mem_drop_iff_getElem.mp hg
    have hkL : j + 1 + k < L.length := by omega
    have he := hUnique (j + 1 + k) hkL (hkg.symm ▸ hbad)
    omega
  have hob (swapped : Bool) (w : ℕ)
      (hin : [opA D j, opB D j] = if swapped then [w, 0] else [0, w]) :
      L[j] = ⟨if tag D j then .and else .or, if swapped then [w, 0] else [0, w]⟩ := by
    rw [hMap j hjL hjlen]
    unfold toGate
    rw [← tag_eq D j hjlen, ← opA_eq D j hjlen, ← opB_eq D j hjlen, hin]
  have hs := live.1 j hjlen
  rcases hoperand with ha | hb
  · refine ⟨pre, post, opB D j, tag D j, false, ?_, ?_, ?_, hpre, hpost⟩
    · rw [← hob false (opB D j) (by simp [ha])]
      exact hsplit
    · intro h
      exact hs.2.2 (ha.trans h.symm)
    · simpa [hpreLen] using hs.2.1
  · refine ⟨pre, post, opA D j, tag D j, true, ?_, ?_, ?_, hpre, hpost⟩
    · rw [← hob true (opA D j) (by simp [hb])]
      exact hsplit
    · intro h
      exact hs.2.2 (h.trans hb.symm)
    · simpa [hpreLen] using hs.1

theorem toCircuit_out {D : Dag} (live : StrictLive 10 D) :
    (toCircuit 10 D).output ≠ 0 ∧ (toCircuit 10 D).output < 10 + (toCircuit 10 D).size := by
  have hpos : 0 < D.length := List.length_pos_iff.mpr live.2.2
  rw [toCircuit_size]
  change 10 + D.length - 1 ≠ 0 ∧ 10 + D.length - 1 < 10 + D.length
  omega

/-- The exact target in the released L-meta-7889 statement. -/
def target (x : Fin 10 → Bool) : Bool :=
  decide (∃ i : Fin 5,
    (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
     x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
     x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))) = true)

def adj (i j : Fin 10) : Prop :=
  (i.val, j.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)] : List (ℕ × ℕ)) ∨
  (j.val, i.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)] : List (ℕ × ℕ))

instance (i j : Fin 10) : Decidable (adj i j) := by unfold adj; infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 25000 in
theorem target_spec (x : Fin 10 → Bool) :
    target x = true ↔ ∃ i j, adj i j ∧ x i = true ∧ x j = true := by
  revert x
  decide +kernel

def autMap (i j : Fin 10) : Fin 10 :=
  let j₀ := j.val % 5
  let i₀ := i.val % 5
  if i.val < 5 then
    Fin.ofNat 10 ((j₀ + 5 - i₀) % 5 + if j.val < 5 then 0 else 5)
  else
    Fin.ofNat 10 (((j₀ + 5 - i₀) * 3) % 5 + if j.val < 5 then 5 else 0)

set_option maxHeartbeats 0 in
theorem aut_data : ∀ i : Fin 10,
    Function.Bijective (autMap i) ∧ autMap i i = 0 ∧
      ∀ j k, adj (autMap i j) (autMap i k) ↔ adj j k := by decide +kernel

theorem target_aut (i : Fin 10) : ∃ σ : Equiv.Perm (Fin 10), σ i = 0 ∧
    ∀ x : Fin 10 → Bool, target (fun j => x (σ j)) = target x := by
  obtain ⟨bij, hz, hadj⟩ := aut_data i
  let σ : Equiv.Perm (Fin 10) := Equiv.ofBijective (autMap i) bij
  refine ⟨σ, hz, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [target_spec]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨σ u, σ v, (hadj u v).mpr huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨σ.symm u, σ.symm v, (hadj _ _).mp ?_, by simpa, by simpa⟩
    change adj (σ (σ.symm u)) (σ (σ.symm v))
    simpa only [Equiv.apply_symm_apply] using huv

def partner (i : Fin 10) : Fin 10 := Fin.ofNat 10 (i.val + 5)

theorem partner_adj : ∀ i : Fin 10, adj i (partner i) ∧ i ≠ partner i := by decide +kernel

theorem adj_loopless : ∀ i : Fin 10, ¬ adj i i := by decide +kernel

theorem target_zero : target (fun _ => false) = false := by decide +kernel

theorem target_single (i : Fin 10) : target (single i) = false := by
  by_contra h
  have ht : target (single i) = true := Bool.eq_true_of_not_eq_false h
  obtain ⟨u, v, hadj, hu, hv⟩ := (target_spec _).mp ht
  simp only [single, decide_eq_true_eq] at hu hv
  subst u
  subst v
  exact adj_loopless i hadj

theorem target_full : target (fun _ => true) = true := by decide +kernel

theorem target_nonconstant (b : Bool) : ∃ x : Fin 10 → Bool, target x ≠ b := by
  cases b
  · exact ⟨fun _ => true, by rw [target_full]; decide⟩
  · exact ⟨fun _ => false, by rw [target_zero]; decide⟩

theorem target_nonprojection (i : Fin 10) : ∃ x : Fin 10 → Bool, target x ≠ x i := by
  exact ⟨single i, by simp [target_single, single]⟩

theorem target_essential (i : Fin 10) : ∃ x y : Fin 10 → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ target x ≠ target y := by
  let x : Fin 10 → Bool := fun j => decide (j = i ∨ j = partner i)
  refine ⟨x, single (partner i), ?_, ?_⟩
  · intro k hk
    simp [x, single, hk]
  · have ht : target x = true := (target_spec x).mpr
      ⟨i, partner i, (partner_adj i).1, by simp [x], by simp [x]⟩
    rw [ht, target_single]
    decide

theorem petersen_normalize (C : Circuit) (mono : Monotone2 C) (size : C.size ≤ 19)
    (correct : circuitFun 10 C = target) :
    ∃ D : Dag, StrictLive 10 D ∧ D.length ≤ 19 ∧
      (∀ x : Fin 10 → Bool, val D x (outW 10 D) = target x) ∧
      (fanout D 0 = 1 ∨ (D.length = 19 ∧ (∀ i < 10, fanout D i = 2) ∧
        ∀ w, 10 ≤ w → w + 1 < 10 + D.length → fanout D w = 1)) :=
  normalize_dichotomy target target_nonconstant target_nonprojection target_essential target_aut
    C mono size correct

end PEqualNP.Outside.L_meta_7889.PetersenNormalize

namespace PEqualNP.Outside.L_meta_7889.PetersenAssemble

open CircuitLowerBounds MetaComplexity TopForm PetersenPeel PetersenNormalize

/-- The only outstanding case after extracting the single read is a 19-gate formula. -/
def TwiceFormulaImpossible : Prop :=
  ∀ D : Dag, StrictLive 10 D → D.length = 19 → (∀ i < 10, fanout D i = 2) →
    (∀ w, 10 ≤ w → w + 1 < 10 + D.length → fanout D w = 1) →
    (∀ x : Fin 10 → Bool, val D x (outW 10 D) = target x) → False

theorem normal_form (noFormula : TwiceFormulaImpossible) (C : Circuit) (mono : Monotone2 C)
    (small : C.size ≤ 19) (correct : circuitFun 10 C = target) :
    ∃ (D : Circuit) (w : ℕ) (isAnd : Bool),
      IsAO2 10 D ∧ (16 ≤ D.size ∧ D.size ≤ 18) ∧
      (w ≠ 0 ∧ w < 10 + D.size ∧ ∀ j g, 10 + j ≤ w → D.gates[j]? = some g → 0 ∉ g.inputs) ∧
      ∀ x : Fin 10 → Bool,
        let v := (D.wires (List.ofFn (Function.update x 0 false))).getD w false
        circuitFun 10 D (Function.update x 0 (if isAnd = true then x 0 && v else x 0 || v)) =
          circuitFun 10 C x := by
  obtain ⟨D, live, hsmall, hd, once | ⟨hlen, htwice, htree⟩⟩ := petersen_normalize C mono small correct
  · obtain ⟨pre, post, w, isAnd, swapped, hgates, hw0, hw, hpre, hpost⟩ := reader_split live once
    let out := (toCircuit 10 D).output
    let rebuilt : Circuit := ⟨pre ++ marked isAnd swapped w :: post, out⟩
    have eq : toCircuit 10 D = rebuilt := by
      change (toCircuit 10 D) = ⟨pre ++ marked isAnd swapped w :: post, (toCircuit 10 D).output⟩
      change (toCircuit 10 D).gates = pre ++ marked isAnd swapped w :: post at hgates
      rw [← hgates]
    obtain ⟨ho, hlt⟩ := toCircuit_out live
    have hao := toCircuit_AO2 10 D live.1
    have hs : (toCircuit 10 D).size ≤ 19 := by simpa only [toCircuit_size] using hsmall
    rw [eq] at hlt hao hs
    obtain ⟨E, heao, heSize, heWire, heEq⟩ := peel pre post out w isAnd swapped hw0 hw ho
      hpre hpost hao hlt hs
    refine ⟨E, w, isAnd, heao, heSize, heWire, fun x => ?_⟩
    dsimp only
    rw [heEq x]
    change circuitFun 10 rebuilt x = circuitFun 10 C x
    rw [← eq, toCircuit_eval, hd, correct]
  · exact (noFormula D live hlen htwice htree hd).elim

end PEqualNP.Outside.L_meta_7889.PetersenAssemble

/-
A checker for LRAT unsatisfiability certificates (RUP steps) written so that the kernel can
evaluate it fast: every loop is a raw recursor (`List.rec`, `Nat.rec`, `Trie.rec`) and every
branch a raw `Bool.rec` / `Option.rec` (pattern matching compiles to matchers and `brecOn`, which
measured three times slower in the kernel); there is no HashMap, no USize, no Array, no
well-founded recursion. A certificate accepted by `check` becomes a theorem through
`check_sound` and `decide +kernel`, by kernel reduction alone.

Representation:
* a literal is a natural number: variable `v` positive is `2 * v`, negative is `2 * v + 1`;
* a formula is a `List (List Nat)`; the certificate gives every clause a key in the store
  (formula clauses through a key list, derived clauses through their first token), so that the
  most used clauses can sit near the root;
* an assignment is `a : Nat → Bool`; literal `l` is true under `a` iff `a (l / 2) = (l % 2 == 0)`;
* a stored clause is ONE natural number, its bitmask (bit `l` set iff `l` is in the clause), in
  a binary trie keyed by key;
* the certificate is a flat token list: per step, the key of the new clause, its literals, `0`,
  then its hints `h1 u1 h2 u2 ... hk`: each `h` a clause key, each `u` the literal that hint makes
  unit (supplied because `Nat.log2` is not a kernel primitive), `hk` the hint that is falsified;
  the step ends there. The run succeeds when an empty clause is derived;
* during a RUP check the only state is ONE bitset `F` of literals known false (it starts as
  the new clause): reading a hint is a few GMP operations (`land`, `xor`, `shiftLeft`, `beq`),
  primitive in the kernel, whatever the clause length;
* a long certificate can be cut into segments, one theorem each (`checkFirst`, `checkSeg`,
  `checkLast`): the clauses still to be used at a cut are stated as a list, which bounds the
  kernel's memory per theorem (its caches live for one declaration) and lets the segments be
  checked in parallel. Soundness never depends on the keys, the unit literals, or the cuts
  being chosen well: a bad choice only makes the checker reject.
-/

namespace PEqualNP.Outside.L_meta_7889.KWCert.LRAT

-- The definitions use raw recursors, which the code generator does not compile; they are for
-- the kernel only.
noncomputable section

/-- The negation of a literal (flip the low bit). -/
def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

/-- Bit `l` of `T`, written with the kernel's GMP primitives only. -/
def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

/-- `T` with bit `u` set. -/
def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

/-- The truth value of literal `l` under the assignment `a`. -/
def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

/-- A clause is satisfied by `a` when one of its literals is true. -/
def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

/-- A formula (list of clauses) is satisfiable when one assignment satisfies every clause. -/
def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

/-! ## The clause store: a binary trie keyed by clause id -/

/-- Key `0` sits at the root, odd key `2j+1` at key `j` of the left child, even key `2j+2` at
key `j` of the right child. -/
inductive Trie where
  | nil : Trie
  | node (v : Option Nat) (l r : Trie) : Trie

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  Trie.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := Trie.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t

/-- Store `o` at key `k`; `fuel` bounds the depth (64 is plenty). Out of fuel: no change. -/
def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

/-- Every clause stored in the trie has property `P`. -/
def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

theorem All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (r.get _) (l.get _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

theorem All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

theorem All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

theorem All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

theorem All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

/-! ## Bit lemmas -/

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

/-! ## Clauses as bitmasks -/

/-- The bitmask of a clause. -/
def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

/-! ## The checker -/

/-- The type of the token machine's continuation: store, key slot, mode, `C`, `F`, `P`. -/
abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

/-! Each branch of the machine is its own constant, so that the kernel instantiates only the
branch taken (measured: same time, a third of the memory). -/

/-- Reading a clause. The first token of a step is the key the new clause will be stored
under (the slot `id` then holds key + 1; `0` means a key is expected). After it, `0` ends the
clause and starts its hints with `F := C`, and a literal joins `C`. -/
def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

/-- `x` is the unit literal claimed for the pending hint: `P` must be exactly `{x}`; then `x`
is true, so its negation joins `F`. -/
def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

/-- The hint clause is `D`: if every literal of `D` is in `F`, the clause `C` is derived (and if
`C` is empty, the certificate is accepted) and stored under its key; otherwise the literals of
`D` not in `F` wait for the claimed unit literal. -/
def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

/-- `x` is a hint key: look the clause up (a missing clause rejects). -/
def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)

/-- One token. State: the store `db`, the key slot `id`, the mode (`false`: reading a new
clause into the bitmask `C`; `true`: reading its hints), the bitset `F` of literals known false,
and `P`: `0` when a hint key is expected, otherwise the bitset of literals not false of the last
hint clause, waiting for its unit literal. `k` is the machine on the remaining tokens. -/
def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

/-- The end of the tokens, when the certificate must have derived the empty clause: reject. -/
def stop : Cont := fun _ _ _ _ _ _ => false

/-- The token machine on a token list, then the continuation `e`. -/
def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

/-- The machine on the `W`-bit fields of one word (lowest first, up to a sentinel top bit `1`;
`M = 2 ^ W - 1`; at most `fuel` fields), then `k`. No token list is built. -/
def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

/-- At most this many fields per word. -/
def fuelW : Nat := 1024

/-- The machine on a packed certificate (a list of words of `W`-bit fields), then `e`. -/
def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

/-- Is the clause of the entry `q :: lits` stored under key `q - 1`? (Entries carry key + 1 so
that no entry token is `0`, the clause separator of `decodeF`.) -/
def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e

/-- The end of a segment: every entry `q :: lits` of `B` must be stored under key `q - 1`. -/
def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

/-- Store the formula's clauses: clause `i` under key `q - 1` where `q` is the `i`-th entry of
`fk`; `q = 0` leaves the clause out. -/
def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

/-- Store the entries `q :: lits` of a list of live clauses, under key `q - 1`. -/
def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

/-- The checker, one theorem: formula `F` with keys `fk`, certificate as a token list. -/
def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

/-- The checker, one theorem: formula `F` with keys `fk`, packed certificate. -/
def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

/-- First segment of a cut certificate: from the formula to the live clauses `B`. -/
def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

/-- A middle segment: from the live clauses `B` to the live clauses `B'`. -/
def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

/-- The last segment: from the live clauses `B` to the empty clause. -/
def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

/-! ## Soundness -/

section Soundness

variable (a : Nat → Bool)

/-- A bitmask clause is satisfied by `a`. -/
def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

/-- Every literal in the bitset is false under `a`. -/
def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

/-- Every entry `q :: lits` of a list of live clauses has its clause `lits` satisfied. -/
def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

/-- The invariant of hint mode: if `a` falsifies the clause `C` being derived, then `F` holds
only false literals, and a pending `P` contains a true literal. -/
def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

/-- A satisfied clause `D` keeps a true literal outside the false literals `F`. -/
theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

/-- A continuation is good for `Q` when it accepts only, from a state satisfying the invariant
(the store holds only clauses `a` satisfies, and the hint-mode invariant), if `Q` holds. -/
def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

theorem stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

theorem tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    · -- unit literal
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    · -- hint key
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h
          -- the clause `C` is satisfied by `a`
          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

theorem runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

theorem runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

theorem runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

theorem clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

theorem verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

theorem loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

theorem loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

/-- SOUNDNESS (token list). If the checker accepts the token list `toks` for the formula `F`
(with keys `fk`), then no assignment satisfies every clause of `F`. -/
theorem check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

/-- SOUNDNESS (packed certificate, one theorem). -/
theorem checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

/-- SOUNDNESS of a first segment: every assignment satisfying `F` satisfies the live clauses
`B`. -/
theorem checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

/-- SOUNDNESS of a middle segment. -/
theorem checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

/-- SOUNDNESS of the last segment. -/
theorem checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

/-! ## Packed certificates

Elaborating a long list literal costs about 0.2 ms per number, so certificates are stored as a
list of big numbers (words), each holding several `W`-bit fields (lowest first) under a
sentinel top bit; `unpack` turns them back into the token list, lazily, inside the kernel. The
soundness theorem holds for every token list, so `unpack` needs no proof. -/

/-- The fields of one word, prepended to `rest`; `fuel` bounds the number of fields. -/
def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

/-- The token list of a packed certificate (fields of `W` bits, at most 1024 per word). -/
def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

/-- A formula from a token list: each clause is its literals followed by `0`. -/
def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end

end PEqualNP.Outside.L_meta_7889.KWCert.LRAT


namespace PEqualNP.Outside.L_meta_7889.KWCert

open PEqualNP.Outside.L_meta_7889.KWCert.LRAT (litVal ClauseSat FormulaSat)

def pos (i : Fin 15) (v : Fin 10) : Bool :=
  (![3, 33, 160, 6, 66, 320, 12, 132, 640, 24, 264, 288, 17, 528, 576] :
    Fin 15 → Nat) i |>.testBit v.val

def neg (i : Fin 15) (v : Fin 10) : Bool :=
  (![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] :
    Fin 15 → Nat) i |>.testBit v.val

def edgeFn (x : Fin 10 → Bool) : Bool :=
  decide (∃ i : Fin 5, ((x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
    (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))) = true)

theorem pos_accept : ∀ i : Fin 15, edgeFn (pos i) = true := by decide +kernel
theorem neg_reject : ∀ i : Fin 15, edgeFn (neg i) = false := by decide +kernel

abbrev Tables := Fin 10 → Fin 2 → Fin 15 → Bool
private abbrev Slot := Fin 10 × Fin 2

private def var (s : Slot) (i : Fin 15) (right : Bool) : Nat :=
  s.1.val * 60 + s.2.val * 30 + (if right then 15 else 0) + i.val + 1

private def assignment (row col : Tables) (x : Nat) : Bool :=
  let z := x - 1
  let v : Fin 10 := ⟨(z / 60) % 10, by omega⟩
  let t : Fin 2 := ⟨(z / 30) % 2, by omega⟩
  let i : Fin 15 := ⟨z % 15, by omega⟩
  if z % 30 < 15 then row v t i else col v t i

private theorem assignment_var (row col : Tables) (s : Slot) (i : Fin 15) (b : Bool) :
    assignment row col (var s i b) = if b then col s.1 s.2 i else row s.1 s.2 i := by
  obtain ⟨v, t⟩ := s
  have hv := v.isLt
  have ht := t.isLt
  have hi := i.isLt
  cases b <;>
    simp only [assignment, var, Bool.false_eq_true, ite_false, ite_true,
      Nat.add_sub_cancel, Nat.add_zero] <;>
    first
    | have hv' : ((v.val * 60 + t.val * 30 + i.val) / 60) % 10 = v.val := by omega
      have ht' : ((v.val * 60 + t.val * 30 + i.val) / 30) % 2 = t.val := by omega
      have hi' : (v.val * 60 + t.val * 30 + i.val) % 15 = i.val := by omega
      have hl : (v.val * 60 + t.val * 30 + i.val) % 30 < 15 := by omega
      simp [hv', ht', hi', hl]
    | have hv' : ((v.val * 60 + t.val * 30 + 15 + i.val) / 60) % 10 = v.val := by omega
      have ht' : ((v.val * 60 + t.val * 30 + 15 + i.val) / 30) % 2 = t.val := by omega
      have hi' : (v.val * 60 + t.val * 30 + 15 + i.val) % 15 = i.val := by omega
      have hl : ¬ (v.val * 60 + t.val * 30 + 15 + i.val) % 30 < 15 := by omega
      simp [hv', ht', hi', hl]

private def rowLit (s : Slot) (i : Fin 15) : Nat := 2 * var s i false
private def colLit (s : Slot) (j : Fin 15) : Nat := 2 * var s j true

private theorem lit_pos (a : Nat → Bool) (n : Nat) : litVal a (2 * n) = a n := by
  have hdiv : 2 * n / 2 = n := by omega
  have hmod : 2 * n % 2 = 0 := by omega
  simp [litVal, hdiv, hmod]

private theorem lit_neg (a : Nat → Bool) (n : Nat) : litVal a (2 * n + 1) = !(a n) := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp [litVal, hdiv, hmod]

private def slots (i j : Fin 15) : List Slot :=
  (List.finRange 10).flatMap fun v =>
    if pos i v && !(neg j v) then (List.finRange 2).map (fun t => (v, t)) else []

private theorem mem_slots (i j : Fin 15) (s : Slot)
    (p : pos i s.1 = true) (n : neg j s.1 = false) : s ∈ slots i j := by
  unfold slots
  refine List.mem_flatMap.mpr ⟨s.1, List.mem_finRange _, ?_⟩
  simp only [p, n, Bool.not_false, Bool.and_self, ite_true]
  exact List.mem_map.mpr ⟨s.2, List.mem_finRange _, Prod.eta _⟩

private def coverage (i j : Fin 15) : List Slot → List (List Nat)
  | [] => [[]]
  | s :: ss => (coverage i j ss).flatMap fun c => [rowLit s i :: c, colLit s j :: c]

private theorem coverage_sat (i j : Fin 15) (a : Nat → Bool) (opts : List Slot)
    (s : Slot) (hs : s ∈ opts) (hrow : litVal a (rowLit s i) = true)
    (hcol : litVal a (colLit s j) = true) : ∀ c ∈ coverage i j opts, ClauseSat a c := by
  induction opts with
  | nil => cases hs
  | cons p ps ih =>
    intro c hc
    rw [coverage, List.mem_flatMap] at hc
    obtain ⟨c', hc', he⟩ := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases List.mem_cons.mp hs with rfl | hmem
    · rcases he with rfl | rfl
      · exact ⟨rowLit s i, by simp, hrow⟩
      · exact ⟨colLit s j, by simp, hcol⟩
    · obtain ⟨lit, hmem', hval⟩ := ih hmem c' hc'
      rcases he with rfl | rfl <;> exact ⟨lit, List.mem_cons_of_mem _ hmem', hval⟩

private def separate (i j : Fin 15) (opts : List Slot) : List (List Nat) :=
  opts.flatMap fun s => (opts.filter (fun t => t != s)).map fun t =>
    [rowLit s i + 1, colLit s j + 1, rowLit t i + 1, colLit t j + 1]

private theorem separate_sat (i j : Fin 15) (opts : List Slot)
    (row col : Tables)
    (hdisj : ∀ v t w u, row v t i = true → col v t j = true →
      row w u i = true → col w u j = true → v = w ∧ t = u) :
    ∀ c ∈ separate i j opts, ClauseSat (assignment row col) c := by
  intro c hc
  unfold separate at hc
  obtain ⟨s, _, ht⟩ := List.mem_flatMap.mp hc
  obtain ⟨t, hne, rfl⟩ := List.mem_map.mp ht
  have hts : t ≠ s := by simpa using (List.mem_filter.mp hne).2
  have hrow (a : Slot) :
      litVal (assignment row col) (rowLit a i + 1) = !(row a.1 a.2 i) := by
    simp [rowLit, lit_neg, assignment_var]
  have hcol (a : Slot) :
      litVal (assignment row col) (colLit a j + 1) = !(col a.1 a.2 j) := by
    simp [colLit, lit_neg, assignment_var]
  cases e₁ : row s.1 s.2 i
  · exact ⟨rowLit s i + 1, by simp, by simp [hrow, e₁]⟩
  cases e₂ : col s.1 s.2 j
  · exact ⟨colLit s j + 1, by simp, by simp [hcol, e₂]⟩
  cases e₃ : row t.1 t.2 i
  · exact ⟨rowLit t i + 1, by simp, by simp [hrow, e₃]⟩
  cases e₄ : col t.1 t.2 j
  · exact ⟨colLit t j + 1, by simp, by simp [hcol, e₄]⟩
  exact (hts (Prod.ext (hdisj _ _ _ _ e₁ e₂ e₃ e₄).1 (hdisj _ _ _ _ e₁ e₂ e₃ e₄).2).symm).elim

def formula : List (List Nat) :=
  (List.finRange 15).flatMap fun i => (List.finRange 15).flatMap fun j =>
    coverage i j (slots i j) ++ separate i j (slots i j)

theorem noPartitionOfUnsat (hunsat : ¬ FormulaSat formula)
    (row col : Tables)
    (hrow : ∀ v t i, row v t i = true → pos i v = true)
    (hcol : ∀ v t j, col v t j = true → neg j v = false)
    (hcover : ∀ i j, ∃ v t, row v t i = true ∧ col v t j = true)
    (hdisj : ∀ i j v t w u, row v t i = true → col v t j = true →
      row w u i = true → col w u j = true → v = w ∧ t = u) : False := by
  apply hunsat
  refine ⟨assignment row col, ?_⟩
  intro c hc
  unfold formula at hc
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hi
  rcases List.mem_append.mp hj with hcov | hsep
  · obtain ⟨v, t, hr, hn⟩ := hcover i j
    exact coverage_sat i j _ _ (v,t) (mem_slots i j _ (hrow v t i hr) (hcol v t j hn))
      (by simpa [rowLit, lit_pos, assignment_var] using hr)
      (by simpa [colLit, lit_pos, assignment_var] using hn) c hcov
  · exact separate_sat i j _ row col (hdisj i j) c hsep


set_option maxRecDepth 30000 in
private def words : List Nat := [
  1455016533560253368, 1364942118502093971, 1989239474104587362, 1449385692662616874, 1997346454389331093, 1381830836550361821, 1989516825912939621, 1416142370930434798, 1152994021190873995, 1211794244330041768, 1998343909428802230, 1447127950317630375, 1340414498178834432, 1211798367549223339,
  1998625177240453754, 1483171315866227635, 1411717336012567703, 1616289335524828906, 1415917485627609963, 1391390950088760251, 1271985437459698551, 1340414498477638239, 1399418688098806044, 1152993331345748815, 1272877539511483325, 1323526000881644187, 1447269502808516891, 1483735229637735455,
  1402410673173676032, 1609255556033656532, 1391076975827162021, 1348753372042667415, 1430242747229729655, 1345884844401008640, 1288355400296817086, 1399279812127194049, 1211797585241572323, 1328996138633294458, 1289203948412576190, 1479218707995999170, 1616229336191956117, 1415649067558413147,
  1572095888354653911, 1419521994948088694, 1152989209988592523, 1278502331190997416, 2000757475259826842, 1433053375673971635, 1348279511480545280, 1278506454410178987, 2001038743071470174, 1483171318080574435, 1555772376321361047, 1394548683523429286, 1265853953773835858, 2001494083354039178,
  1451637458428085036, 1378945930724201619, 1364502875887051504, 1385757022954165288, 1426587525454181172, 1483172140600562845, 1381391581998505984, 1959117630953417626, 1383787829808534265, 1451639108911531051, 1483735229838947377, 1430044064543814813, 1442627737742097349, 1449520898561336328,
  1408283572380146631, 1452202333751600088, 1333096217476587520, 1790224495863693805, 1345602613458825841, 1242760370476304674, 1408283611828839005, 1451638284437259303, 1348575967823302656, 1776713624654823632, 1334067429857985136, 1224183472934601152, 1336185365447160472, 1449663764448983335,
  1483171316000510997, 1616289335521313943, 1415917485627609963, 1399274449449831370, 1447135302110647119, 1776713624652350513, 1336887264866366064, 1300744801538908606, 1391404560563092429, 1152993334147253177, 1278505187311053772, 1336760546621026910, 1819784658593433767, 1429951101769722830,
  1152994571215524894, 1291732656092209598, 1328998956601602696, 1811057041442701519, 1323235798833656516, 1452202333759664382, 1153003094343767175, 2001073933897563071, 1411437181125047257, 1645848469207406165, 1399028986018341811, 1289201211210687953, 1328722155555967683, 1790222361936029981,
  1323809880335663745, 1293704626942230977, 1336185571605590726, 1455017221234166055, 1483735229838947379, 1447270594252518557, 2001919755799070872, 1426586392053175329, 1348473034259858437, 1446849085808489295, 1322946684195345378, 1272028337822736593, 1349984785427018335, 1790789435813290484,
  2004825804790674093, 1430243299099587407, 1348473014865241108, 1278782470684783021, 1331687194030428800, 1775308311322106071, 1350956067601916588, 1399420127348642111, 1434746280973538283, 1616229335990621319, 1415649067558413147, 1323703611279335826, 1446849085976507275, 1340414487986869218,
  1273159981342638528, 1322946695692919479, 1242475116632672420, 2006096153079435929, 1479224894058284002, 1153003094343767187, 1442626773270300717, 1449520899920262152, 1822055181160897471, 1435103553521210358, 1555772376610719845, 1394548683523429286, 2005852950617298514, 1339835124729676382,
  1273158360881651921, 1333096219111547547, 1789940887731085811, 2006514724377035377, 1429965327709024890, 1446932563145946148, 1776436272846962895, 1350956135625700012, 1224460274198118847, 1350252722364826204, 1429965327717734608, 1483171316168291364, 1617145521246307479, 1398760361790710679,
  1272310513752646033, 1350548148075618911, 1798954343360905710, 1328714182569034413, 1818937003294099745, 1402631503855604365, 1152994570946392911, 1292018391794164158, 1348576105939747524, 1211511219843422455, 1334067430553686620, 1452337972709527870, 1482608366248932401, 2004101853998576789,
  1430381425139217445, 2006707658471590040, 1394821636529157031, 1645848331298629354, 1402410671468520371, 1211230468752927706, 1345602613962150552, 1278789167495098797, 1322949856060002944, 1787977228632922356, 1479224892380498912, 1772166473289659541, 1433196175239189464, 1331585633038144647,
  1447135302110573451, 1211795407944811569, 1340694668774109878, 1251482284950591809, 1352509126828487260, 1408428392359336254, 1447135302111138727, 1323805963177562112, 1273159981342499262, 1328714182569034423, 1251764857022765374, 1345894670983754440, 1449663765724150049, 1483735229637268501,
  1394548683523428352, 2009230650337826386, 1399270329509342180, 1340414487987164181, 1273722862408843758, 1322946694669779639, 1251764857022765374, 1345894670983754440, 1487106193414314273, 1483735229838947485, 1426589141973184512, 1443194755096857568, 1416309737736917986, 1651191271034103191,
  1419598651015386006, 2009792244155212178, 1339835124729672286, 1273721310902182097, 1335351180189242011, 1242756833167655262, 2010454960299565765, 1485423938937721583, 1970377180546335907, 1375924397993603839, 1487099182819734570, 1364518531647526035, 1971225728698723226, 1359035967103808315,
  1449385655921443879, 1946962433826968723, 1364645882719744813, 1443894698315727936, 1153002132204041245, 1946169578416684008, 1381534380315738865, 1449805741596705855, 1483735229838947287, 1426585963035505821, 1772797142562120711, 1434887362265728028, 1444316653386016811, 1479224927251764232,
  1483172142513771683, 1429477696626118656, 1999389241078925415, 1438500493705446421, 1741557391918250949, 1399420139904111592, 1651195394253284759, 1407965404670010202, 1211230468769704918, 1345602339084243608, 1278789167478321579, 1322949856194409088, 1812747715388840151, 1432779941866593260,
  1483735229838947289, 1442629114610582685, 1451773660448306184, 1768576033268525100, 1437921876012897299, 1617137949205773267, 1398760361790710679, 1272308589573742993, 1348279511955599995, 1798670944238749859, 1335914541226914495, 1250636309167718654, 1479219842041152199, 1487113479382455443,
  1430056314653814784, 2011209644365462469, 1447269512423437341, 1782085596727172076, 1450230289727910884, 1757880121659832333, 1415917485118272500, 1608407007935166065, 1323703575709815657, 1211795407947411880, 1340694668774093494, 1293421505952872694, 1328998887361340042, 1364519120727208283,
  1487112929558795213, 1369012385749147648, 1440080424917451555, 1482610289017674735, 1988953845002142869, 1385901091516863274, 1439231876835246883, 1485425041771887600, 1455716767699129495, 1442627682075248970, 1432296088189965320, 2001641437153631213, 1310855199962624972, 1152989896980664895,
  1770786253283416006, 2013812934656717242, 1429652723814625841, 1276894195822301184, 1771071851563194318, 2014375814884028798, 1443471240460194187, 1432778360546725888, 1752489417791502338, 2014659696118669754, 1483734952628286009, 1442627855144977561, 1315515026037289954, 2014269323884898665,
  1277755870558351755, 1671143223308556069, 1310860285283811726, 1445936972680753727, 1277755879617221606, 1671143223308556072, 1443471283215024526, 1445936975114237073, 1313291133354267622, 1899428577399524050, 1310673601444614661, 1729972302992145398, 1277479823198024063, 1280921735492577074,
  1449388538169856589, 1499442922657940499, 1276894195817279882, 1686630115034547978, 1260591875392184789, 1516052779705657427, 1310869493741040051, 1152993884253713427, 1659606798712990712, 1267328513559531900, 1722935507242555239, 1275166108160463231, 1516056902891284564, 1310855200123437431,
  1446573788738048529, 1269866117962547200, 1766569549636544601, 1293976838043016188, 1260374233373160019, 1697889320714340104, 1269545403712643547, 1293976826929993859, 1152993196691894787, 1678184902586763016, 1285063362294731218, 1754740726536321002, 1275451774421250430, 1302032758815193219,
  1449388537162978323, 1264229745998942208, 1499447045811443556, 1277177664683479494, 1687469453632977028, 1260865583907651994, 1260374681657898304, 1449949288328081909, 1268174793965977600, 1731101516634023119, 1301894274977061890, 1659602696363050003, 1285063362294731192, 1730815918505239759,
  1303549177180691460, 1686598078490030669, 1260591875928674773, 1294151954328053069, 1446540390068073009, 1260005698226372608, 1754462080835622759, 2019451299339489722, 1446540390737056125, 1666360000185893919, 1280795745133629835, 1449917128160344070, 1260374989287273037, 1668615923186763528,
  1263907245524361671, 1314808174229886981, 1152989759543341645, 1678184902586763016, 1281118520967856594, 1499162012672571367, 1265373238524195190, 1311040780791133451, 1429680067356529215, 1268174999877881856, 1755026889654187808, 1280568695844557268, 1660451224632997925, 1268456749624304008,
  1756436244148516838, 1320433553621113868, 1685472177039569425, 1277480304805183897, 1311041002653197645, 1438654968555852759, 1276894195822411776, 1754747679048292197, 2021702823268635006, 1438654967213674876, 1276894189421728727, 1667771291594934026, 1277753946667372999, 1752770966688589006,
  1269883160826524054, 1294008036712580427, 1152956354259128915, 1822056143887665305, 1302797112244753398, 2021588644932057549, 1268174793965977980, 1754464749134488781, 1282261806432276922, 1502541632528484105, 1285588790206685558, 1293966656699185248, 1298006736818385489, 1858900231595452775,
  2024498952525709845, 1320433561710498784, 1483172131303920209, 1773082658360788131, 1433341723412435996, 2016560577773410494, 1302797111472939569, 1443616684327004519, 1487112929559057369, 1433341722380746752, 1772519777751669743, 1294008036215200797, 1686598070334222897, 1260591875928674773,
  1438831810293917005, 1303549177181295575, 1260005698226475008, 1754462080835622759, 2027613867505668538, 1426867592110179115, 1946680957574976601, 1364645882618913581, 1434610078516626460, 1466270035055309793, 1988957969059939425, 1367320718390334190, 1440080424313471779, 1481751158118612005,
  1885115342980645975, 1369012317029667928, 1440080424917451555, 1465720484409515046, 1466100436970418176, 1946736651538463781, 1364645882719740717, 1381411514076742720, 1152997871545603081, 1946757398631180971, 1364645882719740717, 1449528527176975424, 1318748827167556566, 2019654598087672919,
  1432639890364851231, 1921702268302870681, 1455717748433917030, 1444316656372123978, 1364231847604810760, 1378998667451505409, 2029223282984874796, 1318748827167556566, 2019654598087672919, 1432639890364851231, 1364523378970582056, 1465717806833193993, 1369577191262842880, 1460630018000511801,
  1381830836876419864, 1378996089582037933, 1359312633043133168, 1465712582685021350, 1364523342010684513, 1959686424948288410, 1358455013813740341, 1378434723800269894, 1372257251702747926, 1364242024419660797, 1470783804174988257, 1991209697855669335, 1384209424578175810, 1385474349245651830,
  1371990756230980314, 1378437334335165438, 1426873021317913647, 1364242004472927329, 1385191254847888175, 1375924810310464278, 1990928396375472946, 1358453363724464902, 1489623386545837181, 1482033458602609713, 1435033304713237655, 1743529093157977079, 1468525958522666034, 1367320705750103145,
  1460630018000427891, 1443758119313388312, 2031686400843584599, 1384209424108331759, 1460907369808780150, 1434733740206228188, 1152997870891570125, 1385758328020491058, 2032603867916821240, 1470783806490072041, 1364231847604862976, 1385754204801309487, 2032885550058591028, 1470783804376224717,
  1153002407148745873, 2031476689938119727, 1434540328995730440, 1433060033587051573, 1482324209668531168, 1962230662152848528, 1464974468143174754, 1917446618846583359, 1264314410402570823, 1667769714150761679, 1265075064311464377, 1429683098655930404, 1432295933076898903, 1740989647187503297,
  1391372575338210339, 1152989210290410373, 1251764654890865161, 2038323045568197320, 1152984672222344355, 1572098728435332823, 1320437684406582346, 1263680121240163287, 1534913314790439040, 1446530400850084314, 1429683915712319995, 1731102270633804769, 1263907245489430983, 1293975326225124371,
  1432493725428232785, 1260591325640962048, 1659885116301285350, 2039411901813551544, 1432787913544184323, 1449100750147138645, 1432296088198475776, 1905057664602048666, 1319745190950806072, 1674816220452694746, 1446716242728239604, 1822059373669533705, 1312407667968377846, 2038480295235197353,
  1280568695982063999, 1534909191638857857, 1310859462125846942, 1449100749056381503, 1430044218629926912, 1660447031251720167, 1260865378103460232, 1753057374250935501, 1277177880924676562, 1783171908863150089, 1433987538008192021, 1481900847458460890, 1465716844559733730, 1443122223249192032,
  1430044218629927966, 1965043728649702053, 1468934014692803731, 1892114278847102029, 1300319361900675641, 1752493700579264317, 1263680128056373630, 1499167024060532489, 1446640993017065846, 1678222290260055847, 1275451853861810642, 1739542727248210113, 1482597506858548304, 1367320774469866661,
  1460630018000427892, 1434744873248006936, 2040130651151742109, 1384209492827808495, 1460907369808780151, 1434154572959609564, 1466842332283950225, 1313261223705187287, 1928139162915949266, 1318600255409926673, 1487675602512460810, 1429692583126586461, 2040762200787780577, 1297765196354716223,
  1933209219186547263, 1316643262725726800, 1855235962245012165, 1447134513925784080, 1152989213110195347, 1782931257047271433, 2041609215797433377, 1465157594247885315, 1296372518944887899, 1673126340705867557, 1446526277869113924, 1466842332283401361, 1722063924179596445, 1264245208882647433,
  1831030167000868047, 1310954870179897918, 1899147157905066706, 1467355242342644823, 1313261223705687125, 1669463042840270624, 1482037479822701060, 1466842332283401185, 1260943436798588061, 1731102270635616338, 1263907245489430983, 1891265730748611671, 1312989652741931517, 1432924898839512888,
  1465154033286780069, 1449100750147122267, 1432296090315206656, 2039921603851946138, 1482444814705886352, 2042454089660451923, 1433024505371475034, 1260867295618405335, 1660169822385198884, 1482001195986743748, 1429692583126586339, 1932642212315661281, 1293785996313760312, 1730257901137214554,
  1260591325607449019, 1482183214731134729, 1465154033286796259, 1152993813993215067, 1918601098172434587, 1482444813382268003, 1830467217150520404, 1313261233341108790, 1934614120185711314, 1302011029410394646, 2013712432301803307, 1320008591463301721, 2019089810259396466, 1469057470261670963,
  1465145649258427425, 1152993813992965211, 1905061787821017243, 1310674837540803068, 1722090194093194318, 1276894264772534665, 1468391075123848399, 1394768654800425943, 1432296070515377047, 1635730695563085978, 1483203066280207516, 1949853489778235021, 1467242554371253338, 1638828569692255858,
  1432924873661744288, 2028385968591543388, 1449666930778854349, 1781532279093462028, 1295513328982283285, 1905057664600123753, 1319745190950806072, 1917448819950562010, 1302033981427147335, 1499456137988717658, 1277755871687512518, 1770797592383035173, 2044489513990914468, 1466843292309209603,
  1152989759543841877, 1933209219186547263, 1321998640267240016, 1673127370592377472, 1302033981530358260, 1499456137988717658, 1277755871888982470, 1770797593356113701, 2044770988967625124, 1466838620425303011, 1152993813992969301, 1781522784514345115, 1314653695111459861, 1916598072392260162,
  1277831395044217355, 1729972247543146578, 1280795745098699147, 1450517736622266152, 1429687635324294175, 1772797610004841500, 1296101155283411928, 2039606195242711705, 1267346792773919163, 1668613928727910374, 1263907245386424775, 1731941766824802309, 1447216657284244452, 1502300570342077707,
  1465153929187836302, 1394768654867723361, 1432296070515377047, 1634882215126861978, 1483767734304711814, 1949576066985727629, 1427010393253958742, 1444602028092898105, 1433206828572062752, 1831029535959940193, 1312989652879405570, 1909567107983805140, 1446716242625004101, 1822059373652756489,
  1312407667968377846, 2038480296208325068, 1280568695982063999, 1534909191638857857, 1450475998728978846, 1483732206148490271, 1773010895954080853, 1296372604177327072, 1934899718348049106, 1315515026037289554, 1669744374304791236, 1446716243097416180, 1783212456575847440, 1415602064524139620,
  1152993812918154091, 1772797610009431134, 1483567690823377880, 1636852472285263470, 1466314498170025058, 1951546321525921420, 1465556385829356696, 1444602028092087350, 1314653695111476256, 1916598072392260163, 1310674837641650699, 2020499108902783423, 1446935397358670823, 1449950251183397054,
  1449100750969476247, 1430044218629926912, 1899428098812910147, 1277831395044143621, 1722091843377162322, 1281118520480928137, 1730816727921943758, 1433411943773926419, 1516377548942813002, 1265033842961158579, 1432467053994207268, 1260942612164867063, 1765723692771027026, 1269545403677712859,
  1416728101878396808, 1449096347720790949, 1430044218629926912, 1885399701982108772, 1479262416795255956, 1624750491261249200, 1482442478105056349, 2012908282624707349, 1450230291078603725, 1831029535959940197, 1312989652879409666, 1900278433752353492, 1446716242624954945, 1822059373652756489,
  1312407667968377846, 2046361595556223436, 1426550580907326568, 1442913453307069459, 1282262012826510366, 1667483906340332751, 1484298313890020457, 1446218447993005201, 1446359735270925346, 1900276646911400512, 1277833180743909953, 1740386959640487896, 1276897014538105231, 1310869873232357157,
  1394768654800425899, 1429829591056368535, 1884824650739951624, 1486938588269683856, 1632630347634603605, 1466879165925475423, 1949858025381112601, 1449666927457662102, 1831033659111521385, 1318921862715290174, 1867058334421576409, 1415613877426822251, 1892074808870810475, 1479264134581253211,
  1885113401744104003, 1426873263801582680, 1399281878105596472, 1483567672107864923, 1635167813205822003, 1470546174760703072, 1964213865856465967, 1466283640973605997, 1432493037850317911, 1381954463382843392, 1440640621326746652, 1466271411776425070, 1152988385976636503, 1959117427345374317,
  1375921922976518905, 1297818393896993571, 1455013914300724309, 1438114700729144339, 1312401749209650071, 1934616669651724649, 1318600185804132886, 1470492090952711175, 1462375909851317257, 1637139582292616880, 1483767734439117982, 1885677195088189013, 1469205046196593752, 2048643721599724347,
  1426867594090355824, 1152989758469330005, 1635445164577721382, 1487434743055877276, 2040492556202424995, 1443480081359365097, 1411661140509152205, 1885677407180948449, 1468291214437864596, 1465577721341314783, 1411656052918342741, 1485822584001978368, 1636852472285263470, 1482152894196434018,
  1465153617454905897, 1411666636691411959, 2049490311574455265, 1451642819571117172, 1470546174693543936, 1417265069360110643, 1438114700729144233, 1430044201982215063, 1820653852718627943, 1451428758087308309, 2047517187278710792, 1465577677645083732, 1442911666369780851, 1479088623084184606,
  1949858074639038062, 1296372537675043930, 1669749257514748626, 1260582941864919540, 1499444655024551941, 2050952375626305990, 1446538473252319615, 1449666928875479040, 1499444655024551941, 2051234056761446854, 1429368491906745479, 1411656052918342569, 1442913453307069468, 1483767731990856734,
  1949858074639029845, 1467242554371253338, 2050866165711911487, 1281133776239165823, 1671425507836344360, 1296259116649771388, 1399276240224739889, 1741767173538935643, 1443474341684610084, 2051180877983114246, 1465859299852616839, 1951265262708037204, 1298099458996868248, 1718149630923106665,
  1282262012826509754, 1668328331270464719, 1455013921215044730, 1411666635449086885, 2050058587455095777, 1417300260769553531, 1411666635449086885, 1885395657494103009, 1479262416795255956, 1952667396154670063, 1417265112991564894, 1438114700729144233, 1432296070515377047, 1772803106677816423,
  1438500494729561048, 2051430571862449275, 1313156961183572477, 1449096348962743244, 1451428758383771648, 1609273024740657704, 1483567622036866183, 2047207063394290452, 1302982630351213059, 1399276240979673589, 1442840748272218971, 1312989661819339806, 2047806650389433044, 1297765196354716223,
  1854675025725192653, 1443720692062575743, 1394768654800426021, 1899187999938184087, 1484131053815153757, 1411632544726124173, 1399276240225063945, 1884832707624567643, 1484399815921149072, 2050340056564528725, 1345513557097143425, 1335477886936793694, 1278508005899831578, 1430044218629927578,
  1251764857022765373, 1421203245288907464, 1652035629357949136, 1391366834575029116, 1275708647753033111, 1429829606790898600, 1820653852718942252, 1427016232696321045, 1669185217144849412, 1302797111484658164, 1277553675205594238, 1429367118859743733, 1718123275495748145, 1263397759760044414,
  1502258164502427687, 1280272033966657970, 1545893659635315915, 1318782576548076677, 1152993188437123613, 1502545002953944196, 1260008583715467638, 1754743969169274919, 1275177516063392212, 1687470751686039400, 1318783049900272774, 1152993814997308374, 1671425782915228890, 1271559709031297404,
  1545611293704865754, 1263625496658608562, 1449105964128565001, 1152993188437123661, 1718153735602744454, 1263397759760044414, 1502258164502427687, 1280272033966657970, 1545893659685647563, 1302984854316661896, 1449104863936733751, 1319685678560727040, 2055653030159694284, 1485425179209170057,
  1367320774469260325, 1460630018000427892, 1487675776282309400, 2056174722676806665, 1384209492827808495, 1460907369808780151, 1426867629372637916, 1411661142086218785, 1772797610004841500, 1438837494215914456, 1296413515631909054, 1465144065590146147, 1446290070528066588, 1300319371054310434,
  1831033237500082751, 1277471439460983358, 1499448778210179078, 2059959711313371530, 1152998004806235211, 1266415939457013332, 1483731102441258135, 1478987193833316352, 1555772353441068657, 1399270329845136538, 1402796379700589589, 1289484635549148625, 1328722154531656387, 1447121075074369712,
  1999035302302626649, 1421570830992470903, 1303009196899034878, 1323526000583746442, 1211795070305939879, 2063083154072490678, 1399283935295853151, 1318753909853914143, 1345614983467963029, 1447121076081010867, 1405808972841218923, 1278501111186605827, 1355340782308610714, 1778964773864972497,
  1399283935294766243, 1442913728755401676, 1328996207352771614, 1798953619373679046, 1426575329047411876, 1449666928942727168, 1779813972567375011, 1328722017647252141, 1296414888593727941, 1487671892742886545, 1298061368804635667, 1831031122312583771, 1318600255409926718, 1465716708119059463,
  1471178237647295517, 1985857550132886567, 1375925221511402243, 1482188626777522979, 1466847281293907037, 1296414850142041107, 1909847274740222674, 1297765197748654661, 2018211908760323896, 1465149555075959980, 1773010894612149339, 1449666928875480032, 1939966267928840914, 1295513328980075096,
  2018243187077818729, 1318600255513285137, 1689169940673812941, 1467401365325077677, 1444529596791108693, 1298061386487718944, 2044955191202901139, 1487671617864981678, 1426586875095274657, 1443474341881733120, 1920017275843845291, 1482726906985616484, 1932642222755687227, 1317208066546647608,
  1484297893665503038, 1449949298162291797, 1315177269554225152, 1891265324488301151, 1314653695344648707, 1296415520272468415, 1466847418732860561, 1298061368804635667, 1831031122312608410, 1318600255410000446, 1394768932741258247, 1442840746929861651, 1478987193826878494, 1638828569692587698,
  1483767734439117984, 1902847168667563686, 1482442065828308052, 1920018173961800469, 1296415477014918288, 1928987573156547282, 1301711756037886541, 1429679653689961474, 1446580669546828885, 1933209219184460831, 1317208067785634384, 1674811473657833832, 1482042016836927988, 1152988317441684614,
  1635165271809754847, 1443474341881734240, 2050340057235716771, 1429473710561219621, 1916598080447056027, 1302011304254636555, 1855241056898189117, 1485941434841330252, 1446580670318101657, 1444602303167333324, 1300319439773787168, 1831033237500082752, 1429829460051845694, 1740672557802825688,
  1260008583648309707, 1483734199021823783, 1638465855744455827, 1443474341881734244, 1920302874005691571, 1449524200676705440, 1951252745243949892, 1296415763333366936, 1892396996864740050, 1295513329114665535, 2047201896462035305, 1394785117721117654, 1426575325893735443, 1483567691744727040,
  2068916561536120430, 1467793547202827409, 1653162971183545495, 2069509665986409342, 1399271016018031451, 1275710161792533452, 1462375909851624360, 1635449220569169073, 1487434743089456284, 1585347841838630327, 1411437666371691391, 1921992051944733769, 2069908585909933140, 1466843293265777148,
  1312989644333040659, 1674816220452314284, 1446558885338508474, 1651132229695988558, 1415283823836087190, 1949566624449291270, 1466314497666212950, 1950983646483961484, 1468291214437864594, 1648113258278037175, 1449528873584968808, 1891265332661013158, 1302011304389218819, 1855240085497440617,
  1483734234085487180, 1152988314136032151, 1634870718036083124, 1467444246115337290, 2068921528179296809, 1391121023717719228, 1411437166705034150, 2070031032030757300, 1483203066001601686, 1885394944484021901, 1467242554405766228, 1648398856440366770, 1482000785319060644, 1449949299168900261,
  1302011029511315456, 1855240085497199168, 2071304475545866828, 1483735915087680657, 1932642223019525139, 1317208136505111096, 1674811473658174149, 2071585606153794036, 1426575327185134611, 1415283823836086272, 2069476476389262742, 1466990144542122843, 1612932340718840589, 1484332814444090502,
  1608987293082028587, 1486306506686825547, 1920018173961848544, 1394469970385822864, 1152994019329004366, 1265577358584973060, 1352366465739760522, 1312002663850502486, 1323523937930117787, 1319037444672750061, 1391108351027884693, 1265511511602390037, 1449666928942728074, 2072284641837680364,
  1339838285967475312, 1798952350932263167, 1336041261167071917, 1311151953956907349, 2072816100165661279, 1152992509497521236, 2011220255737203242, 1421802483390901445, 1152992506509890469, 1636853984130279088, 1465854421273277538, 2072863003174841152, 1404682263727645780, 1919438776597829121,
  2073532370256737425, 1152992509497275536, 1364534047904467497, 1465721380112249892, 1443474324198310941, 1449929398067108656, 2073977804616250136, 1465721381387080851, 1443474324198310941, 1988953848647146634, 1381954463382844202, 1439514721419904032, 1421789156845374665, 1482988985393714085,
  1632055095368198760, 1410853134874383215, 1451365601486087681, 1152988317609481363, 1959966179103638532, 1359033767946236725, 1399276310765548538, 1444588428342592460, 1391553203425788960, 2071439920957374866, 1430328167574311955, 2073122219600496794, 1465553224594809990, 1635445165080816399,
  1487434743055877276, 1919454062286802118, 1451787064058295395, 2074551161259924680, 1365065826150490923, 1449933418726923056, 1483167161240245016, 1442277796977169555, 1487434743022298120, 1988957971866082442, 1367320787109815022, 1440361899357291299, 1482609330232425678, 1365065813559645213,
  1460629467841960820, 1483173414762959640, 2075596495935583241, 1381954531918193391, 1460906819650313079, 1462343304430461660, 1479231629472732139, 1430044064542536724, 1651200571332736622, 1419598582295909270, 1999940619970339218, 1446853760730619089, 1482444795857912683, 1772235073010558647,
  1443474341948892120, 1922266402308897769, 1446643476786996326, 2075102420412565547, 1466679193227822154, 1609255556033656434, 1391076976028902309, 1999948067460572625, 1479226540741573842, 1487152648681250816, 1391399134535957165, 1430044064542536724, 2004733676234901547, 1466279520942341332,
  1971169279239902355, 1359035968001164091, 1487258062525760291, 1449395144267699287, 1364231847605518336, 1458936597321874264, 2077918454290199320, 1449391158504878831, 1970095155025282057, 1375924397859287807, 1443761521808995325, 1364535024321418329, 1970943703177669530, 1359035966969492283,
  1443761658979517434, 1487258045448270877, 1313306839865518765, 1485982631673271315, 1648680700779430943, 1317208136505111656, 1674811473658174148, 2079185430524981748, 1485982631673271315, 1648680700779430943, 1296101155286127720, 1929264924930914970, 1314653695861051921, 1462488711469255103,
  1485982630633108635, 1152994018339144839, 1772229567549126254, 1481867296152142808, 2076786520626379994, 1402410671468520371, 1318655134636322003, 1821987541767516668, 1320308560131363830, 1933204530558868582, 1301711755904016976, 1485416308518288400, 1152988317609440404, 2078487687764935684,
  1366899330164958295, 1439514687278269472, 1381672301530661617, 1433325093088486177, 1449391813638664973, 1442840746929861652, 1478987673736594462, 2072862178524391097, 1466100575200154708, 1952954112568294616, 1485179780760188058, 2080454518093006560, 1364783733721477940, 1439516544801368986,
  1375924328292614877, 1440361758059685030, 2080999628110345005, 1426587561367004234, 1443474343835254784, 2080462215781664434, 1364783733721477940, 1439516544801368986, 1375924328292614877, 1440361758059685030, 2081281103087055661, 1446848950148960764, 1318655093690408960, 1469090764734479044,
  1741767172197270557, 1433987548733281238, 1949003674495617177, 1465020373894677650, 1648115663426071777, 1300319361903240296, 1675096100402436806, 1318600255513211462, 2020466529780710502, 1303983347397931583, 1874939300372523368, 1465720729612403285, 1449391843551646699, 1783706944749876244,
  1465020370704241638, 1637135004495117119, 1487241847320523850, 1648676362582121679, 1296137448430163048, 1929265476182501041, 1310674848481870353, 2020503983824882111, 2082235956599190079, 1152992509497275526, 2030356552099432113, 1466843020182994150, 1772166468054631442, 1411437181119439832,
  1277398576724096680, 1432933252370076494, 1483173242034092993, 1399283869160486023, 1432915661831110656, 1415891512260987845, 1447287911559775083, 1772235073010412768, 1450793650028635096, 1742116148490568708, 1435103553520833512, 2073421012422051941, 1466679055721841808, 2082431510245665561,
  1465264396751832139, 2082714899821709866, 1398760361790170263, 1265856176234919636, 1419299171514004362, 2074250981028644587, 1432933251695076283, 1273720044272352327, 1331391014075519671, 1446445585508272412, 1415890895437603924, 1885400941142737771, 1393962370040693908, 1757880121659656235,
  1394539616854242292, 2038221289867875922, 1415283892052104087, 1658230415292048849, 1391086047140287364, 1278501109677042899, 1351957653749420698, 1778683297915183313, 1391399202590235882, 1334067350956585945, 1211795549513562287, 1434725084619788982, 1152981650678019043, 1211797985112586421,
  2084069806073184890, 1430232576747779049, 1328722017961029632, 1278784493362616535, 2084351694842172058, 1391393154338271927, 1345885039370875865, 1278503776112193965, 1419546738965750366, 1152989207505449835, 1272028991412993261, 1340414498477634143, 1301767830637390108, 1485988128106820566,
  1449666911124898961, 1855240508554181822, 1296101155283948108, 1889015311498300115, 1310674837540807170, 1858895558654295047, 1455718562797134417, 1752491691154848872, 1264245207893328254, 1667770456307631880, 1449394320573770992, 2074752069645284262, 1433424188278703125, 1637130912162513932,
  1465264396852659358, 2071160464464751849, 1296381530063434903, 1889300772120922834, 1293786408664289854, 1830467215655152044, 1310678411120525878, 1723220217168395382, 1260005835896021445, 1465023498288669903, 1152992509497472075, 1639390789702912678, 1301860924280542309, 1449954795619169371,
  1314950083353624576, 2018210945244809022, 1465148946901966067, 2085729595130524817, 1487784513888920121, 1296420171086731974, 1469094130855817805, 1891266354321818655, 1314653695861051907, 1449949298171010055, 2086011071248274517, 1296420151412650513, 1928748294136367826, 1465148983867217001,
  1426583712958919767, 1481909007412117504, 1733113879220847628, 1466994064137544663, 1997704449661414157, 1479227405647393941, 1152988314622125085, 1782095236110048459, 1481909007412118500, 2086931674100444400, 1434540190227006483, 1949294739597469745, 2087645357766972506, 1426575327185982599,
  1447287929353175040, 2087207888061082848, 1485822583934862423, 1648398581360801466, 1465144860754879652, 1821987541768090729, 1432295949824955382, 1929265476179840226, 1316867425084625425, 2046363529600264619, 1313267418113548883, 1936301177249557211, 1321138339579027992, 1481755960691107732,
  1426587562424046677, 1312407676767985664, 1932646337718045119, 1300319362303734268, 1887891182798093556, 1295513328981930498, 2046920422358063564, 1263680333812146619, 1499447467724814341, 1415891550221783494, 1447287911559775083, 2080733963596456966, 1469417938985387106, 1949009141469447903,
  1465020373928256658, 1731701663691512489, 1296381461344003090, 1917448269791988434, 1293786417592214087, 2018215071819213228, 1303120025147044355, 1752489578081748849, 1281133776423788986, 2022987753747629834, 1465148947791158524, 1648036004952654982, 1450793654492558440, 1932642214501016582,
  1466989932918424120, 1674815600232528540, 1298092369783734772, 1689168004801325415, 1277479823237145136, 1499448778210179078, 2088951633914569098, 1426586942757692501, 1468854576188616704, 1442350228278748178, 1446359734089126920, 1949572089526765612, 1482191859302515862, 1855240508551535868,
  1296101155283944012, 1916600271834794707, 2089234623762039307, 1426586942757692563, 1486375224945397760, 1822064793885411880, 1450230290043212790, 1949572084426466310, 1485822584035558550, 2046109122734144694, 1297765196354716223, 1933209219186547264, 1317208136824496720, 1689165726086274150,
  1312690173737239060, 1399276312661588413, 2074824470693938124, 1430044081291793429, 1634877600486794258, 1465553087095628874, 2050340606404045581, 1429473707300430885, 1740985845134821421, 1391079724673565715, 1482475981279997139, 1152988314622125074, 2088342485192239112, 1438500494733259805,
  1442913315771517081, 1467242417033892894, 2082429029197409049, 1314987406839944267, 1932642002552216749, 1320308553422815800, 1674814716308126364, 1302033981964227060, 1318939074855401932, 1466847418732860561, 1433987531715724247, 1932646337736476825, 1298061377585914364, 2020466868227344189,
  1487667013660253442, 2089951718573192351, 1296137094881342029, 1465716844383976130, 1415890895437374611, 1637125981569287019, 1487434743089456286, 1920018173944745193, 1446276691651470480, 1434540173746942996, 2084109089809205400, 1446298919490665733, 1152981649823188103, 2090579118318222596,
  1394821915525145674, 1632899454078659177, 1429693133785910534, 2079857682050712596, 1482605105636987468, 1399276310740104210, 1416975420994109440, 1772516547986548744, 1483567690824045536, 1632899454077351534, 1462379620768060571, 1648398856440374968, 1481871556865180836, 1928139576289774854,
  1310674837406220817, 2020466868227459519, 1426575327185939720, 1447287930997436416, 1275702855755967744, 1483567622037468072, 1625014098201250580, 1482604212313400215, 1485179762312778789, 1465588168228751072, 1449112843482653771, 1951265262703477708, 1485822584069137560, 2047247814647740076,
  1314653695011144195, 1470936320441551570, 1929229508982854201, 2093500866784674321, 1451646944012128825, 1648676578919449609, 1468291352252425380, 1673404584441436800, 1426586866033040654, 1449666928875479040, 1731101516516293750, 1263907246816002503, 1294170227870254898, 1446218446651077123,
  1277833190035186722, 1740386959640488018, 1276897014538105231, 1466280200832616229, 1152988317592212567, 1958836155961082884, 1383787829808534265, 1465716707330954283, 1442277796977165349, 1381120345201771528, 1437267697861843716, 2094809906958021340, 1451646944048157483, 1468684820153156636,
  1946751874682701491, 1359030608016388909, 1466433175628514107, 1426587492664554583, 1468684837467471872, 1988957973074527923, 1367320787109810926, 1453311668606043121, 1482605068484017428, 2095018267969176613, 1443474343867888729, 1436982099665951490, 2095654539053216536, 1449106111121945697,
  1885677409915634636, 1364539302242960532, 1959684704126020506, 1366899330199266101, 1446567407502058536, 1741767172197303431, 1462210363247313956, 1885677409920183562, 1485550660145468564, 1466843294231266995, 1152988317592138710, 1416049603268037817, 1450230273395180395, 1782089944358052870,
  1479098175016907748, 2095930262415289608, 1467805779304174739, 1884832710196079419, 1462379896652596368, 2071174546908112568, 1296381530063434903, 1889300772120922834, 1311058636825023038, 1689166148838311742, 1312690173502300692, 1429402244269320551, 1451428741069456403, 1949003674495869958,
  1467805779304174678, 2096505257185389371, 1484682115464463445, 1648398718900418220, 1301767842224137380, 1933209219186547394, 1317208136488288848, 1849887937788058894, 1298092370217603578, 1449263774335990220, 1152988314622571478, 1442904970868443180, 1482477729801585694, 2050335529299901718,
  1483567617607877719, 1998254067548725648, 1393966353654653875, 1455016535886253240, 1442840746930549797, 1465020371370525726, 1885681527283821833, 1483567622037275736, 2079055452662508314, 1479268394248598673, 1648113120738412209, 1296381461344003176, 1928707268860414674, 1466993849743704653,
  1888168534519818686, 1311058635685634622, 1859178811898423655, 1426575329014410525, 1443474341881733120, 2097343754825517100, 1465553087095751708, 2050340881852377869, 1465305215892481158, 1648398718900419825, 1301767842224137380, 1933209219186547401, 1317208136488288848, 1849887937788058894,
  1298092370217603578, 1479381871721937356, 1415602200889119891, 1632916975040594953, 1465554048175486107, 1391112507544968408, 1634806681046774803, 1466879373063468106, 1426575329024158479, 1450793651345133568, 1740990269806994438, 1391553203632083943, 1275708647753163152, 1419684687879316392,
  1651191298045347280, 1483203066002019222, 1625035813606241961, 1466100574106854553, 1951542614532909850, 1485179780753343580, 2066670947280750270, 1465721513071205667, 1266074462580142999, 1464974606567035812, 2073425205316460986, 2099990468232459408, 1485424767128982350, 1446298091635700827,
  1731702535833519052, 1449666928841901014, 1275708647753679876, 1484332814444090280, 2099598589822323242, 1432296087028868125, 1822067910252779710, 1482726976894161910, 2066347370903644987, 1312989652828193277, 1917448407331703508, 1293786408297062983, 1858897150610589553, 1399270371091010103,
  2063846260061766604, 1479214212299375637, 1391562050923971435, 1617137981452270882, 1466679192135459991, 1637139582292375152, 1487434743089456286, 1487667013669256484, 1429687772763518113, 1772517649775854540, 1449666928841901024, 1885118307971924996, 1449537393776022616, 1962238801154227013,
  1296415272114459746, 1933209219186534760, 1317208068105019984, 1689165726086274150, 1312690173737239060, 1486551076996024765, 1429687772763509919, 1783775134063002572, 1465308649278968806, 1928138555902200360, 1312407667832513041, 1928986529295026623, 1303419985816756793, 2026091694820264671,
  2101344026956407285, 2100084817549243527, 1415283824138478415, 1731987262523613584, 1416049565743743972, 1442350228278739980, 1394548683530462216, 1949853489778226798, 1485179780753445978, 1648398856440374968, 1430328237104465060, 1571828599789140923, 1481909004964533080, 1919459465539964105,
  1482444814756271203, 1885681531897617623, 1399276380382149930, 1394821568565542912, 1426575329175189250, 1479382534215274496, 1949290892481570480, 1433411954886714514, 2089174934059353100, 1426575368093688852, 1443474341881733120, 1731705787547020569, 1407965335521481686, 2101276268488704402,
  1468854575685108871, 1949290892481693407, 1465867064388531346, 1919459140867280068, 1466100435597104273, 1571819450334395323, 2102561259423441752, 1482601082017895153, 1946168377433129993, 1388439657347539695, 1449382294741771421, 1455952406784283795, 1378997713265437002, 1381391581671576364,
  1476670966647866430, 1447128909906410801, 1555772382394713036, 1340694674976826278, 1827095725317216435, 1481747487279866516, 1921629682315605013, 1466100436835923046, 1555213454329429292, 1417343623413916564, 1277398551021075606, 1421570829985743694, 1585609454252721924, 1348778694296032127,
  1778963572649861329, 1351803103159771761, 1462334335474676196, 1555772382394713036, 1466100435755492262, 1651195423261878955, 1402709876528190298, 1998255893278925201, 1482608298116078900, 1949576963370779596, 1462098695610397846, 2104096386663449612, 1465264394426082448, 1783216393903032329,
  1478945862989751257, 1470546155900028051, 2104377861640431287, 1451511703137149973, 1731701663691263172, 2105100516400194578, 1444529596791338118, 1443474341881734176, 1638542971530159792, 1449541516712432740, 2089174934059883332, 1433705869176628244, 2086645642566372659, 2105345915384194139,
  1469089594530952337, 1449666911124898901, 2067795903083035893, 1300319362017919484, 2093649390771366249, 1446580188357061944, 1830713264838104163, 1296090296682451450, 1674812097233378575, 1312406432137167430, 1936303310187502236, 1446566720247803193, 1314720687952581731, 1674529026961775886,
  1298110855756845578, 1887891604407048857, 1317208068071440952, 1466998829329922508, 1469089594179146780, 1298061377336479744, 1674534121849797273, 1446572255043707440, 1152988319588897891, 2095930883273420086, 1466717263717692374, 1447135236488154426, 1443474324198311059, 2081020082221579462,
  1469089634738803748, 1152988319588635733, 1555772382399458614, 1443474341881734054, 1919458187384311099, 1462099245255316639, 2078491952198019900, 1482989069534696537, 1608429638100821738, 1407965408919212905, 1572102872659097299, 1482600532798750014, 1442350365814031308, 1433411954886824968,
  2102690405865593023, 1466100575116706965, 1962519940133681827, 1426595670013087039, 1399443850746093568, 1442350228278240663, 1483323529461605384, 1949572091204700715, 1411710346362700950, 1275423414545655530, 1402410673173672842, 1644735712908162772, 2107911211538486347, 1426595670013596701,
  1485743212153004032, 1782930179346269196, 1479101954398393317, 1442904938621877548, 1481917116310373406, 1949853489778228442, 1482989072796189786, 1616873887403125964, 1394548687000753047, 1572097764181374675, 2108735430329963442, 1465158566574126154, 1442840746931074067, 1486306506653246494,
  1920018173961848544, 1466679193227863184, 1951501046245612718, 2109315141052581016, 1426587009043198619, 1415917485119684608, 1572102872659780614, 1348575968500794230, 1778965424468592924, 1426594845379882310, 1415917485119684608, 1949568136310769045, 1411710346362700950, 1658230552831305450,
  1407967741199557508, 1585607392651590587, 1340898768331039675, 1272312328190550462, 1348279512300106363, 1447125195508971699, 1555772382394713036, 1449666928942728102, 1280476779263930795, 2110093940942283394, 2102055142386914187, 1451921887706313579, 1211797591805780998, 1328996207352775290,
  1798953619373679046, 1426595670013369674, 1465020371370524672, 1482600529620417856, 2110008844108170188, 1398395255809725323, 1444605916111990070, 1433705867098977312, 1555772382398982153, 1483767936032789414, 1637134014907525903, 1482989004010042526, 1632895397079394920, 1393964705997857707,
  1426595670022997504, 1450230292833067008, 1731984082570415423, 1408452973340943378, 2110559718479413683, 1394548683530613789, 1951547062357694090, 1462377490296505436, 1465874250514163384, 1152988319588897866, 1741840123240154116, 1486306506787652566, 1783778796383102648, 1466997498769413094,
  1920021540309982021, 1298061446056273040, 1831031122312608410, 1318600255410000446, 1438118001270651914, 1152985774837109739, 1272308589574064280, 1348279511955599995, 1798670944238749859, 1335914541226914495, 1250636309167718654, 1465152764950774471, 1447296776372274323, 2104937532721350843,
  1415917485119685766, 1442350365817783701, 1429473710696338440, 1743246239765268525, 1465874210538017770, 1617154602892356366, 1404118900428153751, 1624172493268313841, 1432941773916418925, 1572096593769479108, 1391086047133176694, 1273157094318931015, 1331391014075515575, 1329077667045509404,
  1416168313313604579, 1333502487516868608, 1273157094336061649, 1416172368450600274, 1435103553000984576, 2111974407139133483, 1345610515557454818, 1211798123021301941, 2113061797393883770, 1152985776766890903, 1949853813544941169, 1479226539734654292, 1467444041030868992, 1482601012737170197,
  1782089946517996492, 1450230292833068004, 1462497168513136652, 2113032665858339693, 2114281847240606615, 2111062341642171410, 1399443850746094613, 2112818692214121879, 1462497127004058507, 1638828569692587698, 1465311469694223520, 2013190580574177834, 1466679192135459991, 1152988319598349608,
  1782089946522321932, 1429752986331345892, 1758165582282345813, 1433623788143100976, 1962242590468211660, 1450230292025492578, 1732830892382086150, 1449263683023848407, 2073420944021941364, 1485743143030559888, 2071129218074953440, 1312989652879942807, 1917728505200970452, 1293786408297751111,
  2093928942474865068, 2115168392307327491, 1782018093866894410, 1429471236493513700, 1949009339709209944, 1485743144382964822, 2101010894439450302, 2114440041362181467, 1466679054797190291, 1782082285558218028, 1408453659411715044, 1616867777559577011, 2115689222117036951, 1447016332187714635,
  2114500230613876040, 1466679054797190291, 1616856474229062956, 2115970697093747607, 1462497524626277524, 1637139857371973344, 1447016351987868830, 1950980215073750360, 1465553086137291868, 1885390329759269900, 1482152894183683156, 1731987947688901806, 2116282754336924644, 1444600516226057164,
  1410850798099940384, 1949290539791236440, 1468934015706805338, 1265855355880033627, 1462497539623310184, 1637139582292616880, 1487434743089456286, 1651191270565563741, 1394251128776893334, 1902851891436103096, 1446722988361266260, 1772797882437590214, 1394205746627605464, 1394498863275807567,
  1450099723092279296, 1408283577901515783, 1435103536017908697, 1808801207213262891, 1348699800938177196, 1272310466389336518, 1408283578896932193, 1779766295277777881, 1331391014015820471, 1345685828720255430, 1438127963118203787, 2053967336947319703, 1469090253839950430, 1447134480413586591,
  1757878082301068122, 1434540190562718708, 1772792517502936818, 1481898011629564888, 1902851425449630371, 1415649072058647706, 1266139551969752745, 1402410671640642382, 1585611514830044511, 1345685836806574975, 2116764381377881495, 1443442220995736547, 1466842879790822485, 1293785041230434304,
  1932642212787537707, 1297765197513237048, 1730257901137214452, 1260591325602009531, 1298116791663912753, 1432213075993887752, 1445936974073504914, 1296372535423697894, 1909565321145355327, 1264314410402546245, 1667769714150761679, 1265075064311980473, 1432213076003153956, 1446294797530244125,
  1468933996976387165, 2073425057207379976, 1298116766107845641, 1892114278847310183, 1281203048143594041, 1883667562020031187, 1320008589578662394, 1689439164171802407, 1287617046517940724, 1430242543095150508, 1479227369805390877, 1152998141222835218, 1741561232525503291, 1411437182713799656,
  1902851425449631078, 1415649072058647706, 1266155241183295145, 1415931709724787534, 1555211632340548844, 2119049261514576788, 1479227369805390809, 1466825083694699538, 1449268700589043712, 1741554573010843323, 1411437182713799656, 1442627689088161948, 1481909007781229576, 1885395649595501859,
  1486938588370601108, 1565081666349348521, 1399447351674168152, 1303009196915639701, 1328722017961513866, 1211793861893404848, 2119254454046552758, 1391391779747050156, 1328722006459372575, 1289762017471129883, 1340414499627012703, 1447127123211231659, 2119225117357962103, 1331391013881328300,
  1278502331207774632, 2119821321688957594, 1447142519568725076, 1651197801595405146, 1484682115531580310, 1632900482371037868, 1483861257603609515, 1572096593366409618, 1399434226254111606, 1303009196915639701, 1433065373994230666, 1446294797530244125, 1426750340023563357, 2118461053481659195,
  1314804995702547424, 1429692718552269974, 1312401768812019712, 1675097695446075959, 1296378780911845898, 1858902024794737364, 2120763394565808661, 1433056674341409283, 1280795744349298688, 1752493540977129475, 2122178806787641726, 1485977340172923455, 1892424592849372119, 1302856622421123641,
  1916880025955707621, 1310674838260969995, 1883661862883924978, 1320008589578662394, 1689439164171802407, 1287617046517940724, 1443484033367885740, 1433905068343391391, 1831034294969967621, 1312989652879409666, 2014269324187171485, 1277755870558351755, 1671143223308556069, 1464835281587945870,
  1884756460551402504, 1433905088066700432, 1831029535961654277, 1300319430619922946, 1919135327963080511, 1320008591900226105, 1499444396471306098, 1277177664699904454, 1739542737312016466, 1433028628775480694, 1849610585960874967, 1295794941833716278, 1465721518516828708, 1394503811816563847,
  1731982384443688027, 1468934013455467492, 1782367298800176483, 1432778361133917216, 1884832711604855825, 1314724899563455632, 1916880520782818669, 1317208136388256253, 1499444396471306046, 1277177664699904454, 1739542737312016466, 1433060044551048568, 1445936971859489942, 1297835841121899494,
  1932642213844528502, 1293786408664289848, 1730257901137214452, 1260591325602009531, 1315006664656086833, 1433060044551049777, 1892074812159653029, 1296101153372594745, 1668338585773319375, 1318600252441239933, 1685222882153301768, 1487663645114047866, 1466842879791592598, 1465032740305965056,
  1831034295068855652, 1312989652879405570, 2014269324187171485, 1277755870558351755, 1671143223308556069, 1465112702216192398, 1466842879790822408, 1296372535687974912, 1669749257514748626, 1280795744348881396, 1752493540977129475, 2124716342286422398, 1446294797530248357, 1152998141222835221,
  1741566473827831134, 1429471235699413992, 1979976196787103466, 1416213875957376105, 1555771044147140236, 1450099720580711274, 1782367876993097055, 1482202851911459872, 2124330189659130408, 1314653695963984387, 2014839235007453762, 1301728661332636103, 1859169317302544932, 1260867302013956689,
  1754745271585032050, 1465721556812833236, 1394503811816563847, 1741552533651850331, 1429471235699413992, 2124653583834638058, 1470546311763592357, 2032595225099794032, 1399028986190324833, 2062729747094626740, 1487241706747589663, 1921983746265719815, 1310783079266182228, 1892114278847102331,
  1296101153372594745, 1668338585840428239, 1318600252441239933, 1685222882153301768, 1433065745969143166, 1310783061935641559, 1831033659111521659, 1322298119326802494, 1937991819906022390, 1263907247606612506, 1729971419705842125, 1276894197814075775, 1313036750123034766, 1433060043527967295,
  1481862948048434326, 1889013524676371473, 1312407667967009282, 2013713258629806442, 1264314410402488881, 1667769714150761679, 1265075064311980473, 1464877495921149988, 1429692103113192456, 1433905087945801728, 1854960618552135039, 1296381530060091898, 2013711610168052460, 1298288701225476657,
  2014270295537580423, 1277755870558351755, 1671143223308556069, 1479227407960523150, 1466825083694699538, 1434540190064828416, 1651199730408900617, 1462099246396724118, 1625863745845163639, 1393962369250018457, 2062706773331453335, 1432778497777333279, 1446007960001185980, 1481862966664487910,
  1633762311968238184, 1485552859988726879, 1648676575316936371, 1295513328983475364, 1928138543853480297, 1318600255513285137, 1859178826427505349, 1264314410402783825, 1667769714150761679, 1265075064311980473, 1447134480423200804, 2116128893620823133, 1465877783749243852, 1617998890282855180,
  1487434743022298187, 1467400882941869137, 1426750340023563098, 1731983048724539114, 1479388651350832100, 1648112983198705328, 1416778747321189480, 1555771044147854389, 1483567617579631466, 2116482903164185404, 1450312753444058073, 2122397592250782734, 1429960422276777105, 1394498860859437903,
  1421570833331650560, 1743528883492980460, 1340591527348823078, 1302995434431101901, 1411139622004396926, 2006977494353572263, 1449388547128704389, 1648036007351760006, 1296372537771127912, 1928706649445599954, 1301711755800732237, 1478950014668008446, 1152998141222835221, 1624749048285718250,
  1416213871724282793, 1648094836507977111, 1449184517890258024, 2126898768644278460, 1443474821965992918, 1831030172103822532, 1296101155283411518, 1669464485747776091, 2127879984027267632, 1394205703404401625, 1571535799634101179, 1404947246475973524, 1479107580851174638, 1152998141222835221,
  1651197801599675779, 1416213875957367702, 1555771044147140236, 1450099720580711274, 1772797150111867911, 1429567718852117532, 1949001286645529990, 2128459159220302934, 1446567543891726911, 1455389044514337885, 1932646335538907290, 1302011304288301564, 2015682757138777899, 1465711209562414474,
  1152998145567831000, 1822349318439422106, 1485179849848050738, 1891265730748611977, 1316643262289486333, 1855235962245012164, 1487630700625519120, 1446567544126772309, 1772803247937946715, 1312989652879406108, 1855241680524204741, 2129287701029184016, 1446567544914744405, 1449184500398797917,
  1962242381864856332, 1470944953048015970, 1831030172204812001, 1296101155283411518, 1669464485680667227, 2129568833887531568, 1482047067475505727, 1455389044514042840, 1932646335555684506, 1302011029511315964, 2015682757138777917, 1482047067475508622, 1455389044514042840, 1831034295406413978,
  1312989652879409666, 1674816633457375901, 2130132126431703540, 1464877093896151614, 1830713266029147281, 1300319430619922938, 1675096100402436802, 1318600255513211462, 1934614120185961122, 1294151927727968790, 1391390953815213938, 1394503811816326290, 1822345325289931867, 1449184518120129586,
  2062720293067582856, 1432778497727153183, 2073415614319187981, 1462490190258422928, 2129721342063929016, 1297835841122006167, 1932642213844528502, 1318899735279030840, 2017086008853481278, 1399270332430413201, 2003538902064911320, 1322946695853167258, 1272028337889845457, 1349984785427022431,
  1791070910790001140, 2130926594357035693, 1391390957227864699, 1778963572630488085, 1345610516803617393, 1447135784348498139, 1331896846283764587, 1273721379822985425, 1333096217786294939, 1391403876499409119, 2130484116259177323, 1391390997771531294, 1394503811816326290, 2126623084319343707,
  1394384169079841810, 1902851891436103096, 1432778361143870548, 1743528883493109118, 1310855344466510886, 1152993196691812927, 1659885116301285353, 2132298850286498232, 1449387171632116273, 1277479823238324224, 1660170714463623146, 2133424199430893948, 1446567535265911167, 1449184518422700032,
  1659886492804749289, 2133713372331692472, 1446567544126526014, 1772803247937946715, 1297765196354716700, 1933209219186547263, 1317208068105019984, 1854675025657808702, 1310678411120529974, 1723220217168395675, 1260005836232081861, 1277854439014262093, 1152993195532055029, 1723262137259993418,
  1260005836232081861, 1465316842290144589, 1466842880797410403, 1449184518422700032, 1932646335536950684, 1303419985094062588, 1830467345997380159, 1318920900488376886, 1689453602963171774, 1260591325642346996, 1659886492804749289, 2134557591103394232, 1446579567702917994, 1651132232094819349,
  1417343694220460950, 1822349307197883832, 1421570833277101106, 1616856474229228949, 1485743144298812491, 2129993705452095200, 1432778496259658302, 1758166491573297685, 1300088258404209622, 1917728095467461274, 1293786408765116999, 1482486972401387967, 1466825083694699480, 1446456150451585024,
  2134220424911349482, 1415649071823234133, 2131668142055140767, 1479218642230267297, 1152998141222540307, 1651204543221991612, 1484682115531580310, 1609252561183874244, 1433341721829872549, 1732818805068194194, 1399279650321482711, 1741767173421761359, 2135789535030879268, 1467408715979764745,
  1449184516715700224, 2078487687765515566, 1462378178632827991, 2092285170161403570, 2135975969952175141, 1465158980851421753, 1152998144326358067, 1855241129258441413, 2136324575684104720, 1455583334423400957, 1152998145567831069, 1928139162915977791, 1310673601444614673, 1416340765107603903,
  1449388548171322527, 1466829275582772359, 1483767939103916032, 1949577356969117374, 1481871556865180758, 1917728095467462053, 2136803962540147271, 1466825083694699480, 1446456150451585024, 1822341329061504746, 1465035560700216370, 2135631903603441054, 1429848780466836489, 2135329258161733030,
  1462377693560128335, 1951265242709857933, 1464876170535310422, 1152989072550654984, 1462221398830837112, 1466842880830968979, 1485179778630017024, 2040493774446651064, 1443914490235245545, 1782930964452615173, 1465314627335267361, 1462502943399414312, 1411673785396392921, 2076786658530821211,
  1399028987550286771, 1999937853525026257, 2137873315610223587, 1466825083694699490, 1430133072582795264, 2137600608414820074, 1465553087096329291, 2126624566792570592, 1449666997158695954, 2028389069658344811, 2138235329781195745, 1485982768239096917, 1152998145567839193, 2028389060933635422,
  1443909885896537057, 1800663035216307251, 1464866756047873063, 1152993332990440419, 2137026898143283752, 2138791064353362903, 1487675602654933561, 1317208126851724447, 1675091977250855621, 1301711755903943178, 1934894431947709082, 1312401759216206418, 1698738429793344508, 1464876473138757039,
  1884756461558035621, 1313321431607080080, 1928139576289774290, 1318600255410000401, 1416162948071230457, 1273111335755682787, 1323526000881652379, 1408460179680864597, 1152989209988690855, 1272310466389704112, 1340414498477634143, 1447303795236989270, 1656761731629032541, 1411437182713799614,
  2137588651746946440, 1482769034182886475, 2137879599609375500, 1482989004010472418, 1609273988994411112, 1483861669786063781, 1614036364896297362, 1410850798100312998, 2139553566769542657, 1430242747749866931, 1265572939445568443, 1411139626061034318, 1434477102917961109, 1152989762865935368,
  1440081759679860062, 1366914723672072985, 1432494895651314480, 2116128894729401352, 1364645882487325644, 1988952573879450370, 2141095705362678570, 1466825083694494631, 1447303802076389376, 1772516410447063369, 1422697556676805600, 1616855380405233394, 1478987190613251147, 1648398718900750002,
  1465553224594822308, 1565059821945293862, 1464978867275600810, 1732274224338140243, 1443756574726403104, 1606160385822334033, 1467397488391181460, 1426750340023563098, 1772234660022148530, 1411437182713799640, 1555771044147133878, 1415283822355313514, 1634882215562871220, 1483203066263397510,
  1951260723397629581, 2141675360010658902, 1467400814061769802, 1782084930298184795, 1429471374157603812, 1648398581360363673, 1465853940930524324, 2092272342989875980, 1465156889879958565, 1468854557260989399, 1465318789741971167, 1466829275582776290, 1433424185762635776, 1732269660583265285,
  1438500494875063254, 1616867779137112217, 1399028987550286759, 2141814758569206196, 1465553224594846854, 2042459658639707174, 1468291352263103645, 1648676575216557314, 1432495925393649083, 1468291211307900928, 1467570723605612255, 1426750340023563098, 1772519799024871146, 1433987548430709728,
  1442627690430425417, 1429471374157603848, 1885399701982109114, 1486938588370601108, 1952668239511763951, 1462379896320537694, 2091440745231279800, 1302011029511315964, 1849612097825212221, 1320617241244070454, 1935180030294596258, 1295513328326406678, 1699024027938413598, 1482604170535062973,
  1635436467431932762, 1434894648742904988, 1442630298851493933, 1421570835053478882, 1772515585225746154, 1464974606574769120, 2049201904021768747, 1416213945956492375, 2127729433790219670, 1482604170534854078, 2142935850441245530, 1487434743022298132, 2092276379654462545, 1446362139445974025,
  1651197801600149168, 1464974606574769046, 2049201904021768747, 1416213945956492375, 2127729433790219670, 1429569780369171417, 1433623883924895723, 1152987145921704931, 2127729433790219670, 1429569780436419545, 1447123001334827020, 1782299566746448869, 2144136476216665120, 1435309296340874201,
  1345610515557031936, 1280758941469112566, 2144305451558048350, 1433057636584084331, 1430134774251713555, 1465144813578632641, 1466847418732545169, 1298061385481080832, 1674534121849797274, 1482033500203225648, 1487666943648420893, 1444248124213810335, 1465036382371075044, 2144625364616485054,
  1317208136388256253, 1831029114348501570, 1280795744348881410, 1752493563257272323, 2145259961036345726, 2116128893620823114, 1484131053128631244, 1651197801600199443, 1485179781743575958, 1648398856440374968, 1434894644531483812, 1742120271641633204, 1432778361143333924, 2143222274818196491,
  1416060974351889377, 1964771663543891569, 1430416543709811813, 2138723072767895882, 1298061377334485561, 1831031122312608410, 1318600255410000446, 1487662823023340537, 1152998144142038161, 2144626171986232377, 1317208136388256253, 1831029114348501570, 1280795744348881410, 1752493540977129475,
  2145829714419528062, 1443479906968547897, 1442628268132926555, 1314950083353625570, 2014270295570859838, 1277755870558351755, 1676209772889347877, 1482047519038161300, 1466825082268386389, 1432778361323225088, 1616867779354912490, 1467570685942002599, 1648113619290393365, 1391079312323040390,
  1637421293827354018, 1296101155287102562, 1831030709307849279, 2146483720296845886, 1429969110535909944, 1455389044514337800, 1932675514523306138, 1304546709634626044, 1929265476179868223, 1314653695963984401, 2015682757138777917, 1322298126253458451, 1499452016548412406, 1260289306054676874,
  1659610854403340290, 2146663145476252088, 1429969110301054051, 1892113885318611976, 1446739340479459903, 1429692573976148102, 1466837040749941919, 1432778360647553024, 1674815669186886301, 1264314410639725044, 2041568483222512847, 1266765151122825657, 1429969111216867404, 2116128893620823048,
  1433341723593507788, 2145183911691297797, 1399028987516617802, 1653464874904575420, 1465553224598852538, 2146605717514771912, 1485743212733363299, 2135327317323060877, 1434540191256409046, 2146890765132241973, 1302856622421123641, 1916880025938930405, 1314653695963984395, 2014839235007416125,
  1263907247606612423, 1729971419705842125, 1276894197814075775, 1260687764574038158, 1152990171858436597, 1752500222872898283, 1287617046955508154, 1502543763973388325, 1267328513358373238, 1545608061473469707, 1443471241349389774, 1303419985194799104, 1442627855149089849, 1264245001758233570,
  1499447045811427404, 1277755870326043078, 1769098439567456141, 1260298579505103266, 1313042246607402307, 1467118515726648279, 1932675514518996059, 1298061377468166652, 2147693557700585831, 1315177269554225653, 1883665425844509682, 1320440287106477520, 1669146628591546942, 1280795744995693104,
  1697887536658745111, 1270728478693913051, 1532094513392608588, 1322122384697115095, 1443471241450435159, 1432778360546725888, 1729972341664057130, 1284235361102668159, 1707458785949116558, 1260008583312810425, 1715056947731457865, 1429969150953337253, 1772166472080401416, 1432778360647554068,
  1616867779354912490, 1467570685942002599, 1608987426578570700, 1429569776905692069, 1831034281261239759, 1320308552029696514, 2148539775830026982, 1280795744348881396, 1752493540977129475, 2149207414140055934, 1443476335650640855, 1951532866277999708, 1315515379583452312, 1939960562198791981,
  1486938576992256600, 1442627717609473081, 1446641555798569954, 1741566477687455144, 1314667930024395752, 1635689692601637863, 1299415427111674976, 1929029683685792821, 1312687562008814157, 1499444396471363943, 1277177664699904454, 1750802148999293010, 1394497969635696084, 2142654375464535131,
  1465320402928612445, 2012909105597467178, 1481862967919797217, 1772802008609401162, 1484131051898504220, 1670025427368024676, 1319745189759533572, 1731701667346590426, 1469417938986079250, 1892436992575503172, 1302034531285893695, 1689168004818102717, 1277479823238345264, 1660172090967087082,
  2149756895241752956, 1464830765960360979, 2142587541431624664, 1481862967786034269, 1920260804815379036, 1449184518422701216, 2135068147705792664, 1465838409567949959, 1830467208108141326, 1318920900725609014, 1689453602963171774, 1260591325642346996, 1659886492804749289, 2150038714822480312,
  1152998141222487000, 2142655847149129054, 1482442066816488541, 1921991448954494418, 1296101155287155874, 2149661139932367571, 1434540190227006483, 2147734869080931752, 1465556385797140981, 1635691115508181649, 1487434810891916384, 1854678193213086402, 2150357711174664758, 1482042943230673879,
  1951466032246146056, 1298626320152732824, 1442595860895696683, 1483865109640066018, 1689489136318111182, 1464983127988654672, 1849607506505022105, 1295801744606270006, 1450684140371680242, 1443471388689634453, 1444325375134925971, 1487245281162163172, 1921980862413277337, 1486656906114872404,
  1466825082278878018, 1462223280599375872, 1555490806137779824, 1484131053128631128, 1442624843857603347, 1391568801951998946, 1608975295627018642, 1481863036215546969, 1638542971530463787, 1450684115781047396, 2150268143870502922, 1465319646007714360, 1465039504477420438, 1426750340023792649,
  2072863275636836906, 2151746127655793693, 1394205706726249295, 2127734937166545754, 2151947064446682083, 1394205706525692896, 2151031786422481995, 1446932647269803092, 2151662398552000667, 1466314494876132175, 1638546147423843925, 1486656906113995876, 1394507658238487362, 2142654375464535131,
  1443647310758229085, 1651207726514392538, 1479262415565964182, 1648112983198992937, 1465553224598852712, 1742117471491611764, 1466825081447079391, 1467570687594323968, 2151102750002850579, 1462223280599376980, 1555490806137779824, 1421570835360076632, 1772801782116650461, 1391076975801394136,
  1443194076978363783, 1433987549206754334, 1885114431059815865, 1485743212152706192, 2081303522917899522, 1298061377484997116, 1831033237198150342, 2152932425185620542, 1152998141222286481, 2152514660035290858, 1415649002097128597, 1950979882229227922, 1465039475395368082, 1555490806137779824,
  1421570835360076632, 2078487554134997577, 1432296087028868125, 1443194076978363783, 1433987549206754334, 2090314432353025269, 1296137448542049445, 1929264924914113116, 1314653695860978193, 1432670368491162047, 2116128893620822999, 1411437186328167372, 1885681536511290821, 1391076975793488984,
  2150830746401889724, 1416213876132652040, 1441210728625644951, 1430044220630131741, 1617990037516413710, 1394494645510837383, 2142654375464535131, 1443647310758229085, 2145183911691767258, 1399028987516617802, 1885681536510297494, 1391076975793488984, 1773082658364857825, 1465866169911985180,
  1949569533316565180, 1479264543921206422, 1636853984130050057, 1313261233345512546, 1672841634487716562, 1470546165790380592, 1391575149481892550, 1394485941900239893, 2154090355016474624, 1426750340023563098, 1616867779354912490, 1399028986190324647, 1732264617553464793, 1446934985054417952,
  1608975020178341347, 2154306893258810457, 1462057394984080393, 1485743140900298752, 1919455017682156809, 1432639892720096401, 1482491768221064361, 1152998145433613272, 2134220424912161555, 1399288336664587751, 1616006862266696795, 1483767733935604811, 1638828982680251150, 1446359737421235360,
  2154200874514253834, 1430328167570125833, 2154483316361906330, 1481871556865180818, 1891265324488301998, 1302011029511315971, 1855240085497440617, 1429691936960123468, 2116128893620892757, 1462375561960506316, 1949576461703210672, 1486306506787652694, 2040493223919085240, 1451428828671132649,
  2145473319389432485, 1466826251791334889, 1394671417405333504, 1616308922153743981, 1485743143213130903, 1962238801154227688, 1466100437691806818, 1773079168922577579, 1432778361143129116, 1466826251801898366, 1394671417405333504, 1616308922153743981, 1487434741852464279, 2155335014417032888,
  1447307445679604695, 2028376888828796389, 1482444814705898640, 2048655547321719889, 1429401803394561113, 1451992103339471704, 1555495754896918572, 1432778498950017958, 1429574967208283082, 1426750340022711128, 1732261214663943632, 1430044082085741600, 1445160956848916667, 1429683209678902281,
  1485988129129788339, 1772515585221985163, 1446452780776854496, 1916913017813978374, 1449666988726821387, 1849612097825212221, 1320617241244070454, 1935180030244264610, 1295513328326406678, 1699024027938413598, 1152998141020519919, 1266140012588354910, 1394671416285660068, 1637138070430332525,
  1483767734439117982, 2074269411354959338, 1419299102832288601, 1998262662634237421, 1443643940543689759, 1782371882368867268, 1433623473952171040, 1486151627663556015, 1398998204090823640, 1782366405274895269, 1484682113516676128, 2137038331161692714, 1433623475584345096, 1731992407744277260,
  1462379896319661074, 1613777709752219221, 1465711250843952278, 2085448121042719819, 1434757593356457095, 1635154992455222359, 2158283413737305184, 1464866717003567678, 1830793556495696855, 1302011029259256314, 1928988464311921085, 1294183331573658169, 1487840750436964866, 1450516919647560851,
  2158068662937142243, 1313036736914784830, 1433234700503472919, 1152998141020439636, 1902852389702782302, 1429574931873072282, 1555772385670145488, 1430381355368784806, 2157296826796066970, 1465556384399197343, 1732828418598280689, 1479114872955515923, 1952668839196587639, 1485552860310488210,
  2032607801419138785, 1466824254682385910, 1399457247479529472, 1265575548591695255, 1482989004996641674, 1442627691471284840, 1482772399286940680, 1952668239511247803, 1438500493839668318, 1609272077985066322, 1483485639493731223, 2071174546908112568, 1465153619543236087, 1487434739539632128,
  2154209114510190264, 1482745391630963749, 1885118297788525371, 1449537391579784280, 1465153619553650843, 1485743124583396311, 2159276214618556094, 1482208073937343497, 1950980349995900286, 1468494114905674898, 1152998143319954440, 1909594566432834617, 1293785996212838981, 1499444396471363945,
  1277177664699904454, 1750802148999293010, 1465148189077822970, 1426750340023563223, 1950979881189647365, 1468291352252191890, 2147970503248420345, 1298061377220174992, 2123768184680154922, 1429687633929539067, 1932675514518996059, 1294183331506500092, 1689451323895855679, 1314653695963984464,
  1883665427018914802, 1466824254682074620, 1407965339901190144, 2157007780127272429, 1432778359474582379, 2000793146954236939, 1446641485164037081, 1648680706085128235, 1314950083105502312, 1934894352138493196, 1321998640334398034, 1499444396471307729, 1277177664699904454, 1750802148999293010,
  1465148259641953789, 1772796256066733147, 1433623473649599516, 2078491689516869641, 2161343767675855961, 1152998141020439639, 2158984049937141086, 1429574931873072212, 1555772385670145488, 1433196106021327782, 1772519790586487815, 1481898012473369568, 2090314432353025269, 1296137448542049445,
  1916880990276434495, 1318600255647158795, 1462227302579636029, 1426750340023227539, 2092285170161403570, 2161871667809555493, 2116128893620773720, 1415917485120484300, 2156444830173536656, 1443649714902754262, 1949576137936305662, 1482146504380621974, 1633756278931450471, 1468854576054211719,
  1998262661745641183, 1430381356411548703, 1822341604510386330, 1446359803034137650, 1932646335536950684, 1302011304355549692, 2015682757138777911, 2116128893620776449, 1415283822540243916, 2157008313877430708, 1415917485799592811, 1653164067926674944, 1478987193826870166, 2074269876436461240,
  1483203066313888852, 1885677607522233102, 1443930844184937560, 1732268646870162544, 1449254061219034144, 1822336725461059737, 2162530896586892338, 1152980554085921945, 1275986364499400333, 1462057254357143043, 1426750340023563411, 2162370376971431396, 1399456906739799193, 1648398581360125335,
  1446362139572114596, 1822341329062586040, 1462049327686509618, 2116128892229350547, 1487434743022298060, 2048655547321719889, 1482604216544572505, 2116128893621535831, 1435033324433245132, 2162077620542260235, 1485743144382964558, 1964777005711492798, 1481871554785907813, 1772516226988320811,
  1399454156884390932, 1822332111172771268, 2163938888922444850, 1391395080127427615, 1402825807532634112, 1408291755335386577, 1152990033616131048, 1782371193312135213, 1429752986682041376, 1447131594205730866, 2153846540500763723, 1415917485112632154, 2162077620542260235, 1407967741206676302,
  2000791814692535815, 1487152438478443443, 1479116551293925075, 1466837040783504405, 1468854573971058688, 1965054357502576317, 1430135480043332769, 2160387963312281791, 1479212017118900792, 1487152423611249739, 1465324414874056403, 1152998144141595607, 2160388770682029113, 1314950093524148792,
  2093083289052415713, 1321435277996958205, 2014269352423295724, 1277755870558351755, 1676209772889347877, 1482600574544560532, 2116128893621535831, 1462227677646570444, 1950122846654477938, 1391295710908929175, 2164321420157939210, 1450124391879488488, 2000789168069246475, 1455153216991511513,
  1921987411214952550, 1485552860310488226, 2032607801419138785, 1466837040783506958, 1394671417764630528, 1555772353508847109, 1430044082085876646, 2142375769177720985, 1402836870195659910, 2000789168069321139, 1430254018231582223, 1623829155059479645, 1407967741375198061, 1447028820945872337,
  2116128893621535831, 1468934016632677324, 1442628130597882643, 1394671415292072930, 1822055730899683480, 1481898009672029174, 2166014153792712123, 1465264396751832139, 2001087156575619626, 2166625404956480663, 1466837040783553497, 1482775972542480384, 1442635994146155323, 2167034907490702306,
  1465720625371645013, 1449184500398797795, 2120146263088704315, 1479226517062542354, 2166231439476032599, 1432778363459658772, 1637117485523463681, 1430421835441112222, 1921991448954494482, 1411813147464598690, 1613756229581088776, 1465719910085223574, 1482775955016889352, 1950979939625216827,
  1394671417764631644, 1633740922057698835, 1464978863164060827, 2134210882618367503, 1293975918976984083, 1152992440609502237, 1499444396473328645, 1277177664699904454, 1722935300698138706, 1416162952925003287, 1419685290619237347, 1289203160538637777, 1328722154531656387, 1466837040793487535,
  1432778360513146880, 2165727491786075649, 1447028789144007827, 2157862654176689684, 1399890041553495017, 2163760413122651543, 1419685307139261471, 1278505240629831121, 1335068879262220894, 1780376270927519953, 1443475371516321305, 1962519945497543771, 1432778360513148062, 1732273206598965439,
  1314950083105502166, 1934894012131453289, 1321998640334398034, 2120704896647777745, 1432493768300934113, 1465888143609017352, 1442639979792165692, 1464974469068440546, 1831034281261239803, 1294176734050251266, 1939966680547797722, 1416162996993725016, 2000724148673721305, 1402410668478526387,
  1288354612388422078, 1345610585421451911, 1443475371526834357, 1951260946429117531, 1435033324349342872, 2153904718617650181, 1415917485120295770, 2169114377184173593, 1408467472239076311, 1277112174899528081, 1462098696230970222, 1902565879498274469, 2170697106914981008, 1391402639739675231,
  1404118901099319296, 1251764516982149641, 2170897828318368456, 1152979727540229014, 2170515285524072171, 1355340781822141023, 1251762142486237708, 1443475415679361676, 1951260946429117531, 1391295710942508184, 1772234202657697252, 1399454019512681492, 1758156912538253324, 1462375769125815344,
  1443652337238834690, 1949572096568853595, 1446748483505865878, 2165174275420284936, 2171769405583082581, 1152979727002997654, 1658230827910678251, 1340414498179412868, 1825695704726434356, 2172023452802085488, 1152998143319176336, 1885114103835766244, 1415917485120463960, 2159556820786787952,
  1411673416304485463, 1443652307643642857, 2038239943414099428, 1399456906605151395, 1616856474229976567, 1466833671682620966, 1481933059239583744, 1949576137936305701, 2172886096057050262, 1429692169601500245, 1894116097485964379, 1465855933612266641, 2161526795399378548, 1429680214626901544,
  2171361184312198235, 1438304366009259016, 2170808723763701861, 1481862966665180181, 1921992137223260714, 1465553087096530082, 1633760401881951001, 1485743141284500555, 2071165326267664096, 1443765917447441961, 1450312753084751872, 1772801043533288463, 1482753297191437340, 1637134047136541452,
  2173788246682502302, 1152998143319512215, 2173057799410208094, 1450312754421933017, 1731984062454901066, 1482491749860545554, 1635167813356531199, 1470546174727124064, 1932646335536950684, 1302011304355549692, 2015682757138777911, 1466833671683399211, 1465553224602918912, 2171361184316943858,
  1394671415292072968, 2159262226395348458, 1438304367476831306, 1758445821264059732, 1447311360099300400, 1443202522612121115, 1485743212152706078, 2081303522917899522, 1302011304254632444, 1855241056898038426, 2174324316784808524, 1485988124197729241, 1429674510809346995, 2084673351065797455,
  1449666997834380259, 1822055730899934752, 1300319430622864374, 1675096100402436802, 1318600255513211462, 2019622104951241830, 1303983347397931583, 1874094875442391400, 1399283844535370325, 1464858123260523685, 1152979726499406998, 1772797152880822824, 2174916412422005788, 2116128893621335017,
  1391295711557067724, 2173612984129400292, 1479114874804036759, 1902851425449631275, 1482772401508500634, 1952652896947836498, 1419299171077788766, 1648398718900418220, 1446749302967129252, 1445162110601283593, 2175110818333602849, 1446576066348602328, 1822341329057743881, 2175479364075033650,
  2174675688777151572, 1446362140557628393, 2153904718617808418, 1482989004996641626, 2151113319162423912, 1467805779237061779, 2038235857727024244, 1402709945247671191, 1265874638538925752, 1430142417987507082, 1758434369925504547, 1447311360573142064, 1466833673321127406, 1434927426598797312,
  2092274481094608941, 2175999500720506003, 2175238638730572951, 1415917485120463956, 2174738850919001649, 1391295711718585321, 2170814694036688423, 1470546174727124017, 1772797152729188455, 1314727577924183068, 1916598072392260162, 1310674837641650699, 1429861253435935167, 2162080275314508891,
  1434927422404182862, 2175311497784272939, 1415917485120463956, 2175864750825844273, 1479088623963923607, 2171639769551703549, 1454810510437069813, 1443194078119214619, 1469245865565893662, 1648680701925123769, 1298061377336648808, 1831031122379717274, 1318600255410000446, 1152998145444236295,
  2176141241777704286, 1443652325633057751, 1782086608309323786, 1451428756481770516, 1616856474229063146, 1465885895521506379, 2116128893632207680, 1391295708637578188, 1732264618912419362, 1454810444308071456, 2170806801027453967, 1486938587216954262, 1949012437387263450, 1153001967443199062,
  1483623244908314165, 2177966458370478080, 2176927488473395775, 1481862967755764882, 1442640189859077594, 1296101155283416034, 1891547347089841614, 1315177269554225667, 1838635899586570599, 1464863391161139707, 1483623217085243392, 1442628268137160154, 1315019843436708834, 1934894012148230505,
  1321998640334398034, 1499444396471307729, 1277177664699904454, 1750802148999293010, 2116128893502221883, 1483623217085244364, 1885400941147589286, 1446932648533357716, 1743528883493109306, 1469417938984170534, 2151113046700161861, 1430332290839557129, 1773082518493538634, 1295513338928858140,
  1932642212334545257, 1320308553422815800, 2017084073954278045, 1303120093866873361, 1752489582997473137, 1286771934612070842, 1695633732336600842, 1426750340023537212, 1884837181777325622, 1486375225999402128, 2012898605174237868, 1446932648676242401, 1731701669076519067, 1451992121128174610,
  1638533566676106191, 1465838477451240548, 1892395774529628988, 1302856622421123641, 1916880025955691225, 1310674838260969995, 1859177035073903609, 1277854415062508113, 1766282519589152850, 1286433903286981023, 1260753856281958285, 1426750340021322229, 1740432523827218620, 1433411953857954835,
  1302072335917944270, 1465046192577565841, 1648676569076095682, 1447142519819648575, 1483623197445501983, 1617136855381554798, 1393962369182679975, 1416351350709870994, 1152997045016024199, 1651192537646988627, 1402836870670005082, 1479401784970263483, 2177208962561168459, 1393962369224541334,
  2179519802320004503, 1391552926638318681, 1266138587716995627, 1293966794784058946, 1482497228819468856, 1498881622161051196, 1434540190227005834, 1739583766348729806, 1449666998276453351, 1638545546530605249, 1486656906115097700, 1451637461559294786, 1638542041749128337, 1486656906113533028,
  1479231900133641026, 1483623197445034979, 1653447127377229422, 1416778816040670138, 2127727492951541142, 1433064648587509317, 2113940285523231705, 1407967740881183597, 1572102872810094091, 1430242749025656390, 2116209337734005905, 1451428760776831948, 1445449519511767050, 1479120439971918821,
  1555771044147134021, 1484468530142700394, 1951524278578538218, 2181827734032565340, 1433060041598464875, 1483623197445034999, 1455573957318364732, 1391572785576731626, 1266137559424671300, 2182212909628736420, 1438686998326969479, 2177008207598191577, 1433341723794252946, 2181780751136151743,
  1415917485799592811, 1651207797380576881, 1465886784221025114, 1275423414546959124, 1394109083830825866, 1433240439350862358, 1481992078572229623, 1429752300244811776, 1444319154030118922, 1432295950613476324, 2142383317382102600, 2182755038838559831, 1482004793451344314, 1303419985194799104,
  1706330070288263251, 1284217081686950269, 1534908771839358861, 1263907108971131294, 2180372850720433369, 1438500632671040530, 1443194739091193417, 1260756881119460939, 1281133775450820608, 1277683233158644943, 1153001846653014399, 1443198407916727862, 1429471236494504990, 1738746445244171269,
  1269866392353710539, 1659888275384280397, 1432565124031463816, 2180096024478042305, 1468854575909721223, 1432959259150773052, 1482002525708612027, 1465046212219723776, 2161518793791144965, 1429471236494505034, 1502822381138118699, 1446935397409116618, 2157864441101188673, 2184162413722113111,
  1303545053041275862, 1731710259040355473, 1430132386791728146, 1783212439429488198, 1438500493839668245, 2142383317382102600, 2184443888698823767, 1303545065219027387, 1429581667871543296, 1499448502711269378, 1482004793451347537, 1277584829129265152, 1277646203359931984, 2183964363912737269,
  1312833781366797270, 2178696782563771537, 1303419985194800212, 1753056564699725393, 1277187148575465938, 1696759091010455304, 1258563345004671391, 1442627693028598990, 1462227268607702024, 1741553197933213702, 1446935397415048168, 2157864441101188673, 2185569788605666391, 1481996202745377762,
  1465046212219723776, 2161518793791144965, 1429471236487930954, 1822057311045060651, 1469417938986734612, 1964213865856466418, 1277695259993554517, 1432959713101987840, 1732268646870120451, 1430056314650248224, 2182065067988576587, 1468854573971059847, 1772529269176621247, 2186176236730172384,
  1152961037920948606, 2185129389665644087, 1277479826201158133, 1686630257036961876, 1267328513358201273, 1499447045811386144, 1286433833474896326, 1281019642472922709, 2178616339354612155, 1269545405279196244, 1722979972638668803, 1430044220022338589, 2181500790974056603, 1469417938986763273,
  1964213865856466363, 1277695259993218648, 2177003672196612479, 1443474409622172818, 2182913958493676551, 1432565123746137107, 2180096024478042265, 1468854575909721223, 1281245071337450300, 1152961037920104891, 2185129389665644087, 1277177872820380149, 1432960168422311689, 1481992079375356363,
  1465046212219723776, 2161518793791144965, 1429471236494505034, 1783775199800227877, 1479401777643762708, 1962520669724179685, 1260756925082645662, 2177208954508612185, 1294192471817073814, 1499448529924589354, 1280272032976761226, 2013740352189278002, 1450300522186703831, 2181498727091550248,
  1433341723112936457, 1433241756798896457, 1322114291798176159, 1483623197443355793, 1669181101876419139, 1446359734088049200, 1784062312391522343, 2188156318120195032, 2177208954505909393, 1465046212219724950, 1932924099628341827, 1302072328004727316, 1669181101876496831, 1295801744906199600,
  2187368356433463844, 1267910155446858171, 1678184077919246176, 1281118521169600978, 1516332795668424052, 1269545266538451379, 1443193141363359324, 1446711511020991518, 1739584110633773064, 1479401777509700583, 1921143123288147645, 1447122977810556065, 2176927489480074374, 1483623216162493586,
  1443197719697982469, 1466100436835922974, 1612634349578569109, 1415648997855032214, 1266140170998691496, 1408466094491665230, 1394679862626096669, 1462331308737909611, 1885114792083981456, 1415648998838936664, 1565059013936854696, 1446298069247587160, 2176927489480074199, 1465046208896951442,
  1445161009546298373, 1434540190261298209, 1921702113633938943, 1466100436835923046, 2188528066458897849, 1398760294100591450, 1653163521710945957, 1407965404240421758, 1303294175780357559, 1394251128463143866, 1481752604024640918, 1426750359663239168, 1443197719697982469, 1447313631407928350,
  1952941595070936748, 1318778634835747926, 1465046192577835517, 2189103341509353053, 1299754498065634439, 1731705782797535031, 1429691045673042902, 2178616329389462499, 1482218452619056212, 1916640661508335287, 1298117934489584139, 1304671916004887091, 1260298573226733987, 1311082229658261285,
  1152961028189614489, 1687187224201500456, 1433068772058308198, 1399463092469067776, 1617137949205939605, 1404682262698435479, 2169389912656631434, 1421485344489751375, 1313052754582013392, 1153001776591024629, 1887889686673079861, 1318777879041294850, 2116128884559696255, 1465046212219724748,
  1730025601625894498, 1277755870558351755, 2189622605300467801, 1293785033909621894, 1899147432984332075, 1484131053192336477, 1782367303062111923, 1470896153735627808, 1741554522008471265, 1433693705021346834, 1411569125465038093, 2177208961336431751, 1394548686092395670, 1616287582339458801,
  1421485343791186795, 1585325952521029013, 1296218597197975147, 2178696782563770943, 1429864932574458964, 2189384009048541228, 1466100437695714274, 1822341329062021272, 1311039598339462194, 1669176878681421955, 1299415426034479604, 1908758621208814925, 1484131043357807713, 2093368481055008433,
  1411569124810732553, 1625019320930516119, 1391079312608666537, 1318777768160710079, 1465046192577835517, 1951542339739131485, 1298626252323853404, 1478946302978348843, 2176646014503367641, 1470050019702408283, 1555507181003336295, 1394539336918725464, 1631770735044820118, 1404682263184880495,
  1572100716518482355, 1391558287377306546, 1467393320730157590, 2176646014503314566, 1467793546964304987, 1623892347903642153, 1399042867911611245, 1556338117822685619, 1478946349299716953, 1153001785653027801, 2192485466656515760, 1411437181127812006, 1632620728215643890, 1393964705216402347,
  1462326771132599731, 1651132232162489305, 1422697556171760534, 1565063257884636840, 1478933842388267864, 1153001785653027801, 1902564850299944501, 1394681040477525086, 1631770459227389078, 1407965404686848879, 2156438713217402295, 1314804600857222770, 1482218452619055104, 1885114792088595115,
  1429864929554736216, 2190519144812482155, 1416354682165200007, 1612911701386429846, 1398760294100591450, 1653163521710945957, 1410853135070073726, 2084669330409858513, 1479218753360192335, 2116209337734005904, 1432960607562462156, 2190514728462625485, 1488362042471564441, 1773086361918512166,
  1443909883939542044, 1616298191227364759, 1411437180925776731, 1462516793258688914, 1152961026847142763, 2116209337738817079, 1318964409118475212, 1648113619119966655, 1411437181119423622, 1782367303280172637, 1446932580800242720, 1902571035874438753, 1484897893681894494, 1266150771548378708,
  1429569780054778702, 1732787135221482507, 1434540181365257235, 1672886997194316790, 2194844924005528072, 1152961026847142763, 2116209612633230908, 1482218453541807052, 1927858441236569714, 1430428569446511721, 1920022484430702744, 1411437181119423588, 1638828432152641140, 1434894646149903520,
  1741554142876629828, 1391572722214085650, 1462235435957401257, 2176927489832653783, 1485179778630018194, 1444316946601385471, 2195364922978907108, 2177208954505908607, 1426750359663240342, 1902569762349993532, 1301711757301458014, 1648678545264122561, 1430428566702920868, 1782371882369108120,
  1415917485121033248, 1730012751301539441, 1462235436159922571, 2113949635369875116, 1407967745113432941, 2014866345262357702, 1299415434161848881, 1635728169250708561, 1429972542969659000, 1483623197443355133, 2116209337738546748, 1432960607478731724, 1772196863116050039, 1281133579147322388,
  1616288307280913615, 1449184516070011755, 2180104743547169383, 1465554044236162079, 1444319147587051955, 1434643338425865188, 1666358006433757221, 1299415425766040113, 2093125006403014093, 1487434811741779049, 1429972542980332625, 1450312736765637117, 2195572362781477016, 2196322187737957451,
  1429972542985446474, 2177008207598191717, 1399028987516621970, 1772239058655085974, 1487434743089456148, 1952941001777969988, 1417343688670463130, 1296259907177656762, 2178697057458455103, 1426750359663240276, 1772238783207573692, 1277479823239246868, 1902566654001880669, 1432960606518023262,
  1617132825309965945, 1462235718085079975, 1952937530874246828, 1443909882433053782, 1446005417329913250, 1446641475080172518, 1741512777037297701, 1310954317249979368, 2147408362443065130, 1470936295183733304, 2040493774463420083, 1152961026849607292, 1822341329062284860, 1468291214446408754,
  1929265338273662687, 1318600255409975825, 2189665569672670818, 1314804656664765399, 1465046211296972800, 1902565827287785053, 1430147712412202078, 1648111471353691763, 1318600254893614184, 2193039156592914018, 1393962369224741981, 2059892868297172375, 1400454915618575255, 1265853196400031443,
  1419299171249910666, 1275702855385912757, 1481751982568783486, 1479405214680436736, 1902566791541204656, 1467582990726108254, 1555771044147134065, 1411818436759528298, 1644718721882035793, 1407965404720518007, 1564221479191135671, 2197505119095808937, 2116128894510535638, 1462098696239264716,
  1732273466377628263, 1433244073485059104, 1445446453039236101, 1399183402011964389, 1266136711804812691, 1394109085613384612, 1653161529232160340, 1411139626120926078, 1314837321591817655, 1483623216045080576, 1892395347563503229, 1479405212449371281, 1855242093514360543, 1317208076959052304,
  1909603236560480684, 1320308551875527237, 2188821866530278100, 1312401757858440210, 2016525248024893901, 2198201593810179123, 1301889335227855289, 1667771498154164725, 1263907245524361671, 1152961034846742530, 2196988395547881015, 1482146287987794429, 2194138171898694380, 1468854576054211719,
  1917447512470750943, 1293785996448252487, 2197511468925036972, 1311039127393141718, 1830470779588921201, 1260005698228982274, 1499445338947763219, 2198741994158002630, 1294008035880014339, 1260005698228981760, 1499445338947761956, 2199023469134713286, 1432215616802394924, 1426750340023555159,
  1945886833538695971, 1381120345360200431, 1468710431881380667, 1465708390771954665, 1381734563592921088, 1945888103439973124, 1375918762014995185, 1295603359724815163, 1483623197443355607, 2116209337738546748, 1450312753304052684, 1932642230540028058, 1467793548159234616, 1854960132803627561,
  1470896163043000908, 2195023536677480119, 1465554049295893578, 1444319147587410982, 1434540191250432996, 2199240987632065617, 1152961034802052743, 1939960579932270214, 1311039120644850264, 1859178811898152746, 1301711618598924855, 1152961034813214339, 2198395770431434295, 1449184518422701017,
  1892395347563503229, 1295603351780410513, 2189103341508640391, 1311068059098023047, 1689165725753050847, 1312690243461988884, 2017085045304527295, 2200008427619688073, 1430429598293722071, 2196984523064027466, 1450116690073199101, 1752494437836520859, 1286771934409949626, 1697604057173575432,
  2177208954508574346, 1430429597310682262, 1932642230539995288, 1469486658627056184, 2060178500937419305, 1462235719109383003, 1608971051712480662, 2200880482354742181, 2196988395543069247, 1319745190749872637, 1822341329061781122, 1446359734090761266, 1689165725750730377, 1468854576716751380,
  1928706649447892703, 1301711755903943245, 1830467215588293069, 1315025458829438604, 2200852851539368296, 1478908691558601279, 1465046192579752920, 1635165684795190925, 1449184518422701152, 1673127783580326528, 2202471195446342132, 2178616337243145350, 1455389053014295636, 1648113120738412209,
  1296101155287921768, 1908718559868046035, 1302011304389218825, 1855240508249671479, 1294151927727968844, 1152989003657058162, 1772238093563817527, 1411569127539672084, 1616289401107281521, 1415283822355424091, 1608987426612139605, 1487434743055877195, 1920021207433240186, 1152989006582075028,
  1732264689208708446, 1438500493906916384, 2182062343888868366, 2176927486360190613, 1481939311907116178, 1782934308235905034, 1462227268238619621, 1443194765867630150, 1465046192579505814, 1732263859425193526, 1430149154411299872, 1635167848219872895, 1443936069189596256, 2150537284037507747,
  1447216736812385429, 2027814580318997035, 1443438652738343905, 2200929045217018985, 1297855639177486911, 1934898069048796165, 1321998640334398034, 1855235990581729988, 1478940508832674320, 1429586548866924544, 1636854534655422092, 1300319361905030242, 1936305301542378764, 1321138133422367256,
  1153001090164823956, 1636811824110587452, 1316304003489535074, 1932646336577210226, 1300319362303734268, 1394683949554563533, 2178616339172528696, 1467016052866638932, 1934657909524745881, 1296101164523917846, 1648074502537517693, 1318600254893614184, 2019093852580707358, 1467793545227535379,
  2193317229939173040, 1153001098288795291, 2204861037751389756, 1468291213918335476, 1934612470903908016, 1299754498895720982, 1902565827285162694, 1318600255409976414, 2019093852580707358, 1432960536118973459, 1608129749206806170, 1404682263050474345, 1564781662111596067, 1416335919327306644,
  1482222787219527169, 2116205077227111558, 1470546173225436108, 2180663639135364791, 1434540331040912421, 1479126659633605436, 1315025477548855296, 1648102841388453436, 1482222780553987176, 2205395599948237364, 1446756109587383257, 1301797477220848803, 2201134334388408888, 1426750356509516282,
  1823994454338530009, 1312407677109052468, 1689453602963507647, 1446711372474540532, 1468712207129744547, 2201496530572018173, 1479126625804337666, 1891579388671872350, 1450312753303991441, 1885114792088291482, 1310674425190274136, 2206240013939918649, 1487434810890392080, 1952954437341589110,
  1432639891397317718, 1732828807192003595, 1296274038032872467, 1297855642398322688, 2204015920392203933, 1468712190145160150, 2194177820556117683, 1434894646530261977, 1733114309371832363, 2207116434390688741, 2177244329163096573, 1465046212018820246, 1885118296127008406, 1430428568779125848,
  1648399233893648538, 1484897893946889290, 1952909787295620364, 1443907884800402518, 1313056773831083818, 2209205978730729472, 2200887883944952976, 2209476606196666943, 2178696647037420097, 1484400011950826580, 1293917013479381598, 2210267695787184128, 2178651360784811113, 1482497238359483476,
  2203983490369220253, 1447008025765794774, 2161486868175163031, 1450128371275789386, 1487571973314592387, 2210825501040885760, 2204030769414800404, 1296449641804104662, 2210423002005961990, 1481942122426410148, 2210985950935976645, 1152989943595528781, 2203984451952774832, 2212085668252394454,
  1442627694620574728, 1433247560390274739, 2211830385429136391, 2212921033451856904, 1462239706844180480, 2180103334545936046]

set_option maxRecDepth 300000 in
set_option maxHeartbeats 0 in
private theorem checked : PEqualNP.Outside.L_meta_7889.KWCert.LRAT.checkW formula
    ((List.range formula.length).map Nat.succ) 12 words = true := by
  decide +kernel

theorem noPartition (row col : Tables)
    (hrow : ∀ v t i, row v t i = true → pos i v = true)
    (hcol : ∀ v t j, col v t j = true → neg j v = false)
    (hcover : ∀ i j, ∃ v t, row v t i = true ∧ col v t j = true)
    (hdisj : ∀ i j v t w u, row v t i = true → col v t j = true →
      row w u i = true → col w u j = true → v = w ∧ t = u) : False :=
  noPartitionOfUnsat (PEqualNP.Outside.L_meta_7889.KWCert.LRAT.checkW_sound _ _ _ _ checked)
    row col hrow hcol hcover hdisj

end PEqualNP.Outside.L_meta_7889.KWCert

namespace PEqualNP.Outside.L_meta_7889.KWForm

open PEqualNP.MetaComplexity

def vars {n : ℕ} : DMFormula n → List (Fin n)
  | .lit i _ => [i]
  | .and a b => vars a ++ vars b
  | .or a b => vars a ++ vars b

def positive {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

private def Valid (val : (Fin n → Bool) → Bool) (p q : Fin n → Bool) : Prop :=
  val p = true ∧ val q = false

private def RectangleFamily (V : List (Fin n)) (val : (Fin n → Bool) → Bool)
    (p q : Fin 15 → Fin n → Bool) : Prop :=
  ∃ row col : Fin V.length → Fin 15 → Bool,
    (∀ k i, row k i = true → p i (V.get k) = true) ∧
    (∀ k j, col k j = true → q j (V.get k) = false) ∧
    (∀ k i j, row k i = true → col k j = true → Valid val (p i) (q j)) ∧
    (∀ i j, Valid val (p i) (q j) → ∃! k, row k i = true ∧ col k j = true)

private def combined (isAnd a b : Bool) : Bool := if isAnd then a && b else a || b

private def leftOn (isAnd pA qA : Bool) : Bool := if isAnd then !qA else pA

private theorem leftSplit (isAnd pA pB qA qB : Bool) :
    (pA = true ∧ qA = false ∧ (!isAnd || pB) = true ∧ (isAnd || !qB) = true) ↔
    (combined isAnd pA pB = true ∧ combined isAnd qA qB = false ∧
      leftOn isAnd pA qA = true) := by
  cases isAnd <;> cases pA <;> cases pB <;> cases qA <;> cases qB <;> decide

private theorem rightSplit (isAnd pA pB qA qB : Bool) :
    (pB = true ∧ qB = false ∧ pA = isAnd ∧ qA = isAnd) ↔
    (combined isAnd pA pB = true ∧ combined isAnd qA qB = false ∧
      leftOn isAnd pA qA = false) := by
  cases isAnd <;> cases pA <;> cases pB <;> cases qA <;> cases qB <;> decide

private theorem join {A B : List (Fin n)} {fa fb : (Fin n → Bool) → Bool}
    {p q : Fin 15 → Fin n → Bool} (b : Bool) (sa : RectangleFamily A fa p q) (sb : RectangleFamily B fb p q) :
    RectangleFamily (A ++ B) (fun x => combined b (fa x) (fb x)) p q := by
  obtain ⟨ra, ca, har, hac, hav, hau⟩ := sa
  obtain ⟨rb, cb, hbr, hbc, hbv, hbu⟩ := sb
  let inL (k : Fin A.length) : Fin (A ++ B).length := ⟨k.val, by rw [List.length_append]; omega⟩
  let inR (k : Fin B.length) : Fin (A ++ B).length := ⟨A.length + k.val, by rw [List.length_append]; omega⟩
  let leftR (k : Fin A.length) (i : Fin 15) := ra k i && (!b || fb (p i))
  let leftC (k : Fin A.length) (j : Fin 15) := ca k j && (b || !(fb (q j)))
  let rightR (k : Fin B.length) (i : Fin 15) := rb k i && (fa (p i) == b)
  let rightC (k : Fin B.length) (j : Fin 15) := cb k j && (fa (q j) == b)
  let row (k : Fin (A ++ B).length) : Fin 15 → Bool :=
    Fin.addCases leftR rightR (Fin.cast (List.length_append) k)
  let col (k : Fin (A ++ B).length) : Fin 15 → Bool :=
    Fin.addCases leftC rightC (Fin.cast (List.length_append) k)
  have casesIndex (k : Fin (A ++ B).length) : (∃ i, k = inL i) ∨ (∃ i, k = inR i) := by
    by_cases t : k.val < A.length
    · exact Or.inl ⟨⟨k.val, t⟩, Fin.ext rfl⟩
    · have hk : k.val < A.length + B.length := by simpa only [List.length_append] using k.isLt
      exact Or.inr ⟨⟨k.val - A.length, by omega⟩, Fin.ext (by dsimp [inR]; omega)⟩
  have getL (k : Fin A.length) : (A ++ B).get (inL k) = A.get k := List.getElem_append_left k.isLt
  have getR (k : Fin B.length) : (A ++ B).get (inR k) = B.get k := by
    simpa only [List.get_eq_getElem, inR, Nat.add_comm] using (List.getElem_append_right' A k.isLt).symm
  have rowL (k : Fin A.length) : row (inL k) = leftR k := by
    change Fin.addCases leftR rightR (Fin.castAdd B.length k) = leftR k
    simp
  have colL (k : Fin A.length) : col (inL k) = leftC k := by
    change Fin.addCases leftC rightC (Fin.castAdd B.length k) = leftC k
    simp
  have rowR (k : Fin B.length) : row (inR k) = rightR k := by
    change Fin.addCases leftR rightR (Fin.natAdd A.length k) = rightR k
    simp
  have colR (k : Fin B.length) : col (inR k) = rightC k := by
    change Fin.addCases leftC rightC (Fin.natAdd A.length k) = rightC k
    simp
  have leftHit (k : Fin A.length) (i j : Fin 15) :
      row (inL k) i = true ∧ col (inL k) j = true ↔
        (ra k i = true ∧ ca k j = true) ∧ (!b || fb (p i)) = true ∧ (b || !(fb (q j))) = true := by
    rw [rowL, colL]
    simp only [leftR, leftC, Bool.and_eq_true]
    tauto
  have rightHit (k : Fin B.length) (i j : Fin 15) :
      row (inR k) i = true ∧ col (inR k) j = true ↔
        (rb k i = true ∧ cb k j = true) ∧ fa (p i) = b ∧ fa (q j) = b := by
    rw [rowR, colR]
    simp only [rightR, rightC, Bool.and_eq_true, beq_iff_eq]
    tauto
  have leftGood (i j : Fin 15) (k : Fin A.length)
      (h : row (inL k) i = true ∧ col (inL k) j = true) := by
    obtain ⟨h, a, d⟩ := (leftHit k i j).1 h
    exact (leftSplit _ _ _ _ _).1 ⟨(hav k i j h.1 h.2).1, (hav k i j h.1 h.2).2, a, d⟩
  have rightGood (i j : Fin 15) (k : Fin B.length)
      (h : row (inR k) i = true ∧ col (inR k) j = true) := by
    obtain ⟨h, a, d⟩ := (rightHit k i j).1 h
    exact (rightSplit _ _ _ _ _).1 ⟨(hbv k i j h.1 h.2).1, (hbv k i j h.1 h.2).2, a, d⟩
  refine ⟨row, col, ?_, ?_, ?_, ?_⟩
  · intro k i h
    rcases casesIndex k with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [getL]; simp only [rowL, leftR, Bool.and_eq_true] at h; exact har k i h.1
    · rw [getR]; simp only [rowR, rightR, Bool.and_eq_true] at h; exact hbr k i h.1
  · intro k j h
    rcases casesIndex k with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [getL]; simp only [colL, leftC, Bool.and_eq_true] at h; exact hac k j h.1
    · rw [getR]; simp only [colR, rightC, Bool.and_eq_true] at h; exact hbc k j h.1
  · intro k i j r c
    rcases casesIndex k with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h := leftGood i j k ⟨r, c⟩; exact ⟨h.1, h.2.1⟩
    · have h := rightGood i j k ⟨r, c⟩; exact ⟨h.1, h.2.1⟩
  · intro i j h
    cases s : leftOn b (fa (p i)) (fa (q j)) with
    | false =>
      obtain ⟨hp, hq, r, c⟩ := (rightSplit _ _ _ _ _).2 ⟨h.1, h.2, s⟩
      obtain ⟨k, hit, unique⟩ := hbu i j ⟨hp, hq⟩
      refine ⟨inR k, (rightHit k i j).2 ⟨hit, r, c⟩, ?_⟩
      intro l hl
      rcases casesIndex l with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact False.elim (Bool.false_ne_true (s.symm.trans (leftGood _ _ _ hl).2.2))
      · exact congrArg inR (unique u ((rightHit u i j).1 hl).1)
    | true =>
      obtain ⟨hp, hq, r, c⟩ := (leftSplit _ _ _ _ _).2 ⟨h.1, h.2, s⟩
      obtain ⟨k, hit, unique⟩ := hau i j ⟨hp, hq⟩
      refine ⟨inL k, (leftHit k i j).2 ⟨hit, r, c⟩, ?_⟩
      intro l hl
      rcases casesIndex l with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact congrArg inL (unique u ((leftHit u i j).1 hl).1)
      · exact False.elim (Bool.false_ne_true ((rightGood _ _ _ hl).2.2.symm.trans s))

private theorem rectangles (φ : DMFormula n) (hf : positive φ) (p q : Fin 15 → Fin n → Bool) :
    RectangleFamily (vars φ) φ.eval p q := by
  induction φ with
  | lit v b =>
    change b = true at hf
    subst b
    change RectangleFamily [v] (fun x => x v) p q
    let z : Fin ([v] : List (Fin n)).length := ⟨0, by simp⟩
    have zeroIndex (k : Fin ([v] : List (Fin n)).length) : k = z := by
      apply Fin.ext
      change k.val = 0
      have h : k.val < 1 := by simpa only [List.length_singleton] using k.isLt
      omega
    refine ⟨fun _ i => p i v, fun _ j => !(q j v), ?_, ?_, ?_, ?_⟩
    · intro k i h; rw [zeroIndex k]; exact h
    · intro k j h; rw [zeroIndex k]; simpa using h
    · intro k i j r c; exact ⟨r, by simpa using c⟩
    · intro i j h
      exact ⟨z, ⟨h.1, by simpa using h.2⟩, fun k _ => zeroIndex k⟩
  | and a b ihA ihB => exact join true (ihA hf.1) (ihB hf.2)
  | or a b ihA ihB => exact join false (ihA hf.1) (ihB hf.2)

theorem smallPartition (φ : DMFormula n) (hm : positive φ)
    (read : ∀ v, (vars φ).count v ≤ 2)
    (p q : Fin 15 → Fin n → Bool)
    (hp : ∀ i, φ.eval (p i) = true) (hq : ∀ j, φ.eval (q j) = false) :
    ∃ row col : Fin n → Fin 2 → Fin 15 → Bool,
      (∀ v t i, row v t i = true → p i v = true) ∧
      (∀ v t j, col v t j = true → q j v = false) ∧
      (∀ i j, ∃ v t, row v t i = true ∧ col v t j = true) ∧
      (∀ i j v t w u, row v t i = true → col v t j = true →
        row w u i = true → col w u j = true → v = w ∧ t = u) := by
  obtain ⟨ra, ca, rlabel, clabel, _, unique⟩ := rectangles φ hm p q
  let V := vars φ
  let slots (v : Fin n) := (List.finRange V.length).filter (fun k => V.get k == v)
  have len (v : Fin n) : (slots v).length ≤ 2 := by
    have eq : (slots v).length = V.count v := by
      calc
        (slots v).length = (List.finRange V.length).countP (fun k => V.get k == v) :=
          List.countP_eq_length_filter.symm
        _ = ((List.finRange V.length).map V.get).countP (· == v) :=
          (List.countP_map (p := fun a : Fin n => a == v) (f := V.get)
            (l := List.finRange V.length)).symm
        _ = V.count v := by rw [← List.ofFn_eq_map, List.ofFn_get] <;> rfl
    rw [eq]
    exact read v
  have nodup (v : Fin n) : (slots v).Nodup := (List.nodup_finRange _).filter _
  have getLabel {v : Fin n} {t : Fin 2} {k : Fin V.length}
      (h : (slots v)[t.val]? = some k) : V.get k = v :=
    beq_iff_eq.mp ((List.mem_filter.mp (List.mem_of_getElem? h)).2)
  let row (v : Fin n) (t : Fin 2) (i : Fin 15) :=
    ((slots v)[t.val]?.map (fun k => ra k i)).getD false
  let col (v : Fin n) (t : Fin 2) (j : Fin 15) :=
    ((slots v)[t.val]?.map (fun k => ca k j)).getD false
  refine ⟨row, col, ?_, ?_, ?_, ?_⟩
  · intro v t i h
    cases ht : (slots v)[t.val]? with
    | none => simp [row, ht] at h
    | some k =>
      have la : p i (V.get k) = true := rlabel k i (by simpa [row, ht] using h)
      exact (getLabel ht) ▸ la
  · intro v t j h
    cases ht : (slots v)[t.val]? with
    | none => simp [col, ht] at h
    | some k =>
      have la : q j (V.get k) = false := clabel k j (by simpa [col, ht] using h)
      exact (getLabel ht) ▸ la
  · intro i j
    obtain ⟨k, h, _⟩ := unique i j ⟨hp i, hq j⟩
    have ks : k ∈ slots (V.get k) := by simp [slots]
    obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp ks
    have tlt : t < 2 := lt_of_lt_of_le (List.getElem?_eq_some_iff.1 ht).choose (len _)
    refine ⟨V.get k, ⟨t, tlt⟩, ?_⟩
    change ((slots (V.get k))[t]?.map (fun a => ra a i)).getD false = true ∧
      ((slots (V.get k))[t]?.map (fun a => ca a j)).getD false = true
    rw [ht]
    exact h
  · intro i j v t w u vr vc wr wc
    cases vt : (slots v)[t.val]? with
    | none => simp [row, vt] at vr
    | some k =>
      cases wu : (slots w)[u.val]? with
      | none => simp [row, wu] at wr
      | some l =>
        obtain ⟨a, _, only⟩ := unique i j ⟨hp i, hq j⟩
        have e : k = l :=
          (only k ⟨by simpa [row, vt] using vr, by simpa [col, vt] using vc⟩).trans
          (only l ⟨by simpa [row, wu] using wr, by simpa [col, wu] using wc⟩).symm
        subst l
        have label : v = w := (getLabel vt).symm.trans (getLabel wu)
        refine ⟨label, ?_⟩
        subst w
        obtain ⟨tl, htl⟩ := List.getElem?_eq_some_iff.1 vt
        obtain ⟨ul, hul⟩ := List.getElem?_eq_some_iff.1 wu
        exact Fin.ext ((nodup v).getElem_inj_iff.mp (htl.trans hul.symm))

end PEqualNP.Outside.L_meta_7889.KWForm

namespace PEqualNP.Outside.L_meta_7889.KWForm

open PEqualNP.MetaComplexity

theorem noFormula (φ : DMFormula 10) (hm : positive φ)
    (read : ∀ v, (vars φ).count v ≤ 2)
    (hp : ∀ i, φ.eval (KWCert.pos i) = true)
    (hq : ∀ j, φ.eval (KWCert.neg j) = false) : False := by
  obtain ⟨row, col, hr, hc, cover, disj⟩ :=
    smallPartition φ hm read KWCert.pos KWCert.neg hp hq
  exact KWCert.noPartition row col hr hc cover disj

end PEqualNP.Outside.L_meta_7889.KWForm

namespace PEqualNP.Outside.L_meta_7889.PetersenFormula

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7889.PetersenNormalize

/-- The input labels of a formula, counting every leaf occurrence. -/
def vars : DMFormula n → List (Fin n)
  | .lit i _ => [i]
  | .and a b => vars a ++ vars b
  | .or a b => vars a ++ vars b

def positive : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

def Step (n : ℕ) (D : Dag) (a b : ℕ) : Prop := ∃ j ∈ readers D a, b = n + j

abbrev Path (n : ℕ) (D : Dag) := Relation.ReflTransGen (Step n D)

theorem step_lt {n : ℕ} {D : Dag} (strict : Strict n D) {a b : ℕ} (h : Step n D a b) :
    a < b ∧ b < n + D.length := by
  obtain ⟨j, hj, rfl⟩ := h
  obtain ⟨hj, hread⟩ := Finset.mem_filter.mp hj
  have hlt := Finset.mem_range.mp hj
  have hs := strict j hlt
  rcases hread with h | h <;> omega

theorem path_le {n : ℕ} {D : Dag} (strict : Strict n D) {a b : ℕ} (h : Path n D a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ edge ih => exact ih.trans (step_lt strict edge).1.le

abbrev InternalOne (n : ℕ) (D : Dag) : Prop :=
  ∀ w, n ≤ w → w + 1 < n + D.length → fanout D w = 1

theorem step_unique {n : ℕ} {D : Dag} (strict : Strict n D) (one : InternalOne n D)
    {a b c : ℕ} (ha : n ≤ a) (hb : Step n D a b) (hc : Step n D a c) : b = c := by
  have hl := step_lt strict hb
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hc
  have card : (readers D a).card = 1 := one a ha (by omega)
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp card
  rw [hp, Finset.mem_singleton] at hj hk
  rw [hj, hk]

/-- A unit-fanout internal wire can reach a gate along only one of its incoming arms. -/
theorem path_last_unique {n : ℕ} {D : Dag} (strict : Strict n D) (one : InternalOne n D)
    {w a b c : ℕ} (hw : n ≤ w) (ha : Path n D w a) (hb : Path n D w b)
    (hac : Step n D a c) (hbc : Step n D b c) : a = b := by
  have hla := (step_lt strict hac).1
  have hlb := (step_lt strict hbc).1
  generalize hd : c - w = d
  induction d using Nat.strong_induction_on generalizing w with
  | ind d ih =>
    rcases Relation.ReflTransGen.cases_head ha with (rfl | ⟨a', hwa, hpa⟩)
    · rcases Relation.ReflTransGen.cases_head hb with (rfl | ⟨b', hwb, hpb⟩)
      · rfl
      · have he := step_unique strict one hw hwb hac
        have hl := path_le strict hpb
        omega
    · rcases Relation.ReflTransGen.cases_head hb with (rfl | ⟨b', hwb, hpb⟩)
      · have he := step_unique strict one hw hwa hbc
        have hl := path_le strict hpa
        omega
      · have he := step_unique strict one hw hwa hwb
        subst b'
        have hlt := (step_lt strict hwa).1
        have hle := path_le strict hpa
        exact ih (c - a') (by omega) (by omega) hpa hpb rfl

theorem read_step {n : ℕ} {D : Dag} {j u : ℕ} (hj : j < D.length)
    (h : opA D j = u ∨ opB D j = u) : Step n D u (n + j) :=
  ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩, rfl⟩

/-- Witness sets for the two arms of a gate are kept disjoint before merging. -/
def Arm (n : ℕ) (D : Dag) (j u : ℕ) (φ : DMFormula n) : Prop :=
  ∀ v : Fin n, ∃ S : Finset ℕ, S ⊆ readers D v.val ∧ (vars φ).count v = S.card ∧
    ∀ k ∈ S, (u = v.val ∧ k = j) ∨ (n ≤ u ∧ Path n D (n + k) u)

theorem input_arm {n : ℕ} {D : Dag} (j u : ℕ) (hu : u < n)
    (hs : Step n D u (n + j)) : Arm n D j u (.lit ⟨u, hu⟩ true) := by
  intro v
  by_cases he : v = ⟨u, hu⟩
  · subst v
    have hj : j ∈ readers D u := by
      obtain ⟨k, hk, he⟩ := hs
      have hjk : j = k := by omega
      simpa only [hjk] using hk
    exact ⟨{j}, Finset.singleton_subset_iff.mpr hj, by simp [vars],
      fun k hk => Or.inl ⟨rfl, Finset.mem_singleton.mp hk⟩⟩
  · exact ⟨∅, Finset.empty_subset _, by simp [vars, he, Ne.symm he], by simp⟩

theorem arms_disjoint {n : ℕ} {D : Dag} (strict : Strict n D) (one : InternalOne n D)
    {j a b v : ℕ} {S T : Finset ℕ} (hab : a ≠ b)
    (ha : Step n D a (n + j)) (hb : Step n D b (n + j))
    (hS : ∀ k ∈ S, (a = v ∧ k = j) ∨ (n ≤ a ∧ Path n D (n + k) a))
    (hT : ∀ k ∈ T, (b = v ∧ k = j) ∨ (n ≤ b ∧ Path n D (n + k) b)) : Disjoint S T := by
  rw [Finset.disjoint_left]
  intro k hk hl
  rcases hS k hk with ⟨e₁, hkJ⟩ | ⟨_, p₁⟩
  · rcases hT k hl with ⟨e₂, _⟩ | ⟨_, p₂⟩
    · exact hab (e₁.trans e₂.symm)
    · have hm := path_le strict p₂
      have hn := (step_lt strict hb).1
      omega
  · rcases hT k hl with ⟨_, hkJ⟩ | ⟨_, p₂⟩
    · have hm := path_le strict p₁
      have hn := (step_lt strict ha).1
      omega
    · exact hab (path_last_unique strict one (Nat.le_add_right n k) p₁ p₂ ha hb)

set_option maxHeartbeats 500000 in
theorem wire_formula {n : ℕ} {D : Dag} (strict : Strict n D) (one : InternalOne n D)
    (w : ℕ) (hw₁ : n ≤ w) (hw₂ : w < n + D.length) :
    ∃ φ : DMFormula n, positive φ ∧ (∀ x, φ.eval x = val D x w) ∧
      ∀ v : Fin n, ∃ S : Finset ℕ, S ⊆ readers D v.val ∧ (vars φ).count v = S.card ∧
        ∀ k ∈ S, Path n D (n + k) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    let j := w - n
    have hEq : w = n + j := by omega
    have hj : j < D.length := by omega
    obtain ⟨ha, hb, hab⟩ := strict j hj
    let a := opA D j
    let b := opB D j
    have stepA : Step n D a (n + j) := read_step hj (Or.inl rfl)
    have stepB : Step n D b (n + j) := read_step hj (Or.inr rfl)
    have makeArm (u : ℕ) (hs : Step n D u (n + j)) :
        ∃ φ : DMFormula n, positive φ ∧ (∀ x, φ.eval x = val D x u) ∧ Arm n D j u φ := by
      by_cases hu : u < n
      · refine ⟨.lit ⟨u, hu⟩ true, rfl, ?_, input_arm j u hu hs⟩
        intro x
        exact (val_input D x u hu).symm
      · have hlt := (step_lt strict hs).1
        have hn : n ≤ u := Nat.le_of_not_gt hu
        obtain ⟨φ, hp, he, count⟩ := ih u (by omega) hn (by omega)
        refine ⟨φ, hp, he, ?_⟩
        intro v
        obtain ⟨S, hm, hc, hS⟩ := count v
        exact ⟨S, hm, hc, fun k hk => Or.inr ⟨hn, hS k hk⟩⟩
    obtain ⟨A, pA, eA, hA⟩ := makeArm a stepA
    obtain ⟨B, pB, eB, hB⟩ := makeArm b stepB
    let φ : DMFormula n := if tag D j then .and A B else .or A B
    refine ⟨φ, ?_, ?_, ?_⟩
    · unfold φ
      split <;> exact ⟨pA, pB⟩
    · intro x
      rw [hEq, val_gate strict x j hj]
      unfold φ
      cases htag : tag D j <;> simp [htag, DMFormula.eval, gop, eA, eB, a, b]
    · intro v
      obtain ⟨S, hS, hcs, hs⟩ := hA v
      obtain ⟨T, hT, hct, ht⟩ := hB v
      have hdis := arms_disjoint strict one hab stepA stepB hs ht
      refine ⟨S ∪ T, Finset.union_subset hS hT, ?_, ?_⟩
      · unfold φ
        split <;> simp only [vars, List.count_append, hcs, hct, Finset.card_union_of_disjoint hdis]
      · intro k hk
        rw [hEq]
        have lift (u : ℕ) (hu : Step n D u (n + j))
            (hk : (u = v.val ∧ k = j) ∨ (n ≤ u ∧ Path n D (n + k) u)) :
            Path n D (n + k) (n + j) := by
          rcases hk with ⟨_, rfl⟩ | ⟨_, p⟩
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.tail p hu
        rcases Finset.mem_union.mp hk with hk | hk
        · exact lift a stepA (hs k hk)
        · exact lift b stepB (ht k hk)

theorem circuit_formula {D : Dag} (live : StrictLive 10 D)
    (two : ∀ i < 10, fanout D i = 2) (one : InternalOne 10 D) :
    ∃ φ : DMFormula 10, positive φ ∧ (∀ v, (vars φ).count v ≤ 2) ∧
      ∀ x, φ.eval x = val D x (outW 10 D) := by
  have hpos : 0 < D.length := List.length_pos_iff.mpr live.2.2
  have hw₁ : 10 ≤ outW 10 D := by unfold outW; omega
  have hw₂ : outW 10 D < 10 + D.length := by unfold outW; omega
  obtain ⟨φ, pos, evaluate, count⟩ := wire_formula live.1 one (outW 10 D) hw₁ hw₂
  refine ⟨φ, pos, ?_, evaluate⟩
  intro v
  obtain ⟨S, hS, hc, _⟩ := count v
  rw [hc]
  exact (Finset.card_le_card hS).trans (le_of_eq (two v.val v.isLt))

end PEqualNP.Outside.L_meta_7889.PetersenFormula

namespace PEqualNP.Outside.L_meta_7889

open PEqualNP.MetaComplexity

private theorem sameVars (φ : DMFormula n) :
    PetersenFormula.vars φ = KWForm.vars φ := by
  induction φ <;> simp [PetersenFormula.vars, KWForm.vars, *]

private theorem samePositive (φ : DMFormula n) :
    PetersenFormula.positive φ ↔ KWForm.positive φ := by
  induction φ <;> simp [PetersenFormula.positive, KWForm.positive, *]

theorem noTwiceFormula : PetersenAssemble.TwiceFormulaImpossible := by
  intro D live _ htwice htree hcomputes
  obtain ⟨φ, pos, read, evaluates⟩ := PetersenFormula.circuit_formula live htwice htree
  have targetEq : PetersenNormalize.target = KWCert.edgeFn := rfl
  apply KWForm.noFormula φ ((samePositive φ).mp pos)
  · intro i
    rw [← sameVars]
    exact read i
  · intro i
    rw [evaluates, hcomputes, targetEq]
    exact KWCert.pos_accept i
  · intro j
    rw [evaluates, hcomputes, targetEq]
    exact KWCert.neg_reject j

end PEqualNP.Outside.L_meta_7889

theorem PEqualNP.Outside.L_meta_7889 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (19 : ℕ) →       (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 = fun (x4 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (5 : ℕ)), (x4 (Fin.castAdd (5 : ℕ) x5) && x4 (Fin.castAdd (5 : ℕ) (x5 + (1 : Fin (5 : ℕ)))) || x4 (Fin.castAdd (5 : ℕ) x5) && x4 (Fin.natAdd (5 : ℕ) x5) || x4 (Fin.natAdd (5 : ℕ) x5) && x4 (Fin.natAdd (5 : ℕ) (x5 + (2 : Fin (5 : ℕ))))) = Bool.true)) →         ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Bool),           PEqualNP.TopForm.IsAO2 (10 : ℕ) x5 ∧             ((16 : ℕ) ≤ x5.size ∧ x5.size ≤ (18 : ℕ)) ∧               (x6 ≠ (0 : ℕ) ∧ x6 < (10 : ℕ) + x5.size ∧ ∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x8 ≤ x6 → x5.gates[x8]? = Option.some x9 → (0 : ℕ) ∉ x9.inputs) ∧                 ∀ (x8 : Fin (10 : ℕ) → Bool),                   have x9 : Bool := (x5.wires (List.ofFn (Function.update x8 (0 : Fin (10 : ℕ)) Bool.false))).getD x6 Bool.false;                   PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x5 (Function.update x8 (0 : Fin (10 : ℕ)) (if x7 = Bool.true then x8 (0 : Fin (10 : ℕ)) && x9 else x8 (0 : Fin (10 : ℕ)) || x9)) = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x8) :=
  PEqualNP.Outside.L_meta_7889.PetersenAssemble.normal_form PEqualNP.Outside.L_meta_7889.noTwiceFormula
