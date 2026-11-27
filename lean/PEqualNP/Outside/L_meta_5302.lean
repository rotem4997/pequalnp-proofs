import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Choose
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import PEqualNP.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions

import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sublists


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_5302
-- The monotone rank argument below is adapted from the project proof of L-meta-531.
private theorem cover531_splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

private theorem cover531_formulaRectanglesStrong {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply cover531_splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply cover531_splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩

private theorem cover531_formulaRectangles {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x y, φ.eval x = true → φ.eval y = false → X i x → Y i y →
          x (label i) = true ∧ y (label i) = false) := by
  obtain ⟨X, Y, label, total, goodX, goodY⟩ := cover531_formulaRectanglesStrong φ mono
  exact ⟨X, Y, label, total, fun i x y _ _ hx hy => ⟨(goodX i x hx).2, (goodY i y hy).2⟩⟩

private lemma cover531_starIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (v : Fin n) : ∀ u w, G.Adj u w → ¬ (G.Adj v u ∧ G.Adj v w) := by
  intro u w huw h
  exact triangle v u w ⟨h.1, huw, h.2.symm⟩

private lemma cover531_pairIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (square : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (a b : Fin n) (edge : G.Adj a b) : ∀ u w, G.Adj u w →
      ¬ (((G.Adj a u ∨ G.Adj b u) ∧ u ≠ a ∧ u ≠ b) ∧
         ((G.Adj a w ∨ G.Adj b w) ∧ w ≠ a ∧ w ≠ b)) := by
  intro u w huw h
  rcases h with ⟨⟨hu, hua, hub⟩, ⟨hw, hwa, hwb⟩⟩
  rcases hu with hau | hbu <;> rcases hw with haw | hbw
  · exact triangle a u w ⟨hau, huw, haw.symm⟩
  · exact square a u w b hwa.symm hub ⟨hau, huw, hbw.symm, edge.symm⟩
  · exact square b u w a hwb.symm hua ⟨hbu, huw, haw.symm, edge⟩
  · exact triangle b u w ⟨hbu, huw, hbw.symm⟩

private theorem cover531_rank {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] {m : ℕ} (a b reject : E → V) (T : Finset V) (R : Fin m → (V × E → ℚ))
    (anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v))
    (units : ∀ e, Pi.single (reject e, e) 1 ∈ Submodule.span ℚ (Set.range R))
    (stars : ∀ v ∈ T, (fun p : V × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v)
      then 1 else 0) ∈ Submodule.span ℚ (Set.range R)) :
    Fintype.card E + T.card ≤ m := by
  classical
  let unit (e : E) : V × E → ℚ := Pi.single (reject e, e) 1
  let star (v : V) : V × E → ℚ :=
    fun p => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0
  let family : E ⊕ ↥T → (V × E → ℚ) := Sum.elim unit (fun v => star v.val)
  let W := Submodule.span ℚ (Set.range R)
  have inSpan (i : E ⊕ ↥T) : family i ∈ W := by
    cases i with
    | inl e => exact units e
    | inr v => exact stars v.val v.property
  have independent : LinearIndependent ℚ family := by
    rw [Fintype.linearIndependent_iff]
    intro c relation
    have atCoord (p : V × E) :
        (Finset.univ.sum fun e : E => c (Sum.inl e) * unit e p) +
          (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val p) = 0 := by
      simpa [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, family] using
        congrFun relation p
    have starZero (v : ↥T) : c (Sum.inr v) = 0 := by
      obtain ⟨e, different, incident⟩ := anchor v.val v.property
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (v.val, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h : (v.val, e) ≠ (reject j, j) := by
          intro same
          have ej : e = j := congrArg Prod.snd same
          subst j
          exact different (congrArg Prod.fst same)
        simp [unit, Pi.single_eq_of_ne h]
      have starSum : (Finset.univ.sum fun w : ↥T => c (Sum.inr w) * star w.val (v.val, e)) =
          c (Sum.inr v) := by
        rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v)]
        · simp [star, incident]
        · intro w _ differentSub
          have h : v.val ≠ w.val := fun same => differentSub (Subtype.ext same.symm)
          simp [star, h]
      simpa only [unitSum, starSum, zero_add] using atCoord (v.val, e)
    intro i
    cases i with
    | inr v => exact starZero v
    | inl e =>
      have starSum : (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val (reject e, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        simp [starZero v]
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (reject e, e)) = c (Sum.inl e) := by
        rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
        · simp [unit]
        · intro j _ different
          have h : (reject e, e) ≠ (reject j, j) := fun same =>
            different (congrArg Prod.snd same).symm
          simp [unit, Pi.single_eq_of_ne h]
      simpa only [unitSum, starSum, add_zero] using atCoord (reject e, e)
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (i : E ⊕ ↥T) : ↥W := ⟨family i, inSpan i⟩
  have liftedIndependent : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent ℚ family
    exact independent
  have lower : Fintype.card E + T.card ≤ Module.finrank ℚ ↥W := by
    simpa only [Fintype.card_sum, Fintype.card_coe] using liftedIndependent.fintype_card_le_finrank
  have upper : Module.finrank ℚ W ≤ m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ m
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa only [Fintype.card_fin] using Fintype.card_range_le R
  exact lower.trans upper

set_option maxHeartbeats 1000000 in
theorem monotone_bound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ φ : PEqualNP.MetaComplexity.DMFormula n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ → (∀ x : Fin n → Bool, φ.eval x = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ u w : Fin n, G.Adj u w → u ∈ T ∨ w ∈ T) ∧ G.edgeFinset.card + T.card ≤ φ.leaves := by
  intro n G _ triangle square φ monotone evaluates
  classical
  obtain ⟨X, Y, label, partitions, labels⟩ := cover531_formulaRectangles φ monotone
  let E := {e : Sym2 (Fin n) // e ∈ G.edgeFinset}
  have endpoints (e : E) : ∃ u v : Fin n, G.Adj u v ∧ Sym2.mk u v = e.val := by
    have member : e.val ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.property
    revert member
    refine Sym2.inductionOn e.val ?_
    intro u v member
    exact ⟨u, v, member, rfl⟩
  choose a b adjacent represented using endpoints
  let row (e : E) (v : Fin n) : Bool := decide (v = a e ∨ v = b e)
  let starColumn (v w : Fin n) : Bool := decide (G.Adj v w)
  let edgeColumn (e : E) (w : Fin n) : Bool :=
    decide ((G.Adj (a e) w ∨ G.Adj (b e) w) ∧ w ≠ a e ∧ w ≠ b e)
  have rowPositive (e : E) : φ.eval (row e) = true := by
    rw [evaluates]
    exact decide_eq_true ⟨a e, b e, adjacent e, by simp [row], by simp [row]⟩
  have starNegative (v : Fin n) : φ.eval (starColumn v) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_starIndependent G triangle v u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  have edgeNegative (e : E) : φ.eval (edgeColumn e) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_pairIndependent G triangle square (a e) (b e) (adjacent e) u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  let route (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) : Fin φ.leaves :=
    Classical.choose (partitions (row e) y (rowPositive e) hy)
  have routeMem (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      X (route e y hy) (row e) ∧ Y (route e y hy) y :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).1
  have routeUnique (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (i : Fin φ.leaves) (hi : X i (row e) ∧ Y i y) : i = route e y hy :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).2 i hi
  let selected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) := label (route e y hy)
  have labelProperties (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      (selected e y hy = a e ∨ selected e y hy = b e) ∧ y (selected e y hy) = false := by
    have result := labels (route e y hy) (row e) y (rowPositive e) hy
      (routeMem e y hy).1 (routeMem e y hy).2
    exact ⟨of_decide_eq_true result.1, result.2⟩
  have leftSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (b e) = true) : selected e y hy = a e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · exact chosen
    · simp [chosen, opposite] at missing
  have rightSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (a e) = true) : selected e y hy = b e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · simp [chosen, opposite] at missing
    · exact chosen
  let chosen (e : E) := selected e (edgeColumn e) (edgeNegative e)
  let reject (e : E) := if chosen e = a e then b e else a e
  have chosenEnd (e : E) : chosen e = a e ∨ chosen e = b e :=
    (labelProperties e (edgeColumn e) (edgeNegative e)).1
  have rejectEnd (e : E) : a e = reject e ∨ b e = reject e := by
    dsimp only [reject]
    split <;> simp
  have differentEnd (e : E) : chosen e ≠ reject e := by
    have distinct := (adjacent e).ne
    rcases chosenEnd e with left | right
    · simp [reject, left, distinct]
    · simp [reject, right, distinct.symm]
  let R (i : Fin φ.leaves) (p : Fin n × E) : ℚ :=
    if p.1 = label i ∧ X i (row p.2) then 1 else 0
  let col (v : Fin n) (y : Fin n → Bool) : Fin n × E → ℚ :=
    Finset.univ.sum fun i : Fin φ.leaves => if Y i y ∧ label i = v then R i else 0
  let span := Submodule.span ℚ (Set.range R)
  have colInSpan (v : Fin n) (y : Fin n → Bool) : col v y ∈ span := by
    apply Submodule.sum_mem
    intro i _
    split
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact span.zero_mem
  have colValue (v : Fin n) (y : Fin n → Bool) (hy : φ.eval y = false) (p : Fin n × E) :
      col v y p = if p.1 = v ∧ selected p.2 y hy = v then 1 else 0 := by
    simp only [col, Finset.sum_apply]
    rw [Finset.sum_eq_single (route p.2 y hy)]
    · by_cases same : label (route p.2 y hy) = v
      · simp [R, selected, same, (routeMem p.2 y hy).1, (routeMem p.2 y hy).2]
      · simp [selected, same]
    · intro i _ other
      by_cases inColumn : Y i y ∧ label i = v
      · have noRow : ¬ X i (row p.2) := fun hx => other (routeUnique p.2 y hy i ⟨hx, inColumn.1⟩)
        simp [inColumn, R, noRow]
      · simp [inColumn]
    · simp
  have columnOpposite (e : E) (v w : Fin n) (hv : a e = v ∨ b e = v)
      (edge : G.Adj v w) (other : Sym2.mk v w ≠ e.val) : edgeColumn e w = true := by
    rcases hv with rfl | rfl
    · have notLeft : w ≠ a e := edge.ne.symm
      have notRight : w ≠ b e := by
        intro equal
        apply other
        rw [equal]
        exact represented e
      exact decide_eq_true ⟨Or.inl edge, notLeft, notRight⟩
    · have notRight : w ≠ b e := edge.ne.symm
      have notLeft : w ≠ a e := by
        intro equal
        apply other
        rw [equal]
        exact Sym2.eq_swap.trans (represented e)
      exact decide_eq_true ⟨Or.inr edge, notLeft, notRight⟩
  have starSelected (v : Fin n) (e : E) :
      selected e (starColumn v) (starNegative v) = v ↔ a e = v ∨ b e = v := by
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e (starColumn v) (starNegative v)).1
    · rintro (rfl | rfl)
      · exact leftSelected e (starColumn (a e)) (starNegative (a e)) (decide_eq_true (adjacent e))
      · exact rightSelected e (starColumn (b e)) (starNegative (b e)) (decide_eq_true (adjacent e).symm)
  have otherSelected (e e' : E) (different : e' ≠ e) (v : Fin n) (hv : a e = v ∨ b e = v) :
      selected e' (edgeColumn e) (edgeNegative e) = v ↔ a e' = v ∨ b e' = v := by
    have diffRep : e'.val ≠ e.val := fun equals => different (Subtype.ext equals)
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e' (edgeColumn e) (edgeNegative e)).1
    · rintro (rfl | rfl)
      · exact leftSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e') (by simpa [represented e'] using diffRep))
      · have notReversed : Sym2.mk (b e') (a e') ≠ e.val := by
          rw [Sym2.eq_swap, represented e']
          exact diffRep
        exact rightSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e').symm notReversed)
  let T : Finset (Fin n) := Finset.univ.image chosen
  have starInSpan (v : Fin n) :
      (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) ∈ span := by
    have equals : col v (starColumn v) =
        (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) := by
      funext p
      simp only [colValue v _ (starNegative v), starSelected]
    rw [← equals]
    exact colInSpan v (starColumn v)
  have units (e : E) : Pi.single (reject e, e) (1 : ℚ) ∈ span := by
    let v := reject e
    have equals : col v (starColumn v) - col v (edgeColumn e) = Pi.single (v, e) (1 : ℚ) := by
      funext p
      rcases p with ⟨w, e'⟩
      change col v (starColumn v) (w, e') - col v (edgeColumn e) (w, e') = (Pi.single (v, e) 1 : Fin n × E → ℚ) (w, e')
      simp only [colValue v _ (starNegative v), colValue v _ (edgeNegative e), starSelected]
      by_cases first : w = v
      · subst w
        by_cases second : e' = e
        · subst e'
          have miss : selected e (edgeColumn e) (edgeNegative e) ≠ v := differentEnd e
          simp [rejectEnd e, miss, v]
        · simp only [otherSelected e e' second v (rejectEnd e)]
          simp [second]
      · simp [first]
    rw [← equals]
    exact span.sub_mem (colInSpan v (starColumn v)) (colInSpan v (edgeColumn e))
  have anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v) := by
    intro v hv
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hv
    rcases chosenEnd e with first | second
    · exact ⟨e, differentEnd e, Or.inl first.symm⟩
    · exact ⟨e, differentEnd e, Or.inr second.symm⟩
  refine ⟨T, ?_, ?_⟩
  · intro u w edge
    let e : E := ⟨Sym2.mk u w, SimpleGraph.mem_edgeFinset.mpr edge⟩
    have inCover : chosen e ∈ T := Finset.mem_image_of_mem chosen (Finset.mem_univ e)
    have pair : Sym2.mk (a e) (b e) = Sym2.mk u w := represented e
    rcases Sym2.eq_iff.mp pair with ⟨left, right⟩ | ⟨left, right⟩
    · rcases chosenEnd e with first | second
      · exact Or.inl ((first.trans left) ▸ inCover)
      · exact Or.inr ((second.trans right) ▸ inCover)
    · rcases chosenEnd e with first | second
      · exact Or.inr ((first.trans left) ▸ inCover)
      · exact Or.inl ((second.trans right) ▸ inCover)
  · have bound := cover531_rank a b reject T R anchor units (fun v _ => starInSpan v)
    have count : Fintype.card E = G.edgeFinset.card := Fintype.card_coe _
    rwa [count] at bound

abbrev Form := DMFormula 9
abbrev M := BitVec 8

def F (x : Fin 9 → Bool) : Bool :=
  ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))

def vars : Form → List (Fin 9)
  | .lit i _ => [i]
  | .and a b | .or a b => vars a ++ vars b

def bitop (o : Bool) (x y : M) := if o then x ||| y else x &&& y
def mix (o : Bool) (a b : List M) : List M :=
  (a.flatMap fun x => b.map (bitop o x)).eraseDups
def constants : List M := [0,255]
def col (j : Fin 3) : M := if j=0 then 170 else if j=1 then 204 else 240

def names (f : Fin 9 → Option (Fin 3)) (t : Form) := (vars t).filterMap f

def pool (f : Fin 9 → Option (Fin 3)) : Form → List M
  | .lit i s => match f i with
    | none => constants
    | some j => (if s then col j else ~~~(col j)) :: constants
  | .and a b => mix false (pool f a) (pool f b)
  | .or a b => mix true (pool f a) (pool f b)

lemma in_mix (o : Bool) {x y : M} {A B : List M} (hx : x ∈ A) (hy : y ∈ B) :
    bitop o x y ∈ mix o A B :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,rfl⟩⟩)

lemma mix_mono (o : Bool) {A B U V : List M} (a : A ⊆ U) (b : B ⊆ V) :
    mix o A B ⊆ mix o U V := by
  intro z hz
  obtain ⟨x,hx,w⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hz)
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp w
  exact in_mix o (a hx) (b hy)

lemma includes (f : Fin 9 → Option (Fin 3)) (t : Form) : 0 ∈ pool f t ∧ 255 ∈ pool f t := by
  induction t with
  | lit i s => cases h : f i <;> simp [pool,h,constants]
  | and a b ha hb => exact ⟨in_mix false ha.1 hb.1,in_mix false ha.2 hb.2⟩
  | or a b ha hb => exact ⟨in_mix true ha.1 hb.1,in_mix true ha.2 hb.2⟩

lemma collapse (o : Bool) (A B : List M) (ha : A ⊆ constants) (hb : 0 ∈ B ∧ 255 ∈ B) :
    mix o A B ⊆ B ∧ mix o B A ⊆ B := by
  have act (x y : M) (hx : x ∈ A) (hy : y ∈ B) :
      bitop o x y ∈ B ∧ bitop o y x ∈ B := by
    have hz := ha hx
    simp [constants] at hz
    have left (u v : M) (h : u=v) (hv : v∈B) : u∈B := (congrArg (fun z => z∈B) h).mpr hv
    rcases hz with hz | hz
    · subst x
      cases o
      · exact ⟨left _ 0 BitVec.zero_and hb.1,left _ 0 BitVec.and_zero hb.1⟩
      · exact ⟨left _ y BitVec.zero_or hy,left _ y BitVec.or_zero hy⟩
    · subst x
      cases o
      · exact ⟨left _ y BitVec.allOnes_and hy,left _ y BitVec.and_allOnes hy⟩
      · exact ⟨left _ 255 BitVec.allOnes_or hb.2,left _ 255 BitVec.or_allOnes hb.2⟩
  constructor <;> intro z hz
  all_goals obtain ⟨x,hx,h⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hz)
  all_goals obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h
  · exact (act x y hx hy).1
  · exact (act y x hy hx).2

lemma emptyPool (f : Fin 9 → Option (Fin 3)) (t : Form) (h : names f t = []) :
    pool f t ⊆ constants := by
  induction t with
  | lit i s => cases he : f i <;> simp_all [names,vars,pool]
  | and a b ia ib | or a b ia ib =>
    have hh : names f a = [] ∧ names f b = [] := by simpa [names,vars] using h
    first | exact fun ⦃_⦄ hz => (collapse false constants constants (fun ⦃_⦄ z => z) (by decide)).1 (mix_mono false (ia hh.1) (ib hh.2) hz)
          | exact fun ⦃_⦄ hz => (collapse true constants constants (fun ⦃_⦄ z => z) (by decide)).1 (mix_mono true (ia hh.1) (ib hh.2) hz)

def base : List (Fin 3) → List (List M)
  | [] => [constants]
  | [i] => [col i :: constants, (~~~(col i)) :: constants]
  | _ => []

def forms : Nat → List (Fin 3) → List (List M)
  | 0, xs => base xs
  | k+1, xs =>
    if xs.length ≤ 1 then base xs else
      (List.range (xs.length-1)).flatMap fun d =>
        (forms k (xs.take (d+1))).flatMap fun a =>
          (forms k (xs.drop (d+1))).flatMap fun b => [mix false a b, mix true a b]

lemma base_ok (k : ℕ) (xs : List (Fin 3)) (h : xs.length ≤ 1) : forms k xs = base xs := by
  cases k <;> simp [forms,h]

-- Project the tree to the monitored literals. A subtree without monitored leaves
-- can only transmit its sibling or a constant, so it needs no split in the enumeration.
lemma bounded (f : Fin 9 → Option (Fin 3)) (t : Form) (k : ℕ) (h : (names f t).length ≤ k) :
    ∃ P ∈ forms k (names f t), pool f t ⊆ P := by
  have branch (o : Bool) (a b : Form)
      (ia : ∀ j, (names f a).length ≤ j → ∃ P ∈ forms j (names f a), pool f a ⊆ P)
      (ib : ∀ j, (names f b).length ≤ j → ∃ P ∈ forms j (names f b), pool f b ⊆ P)
      (k : ℕ) (hk : (names f a).length + (names f b).length ≤ k) :
      ∃ P ∈ forms k (names f a ++ names f b), mix o (pool f a) (pool f b) ⊆ P := by
    by_cases ea : names f a = []
    · obtain ⟨P,hP,sub⟩ := ib k (by omega)
      exact ⟨P,by simpa [ea] using hP,fun ⦃_⦄ hz => sub ((collapse o _ _ (emptyPool f a ea) (includes f b)).1 hz)⟩
    by_cases eb : names f b = []
    · obtain ⟨P,hP,sub⟩ := ia k (by omega)
      exact ⟨P,by simpa [eb] using hP,fun ⦃_⦄ hz => sub ((collapse o _ _ (emptyPool f b eb) (includes f a)).2 hz)⟩
    have al := List.length_pos_iff.mpr ea
    have bl := List.length_pos_iff.mpr eb
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨P,hp,sa⟩ := ia k (by omega)
      obtain ⟨Q,hq,sb⟩ := ib k (by omega)
      refine ⟨mix o P Q,?_,mix_mono o sa sb⟩
      simp only [forms,List.length_append,show ¬ ((names f a).length + (names f b).length ≤ 1) by omega,ite_false]
      refine List.mem_flatMap.mpr ⟨(names f a).length-1,List.mem_range.mpr (by omega),?_⟩
      rw [show (names f a).length-1+1=(names f a).length by omega,List.take_left,List.drop_left]
      exact List.mem_flatMap.mpr ⟨P,hp,List.mem_flatMap.mpr ⟨Q,hq,by cases o <;> simp⟩⟩
  induction t generalizing k with
  | lit i s =>
    cases e : f i with
    | none =>
      have hn : names f (.lit i s) = [] := by simp [names,vars,e]
      rw [hn,base_ok k [] (by decide)]
      exact ⟨_,List.mem_cons_self,by simp [pool,e]⟩
    | some j =>
      have hn : names f (.lit i s) = [j] := by simp [names,vars,e]
      rw [hn,base_ok k [j] (by simp)]
      cases s <;> simp [base,pool,e]
  | and a b ia ib | or a b ia ib =>
    first | change ∃ P ∈ forms k (names f (.and a b)), mix false (pool f a) (pool f b) ⊆ P
          | change ∃ P ∈ forms k (names f (.or a b)), mix true (pool f a) (pool f b) ⊆ P
    simpa only [names,vars,List.filterMap_append] using branch _ a b ia ib k (by simpa [names,vars] using h)

def maskedEval (w : Fin 9 → M) : Form → M
  | .lit i s => if s then w i else ~~~(w i)
  | .and a b => maskedEval w a &&& maskedEval w b
  | .or a b => maskedEval w a ||| maskedEval w b

lemma semantic (f : Fin 9 → Option (Fin 3)) (w : Fin 9 → M)
    (hw : ∀ i, match f i with | none => w i = 0 ∨ w i = 255 | some j => w i = col j)
    (t : Form) : maskedEval w t ∈ pool f t := by
  induction t with
  | lit i s =>
    have h := hw i
    cases e : f i with
    | none =>
      rw [e] at h
      rcases h with h | h <;> cases s <;> simp [maskedEval,pool,e,h,constants]
    | some j =>
      rw [e] at h
      cases s <;> simp [maskedEval,pool,e,h]
  | and a b ia ib => exact in_mix false ia ib
  | or a b ia ib => exact in_mix true ia ib

lemma masked_bits (w : Fin 9 → M) (t : Form) (j : ℕ) (hj : j<8) :
    (maskedEval w t).getLsbD j = t.eval (fun i => (w i).getLsbD j) := by
  induction t with
  | lit i s => cases s <;> simp [maskedEval,DMFormula.eval,hj]
  | and a b ia ib | or a b ia ib => simp [maskedEval,DMFormula.eval,ia,ib]

def graphBits (w : Fin 9 → M) : M :=
  ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).foldr
    (fun e t => (w (Fin.ofNat 9 (e / 9)) &&& w (Fin.ofNat 9 (e % 9))) ||| t) 0

lemma computesBits (w : Fin 9 → M) (t : Form) (he : ∀ x, t.eval x = F x) :
    maskedEval w t = graphBits w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [masked_bits w t j hj,he]
  have aux (es : List ℕ) : (es.foldr (fun e (s : M) =>
      (w (Fin.ofNat 9 (e / 9)) &&& w (Fin.ofNat 9 (e % 9))) ||| s) 0).getLsbD j =
      (es.any (fun e => (w (Fin.ofNat 9 (e / 9))).getLsbD j && (w (Fin.ofNat 9 (e % 9))).getLsbD j)) := by
    induction es with
    | nil => simp
    | cons e es ih => simp only [List.foldr_cons,BitVec.getLsbD_or,BitVec.getLsbD_and,List.any_cons]; rw [ih]
  exact (aux _).symm

def select (a b : Fin 9) (c : Option (Fin 9)) (i : Fin 9) : Option (Fin 3) :=
  if i=a then some 0 else if i=b then some 1 else if some i=c then some 2 else none

def assignment (f : Fin 9 → Option (Fin 3)) (s : Nat) (i : Fin 9) : M :=
  match f i with
  | none => if s.testBit i.val then 255 else 0
  | some j => col j

lemma observed (t : Form) (he : ∀ x, t.eval x = F x) (f : Fin 9 → Option (Fin 3)) (s : ℕ) :
    graphBits (assignment f s) ∈ pool f t := by
  rw [← computesBits _ _ he]
  apply semantic
  intro i
  cases hi : f i <;> simp [assignment,hi]

def forbidden (xs : List (Fin 3)) (goals : List M) : Bool :=
  (forms xs.length xs).all (fun P => !(goals.all (fun g => P.contains g)))

lemma rule (t : Form) (f : Fin 9 → Option (Fin 3)) (budget : List (Fin 3)) (G : List M)
    (check : ∀ l ∈ budget.sublists, ∀ s ∈ l.permutations', forbidden s G = true)
    (obs : ∀ g ∈ G, g ∈ pool f t) : ¬ (names f t).Subperm budget := by
  rintro ⟨l,perm,sub⟩
  have checked := check l (List.mem_sublists.mpr sub) (names f t) (List.mem_permutations'.mpr perm.symm)
  obtain ⟨P,hP,inc⟩ := bounded f t _ (Nat.le_refl _)
  have yes : G.all (fun g => P.contains g) = true :=
    List.all_eq_true.mpr (fun g hg => List.contains_iff_mem.mpr (inc (obs g hg)))
  have no := List.all_eq_true.mp checked P hP
  change (!(G.all fun g => P.contains g)) = true at no
  rw [yes] at no
  contradiction

def pairB : List (Fin 3) := [0,1]
def tripleB : List (Fin 3) := [0,1,2,2]
def pairG : List M := [136,238]
def tripleG : List M := [224,234,254]

lemma count_select (t : Form) (f : Fin 9 → Option (Fin 3)) (j : Fin 3) (i : Fin 9)
    (e : ∀ a, f a = some j ↔ a=i) : (names f t).count j = (vars t).count i := by
  dsimp [names]
  induction vars t with
  | nil => rfl
  | cons a l ih =>
    cases h : f a with
    | none =>
      have ne : a ≠ i := fun z => by simpa [h] using (e a).mpr z
      simp [h,ne,ih]
    | some k =>
      by_cases eq : k=j
      · subst k
        have z := (e a).mp h
        subst a
        simp [h,ih]
      · have ne : a ≠ i := fun z => eq (Option.some.inj (h.symm.trans ((e a).mpr z)))
        simp [h,ne,eq,ih]

lemma count_missing (t : Form) (f : Fin 9 → Option (Fin 3)) (j : Fin 3)
    (e : ∀ a, f a ≠ some j) : (names f t).count j = 0 := by
  dsimp [names]
  induction vars t with
  | nil => rfl
  | cons a l ih =>
    cases h : f a with
    | none => simp [h,ih]
    | some k =>
      have ne : k ≠ j := fun z => e a (z ▸ h)
      simp [h,ih,ne]

def tally (t : Form) (i : Fin 9) : ℕ := (vars t).count i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma pairRule (t : Form) (he : ∀ x, t.eval x = F x) (a b : Fin 9) (ne : a ≠ b)
    (s u : ℕ) (w1 : graphBits (assignment (select a b none) s) = 136)
    (w2 : graphBits (assignment (select a b none) u) = 238)
    (cert : ∀ l ∈ pairB.sublists, ∀ v ∈ l.permutations', forbidden v pairG = true) :
    1 < tally t a ∨ 1 < tally t b := by
  by_contra! h
  apply rule t (select a b none) pairB pairG cert (by
    intro g hg
    simp [pairG] at hg
    rcases hg with rfl | rfl
    · exact (congrArg (fun z : M => z ∈ pool (select a b none) t) w1).mp (observed t he _ s)
    · exact (congrArg (fun z : M => z ∈ pool (select a b none) t) w2).mp (observed t he _ u))
  apply List.subperm_iff_count.mpr
  intro j
  have cuts : ∀ (a b : Fin 9), a ≠ b → ∀ i,
      (select a b none i=some 0 ↔ i=a) ∧ (select a b none i=some 1 ↔ i=b) ∧ select a b none i≠some 2 := by decide +kernel
  fin_cases j
  · exact (count_select t _ 0 a (fun i => (cuts a b ne i).1)).le.trans h.1
  · exact (count_select t _ 1 b (fun i => (cuts a b ne i).2.1)).le.trans h.2
  · exact (count_missing t _ 2 (fun i => (cuts a b ne i).2.2)).le.trans (Nat.zero_le _)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma tripleRule (t : Form) (he : ∀ x, t.eval x = F x) (a b c : Fin 9) (ab : a ≠ b)
    (ac : a ≠ c) (bc : b ≠ c) (s u v : ℕ)
    (w1 : graphBits (assignment (select a b (some c)) s) = 224)
    (w2 : graphBits (assignment (select a b (some c)) u) = 234)
    (w3 : graphBits (assignment (select a b (some c)) v) = 254)
    (cert : ∀ l ∈ tripleB.sublists, ∀ w ∈ l.permutations', forbidden w tripleG = true) :
    1 < tally t a ∨ 1 < tally t b ∨ 2 < tally t c := by
  by_contra! h
  apply rule t (select a b (some c)) tripleB tripleG cert (by
    intro g hg
    simp [tripleG] at hg
    rcases hg with rfl | rfl | rfl
    · exact (congrArg (fun z : M => z ∈ pool (select a b (some c)) t) w1).mp (observed t he _ s)
    · exact (congrArg (fun z : M => z ∈ pool (select a b (some c)) t) w2).mp (observed t he _ u)
    · exact (congrArg (fun z : M => z ∈ pool (select a b (some c)) t) w3).mp (observed t he _ v))
  apply List.subperm_iff_count.mpr
  intro j
  have cuts : ∀ (a b c : Fin 9), a ≠ b → a ≠ c → b ≠ c → ∀ i,
      (select a b (some c) i=some 0 ↔ i=a) ∧ (select a b (some c) i=some 1 ↔ i=b) ∧
      (select a b (some c) i=some 2 ↔ i=c) := by decide +kernel
  fin_cases j
  · exact (count_select t _ 0 a (fun i => (cuts a b c ab ac bc i).1)).le.trans h.1
  · exact (count_select t _ 1 b (fun i => (cuts a b c ab ac bc i).2.1)).le.trans h.2.1
  · exact (count_select t _ 2 c (fun i => (cuts a b c ab ac bc i).2.2)).le.trans h.2.2

lemma vars_size (t : Form) : (vars t).length = t.leaves := by
  induction t <;> simp_all [vars,DMFormula.leaves]

lemma vars_congr (t : Form) (x y : Fin 9 → Bool) (h : ∀ i ∈ vars t, x i=y i) :
    t.eval x=t.eval y := by
  induction t with
  | lit i s => have hi := h i (by simp [vars]); simp [DMFormula.eval,hi]
  | and a b ia ib | or a b ia ib =>
    have ha := ia (fun i hi => h i (by simp [vars,hi]))
    have hb := ib (fun i hi => h i (by simp [vars,hi]))
    simp [DMFormula.eval,ha,hb]

lemma used (t : Form) (he : ∀ x, t.eval x=F x) (i : Fin 9) : 0 < tally t i := by
  have witness : ∀ v : Fin 9, ∃ w : Fin 9, w ≠ v ∧
      F (fun i => decide (i=v ∨ i=w)) ≠ F (fun i => decide (i=w)) := by decide +kernel
  obtain ⟨w,_,neq⟩ := witness i
  by_contra! zero
  have unused : i ∉ vars t := by
    intro hi
    have pos := List.count_pos_iff.mpr hi
    change (vars t).count i ≤ 0 at zero
    omega
  apply neq
  rw [← he,← he]
  apply vars_congr
  intro j hj
  have ne : j≠i := fun eq => unused (eq ▸ hj)
  simp [ne]

lemma tally_sum (t : Form) : ∑ i : Fin 9, tally t i = t.leaves := by
  rw [← vars_size]
  unfold tally
  induction vars t with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons,List.length_cons,Finset.sum_add_distrib]
    simp [ih,add_comm]

-- Small truth tables are bit vectors: row 0 is the least significant bit.
-- The two-variable restrictions require both AND and OR. Each selected
-- three-variable restriction realizes all three masks in tripleG.
def pairWords : List (List (Fin 3)) := [[],[0],[1],[0,1],[1,0]]
lemma pairCert : ∀ l ∈ pairB.sublists, ∀ v ∈ l.permutations', forbidden v pairG = true := by
  have cover : pairB.sublists.all (fun l => l.permutations'.all (fun w => pairWords.contains w)) = true := by decide +kernel
  intro l hl v hv
  have hit := List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp cover l hl) v hv)
  simp only [pairWords,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def tripleWords : List (List (Fin 3)) := [[],[0],[1],[2],[0,1],[0,2],[1,0],[1,2],[2,0],[2,1],[2,2],[0,1,2],[0,2,1],[0,2,2],[1,0,2],[1,2,0],[1,2,2],[2,0,1],[2,0,2],[2,1,0],[2,1,2],[2,2,0],[2,2,1],[0,1,2,2],[0,2,1,2],[0,2,2,1],[1,0,2,2],[1,2,0,2],[1,2,2,0],[2,0,1,2],[2,0,2,1],[2,1,0,2],[2,1,2,0],[2,2,0,1],[2,2,1,0]]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma tripleCert : ∀ l ∈ tripleB.sublists, ∀ v ∈ l.permutations', forbidden v tripleG = true := by
  have cover : tripleB.sublists.all (fun l => l.permutations'.all (fun w => tripleWords.contains w)) = true := by decide +kernel
  intro l hl v hv
  have hit := List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp cover l hl) v hv)
  simp only [tripleWords,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma profile (t : Form) (he : ∀ x, t.eval x = F x) (small : t.leaves ≤ 15) : t.leaves = 15 ∧ tally t 0 = 2 := by
  have p0 := used t he 0
  have p1 := used t he 1
  have p2 := used t he 2
  have p3 := used t he 3
  have p4 := used t he 4
  have p5 := used t he 5
  have p6 := used t he 6
  have p7 := used t he 7
  have p8 := used t he 8
  have r0 := pairRule t he 0 1 (by decide) 0 20 (by decide +kernel) (by decide +kernel) pairCert
  have r1 := pairRule t he 2 3 (by decide) 0 18 (by decide +kernel) (by decide +kernel) pairCert
  have r2 := pairRule t he 5 7 (by decide) 0 5 (by decide +kernel) (by decide +kernel) pairCert
  have r3 := pairRule t he 6 8 (by decide) 0 10 (by decide +kernel) (by decide +kernel) pairCert
  have r4 := pairRule t he 0 4 (by decide) 0 10 (by decide +kernel) (by decide +kernel) pairCert
  have r5 := tripleRule t he 1 4 0 (by decide) (by decide) (by decide) 0 4 104 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have r6 := pairRule t he 1 2 (by decide) 0 9 (by decide +kernel) (by decide +kernel) pairCert
  have r7 := pairRule t he 3 4 (by decide) 0 5 (by decide +kernel) (by decide +kernel) pairCert
  have r8 := pairRule t he 5 8 (by decide) 0 9 (by decide +kernel) (by decide +kernel) pairCert
  have r9 := pairRule t he 2 7 (by decide) 0 34 (by decide +kernel) (by decide +kernel) pairCert
  have r10 := tripleRule t he 5 6 8 (by decide) (by decide) (by decide) 0 1 138 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have r11 := tripleRule t he 3 7 2 (by decide) (by decide) (by decide) 0 16 50 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have r12 := tripleRule t he 0 6 1 (by decide) (by decide) (by decide) 0 16 276 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have r13 := tripleRule t he 7 8 5 (by decide) (by decide) (by decide) 0 4 69 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have r14 := pairRule t he 1 6 (by decide) 0 257 (by decide +kernel) (by decide +kernel) pairCert
  have r15 := tripleRule t he 2 4 3 (by decide) (by decide) (by decide) 0 2 385 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have r16 := pairRule t he 0 5 (by decide) 0 130 (by decide +kernel) (by decide +kernel) pairCert
  have r17 := pairRule t he 3 8 (by decide) 0 36 (by decide +kernel) (by decide +kernel) pairCert
  have r18 := tripleRule t he 0 2 1 (by decide) (by decide) (by decide) 0 16 104 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have r19 := tripleRule t he 1 5 0 (by decide) (by decide) (by decide) 0 4 208 (by decide +kernel) (by decide +kernel) (by decide +kernel) tripleCert
  have total := tally_sum t
  simp only [Fin.sum_univ_succ,Fin.succ_zero_eq_one] at total
  change tally t 0 + (tally t 1 + (tally t 2 + (tally t 3 + (tally t 4 + (tally t 5 + (tally t 6 + (tally t 7 + (tally t 8 + 0)))))))) = t.leaves at total
  omega

def clean : Form → Prop
  | .lit i s => s = true ∨ i = 0
  | .and a b | .or a b => clean a ∧ clean b

def positive : Form → Prop
  | .lit _ s => s = true
  | .and a b | .or a b => positive a ∧ positive b

def flip : Form → Form
  | .lit i s => .lit i (!s)
  | .and a b => .or (flip a) (flip b)
  | .or a b => .and (flip a) (flip b)

abbrev Expr := Sum Bool Form
def val (e : Expr) (x : Fin 9 → Bool) : Bool := e.elim id (fun t => t.eval x)
def sz (e : Expr) : ℕ := e.elim (fun _ => 0) DMFormula.leaves
def proper (Q : Form → Prop) (e : Expr) : Prop := e.elim (fun _ => True) Q
def boolOp (o a b : Bool) : Bool := if o then a || b else a && b
def join (o : Bool) (a b : Expr) : Expr :=
  match a,b with
  | .inl c,v | v,.inl c => if c=o then .inl c else v
  | .inr t,.inr u => .inr (if o then .or t u else .and t u)

lemma join_val (o : Bool) (a b : Expr) (x) : val (join o a b) x = boolOp o (val a x) (val b x) := by
  cases a with
  | inl c => cases o <;> cases c <;> cases b <;> simp [join,val,boolOp]
  | inr t => cases b with
    | inl c => cases o <;> cases c <;> simp [join,val,boolOp]
    | inr u => cases o <;> rfl

lemma join_size (o : Bool) (a b : Expr) : sz (join o a b) ≤ sz a + sz b := by
  cases a with
  | inl c => cases o <;> cases c <;> cases b <;> simp [join,sz]
  | inr t => cases b with
    | inl c => cases o <;> cases c <;> simp [join,sz]
    | inr u => cases o <;> rfl

lemma join_proper (Q : Form → Prop) (ha : ∀ a b, Q a → Q b → Q (.and a b))
    (ho : ∀ a b, Q a → Q b → Q (.or a b)) (o : Bool) (a b : Expr)
    (p : proper Q a) (q : proper Q b) : proper Q (join o a b) := by
  cases a with
  | inl c => cases o <;> cases c <;> cases b <;> simp_all [join,proper]
  | inr t => cases b with
    | inl c => cases o <;> cases c <;> simp_all [join,proper]
    | inr u => cases o; exact ha _ _ p q; exact ho _ _ p q

def invert : Expr → Expr
  | .inl b => .inl (!b)
  | .inr t => .inr (flip t)

lemma flip_prop (t : Form) (x) : (flip t).eval x = !t.eval x ∧ (flip t).leaves=t.leaves := by
  induction t with
  | lit i s => cases s <;> simp [flip,DMFormula.eval,DMFormula.leaves]
  | and a b ia ib | or a b ia ib => simp_all [flip,DMFormula.eval,DMFormula.leaves]

lemma inv_val (e : Expr) (x) : val (invert e) x = !val e x := by
  cases e with
  | inl c => rfl
  | inr t => exact (flip_prop t x).1

lemma inv_sz (e : Expr) : sz (invert e) = sz e := by
  cases e with
  | inl c => rfl
  | inr t => exact (flip_prop t (fun _ => false)).2

-- Two independent placeholders for the positive and negative occurrences at vertex zero.
def plug (p q : Bool) (x : Fin 9 → Bool) : Form → Bool
  | .lit i s => if i=0 then (if s then p else q) else (if s then x i else !(x i))
  | .and a b => plug p q x a && plug p q x b
  | .or a b => plug p q x a || plug p q x b

def Upper (t : Form) := ∀ x, plug true true x t = (plug true false x t || plug false true x t)
def Lower (t : Form) := ∀ x, plug false false x t = (plug true false x t && plug false true x t)
def Fixed (t : Form) := ∀ x p q, plug p q x t = plug false false x t

lemma zero_fixed (t : Form) (h : tally t 0=0) : Fixed t := by
  induction t with
  | lit i s =>
    have ne : i ≠ 0 := by intro hi; subst i; simp [tally,vars] at h
    intro x p q; simp [plug,ne]
  | and a b ia ib | or a b ia ib =>
    change (vars a ++ vars b).count 0 = 0 at h
    rw [List.count_append,Nat.add_eq_zero_iff] at h
    intro x p q; simp [plug,ia h.1 x p q,ib h.2 x p q]

-- Holding either input of a binary gate fixed preserves either envelope identity.
lemma up_fixed : ∀ o u v k : Bool, boolOp o (u || v) k =
    (boolOp o u k || boolOp o v k) := by decide
lemma lo_fixed : ∀ o u v k : Bool, boolOp o (u && v) k =
    (boolOp o u k && boolOp o v k) := by decide
lemma comm_op : ∀ o u v : Bool, boolOp o u v = boolOp o v u := by decide

def node (o : Bool) (a b : Form) : Form := if o then .or a b else .and a b
lemma plug_node (o p q : Bool) (x) (a b : Form) :
    plug p q x (node o a b) = boolOp o (plug p q x a) (plug p q x b) := by cases o <;> rfl

lemma lift_up (o : Bool) (a b : Form) (h : Upper a ∧ Fixed b ∨ Fixed a ∧ Upper b) : Upper (node o a b) := by
  intro x
  simp only [plug_node]
  rcases h with ⟨u,f⟩ | ⟨f,u⟩
  · simp only [f x, u x,up_fixed]
  · simp only [f x,u x]; rw [comm_op o _ (_ || _),up_fixed,comm_op o (plug true false x b),comm_op o (plug false true x b)]

lemma lift_lo (o : Bool) (a b : Form) (h : Lower a ∧ Fixed b ∨ Fixed a ∧ Lower b) : Lower (node o a b) := by
  intro x
  simp only [plug_node]
  rcases h with ⟨u,f⟩ | ⟨f,u⟩
  · simp only [f x,u x,lo_fixed]
  · simp only [f x,u x]; rw [comm_op o _ (_ && _),lo_fixed,comm_op o (plug true false x b),comm_op o (plug false true x b)]

lemma envelopes (t : Form) :
    (tally t 0 ≤ 1 → Upper t ∧ Lower t) ∧ (tally t 0 ≤ 2 → Upper t ∨ Lower t) := by
  have step (o : Bool) (a b : Form)
      (ia : (tally a 0 ≤ 1 → Upper a ∧ Lower a) ∧ (tally a 0 ≤ 2 → Upper a ∨ Lower a))
      (ib : (tally b 0 ≤ 1 → Upper b ∧ Lower b) ∧ (tally b 0 ≤ 2 → Upper b ∨ Lower b)) :
      (tally a 0 + tally b 0 ≤ 1 → Upper (node o a b) ∧ Lower (node o a b)) ∧
      (tally a 0 + tally b 0 ≤ 2 → Upper (node o a b) ∨ Lower (node o a b)) := by
    constructor
    · intro h
      by_cases z : tally a 0=0
      · exact ⟨lift_up _ _ _ (.inr ⟨zero_fixed a z,(ib.1 (by omega)).1⟩),lift_lo _ _ _ (.inr ⟨zero_fixed a z,(ib.1 (by omega)).2⟩)⟩
      · have f := zero_fixed b (by omega)
        exact ⟨lift_up _ _ _ (.inl ⟨(ia.1 (by omega)).1,f⟩),lift_lo _ _ _ (.inl ⟨(ia.1 (by omega)).2,f⟩)⟩
    · intro h
      by_cases z : tally a 0=0
      · have f := zero_fixed a z
        exact (ib.2 (by omega)).imp (fun u => lift_up _ _ _ (.inr ⟨f,u⟩)) (fun u => lift_lo _ _ _ (.inr ⟨f,u⟩))
      by_cases w : tally b 0=0
      · have f := zero_fixed b w
        exact (ia.2 (by omega)).imp (fun u => lift_up _ _ _ (.inl ⟨u,f⟩)) (fun u => lift_lo _ _ _ (.inl ⟨u,f⟩))
      obtain ⟨ua,la⟩ := ia.1 (by omega)
      obtain ⟨ub,lb⟩ := ib.1 (by omega)
      cases o
      · right; intro x; simp only [plug_node,boolOp, Bool.false_eq_true,ite_false,la x,lb x]; ac_rfl
      · left; intro x; simp only [plug_node,boolOp,ite_true,ua x,ub x]; ac_rfl
  induction t with
  | lit i s =>
    have h : Upper (.lit i s) ∧ Lower (.lit i s) := by
      constructor <;> intro x <;> by_cases hi : i=0 <;> cases s <;> simp [plug,hi]
    exact ⟨fun _ => h,fun _ => .inl h.1⟩
  | and a b ia ib => simpa [tally,vars,node] using step false a b ia ib
  | or a b ia ib => simpa [tally,vars,node] using step true a b ia ib

def replace (q : Bool) : Form → Expr
  | .lit i s => if s then .inr (.lit i true) else .inl q
  | .and a b => join false (replace q a) (replace q b)
  | .or a b => join true (replace q a) (replace q b)

lemma replace_spec (q : Bool) (t : Form) (h : clean t) :
    proper positive (replace q t) ∧ sz (replace q t) ≤ t.leaves ∧
    ∀ x, val (replace q t) x = plug (x 0) q x t := by
  induction t with
  | lit i s =>
    cases s with
    | false => have hi : i=0 := h.resolve_left (by decide); simp [replace,sz,val,proper,plug,hi,DMFormula.leaves]
    | true => simp [replace,sz,val,proper,positive,plug,DMFormula.leaves,DMFormula.eval]; intro x hi; rw [hi]
  | and a b ia ib | or a b ia ib =>
    obtain ⟨pa,sa,va⟩ := ia h.1
    obtain ⟨pb,sb,vb⟩ := ib h.2
    refine ⟨join_proper positive (fun _ _ u v => ⟨u,v⟩) (fun _ _ u v => ⟨u,v⟩) _ _ _ pa pb, (join_size _ _ _).trans (Nat.add_le_add sa sb),?_⟩
    intro x; simp [replace,join_val,boolOp,plug,va,vb]

def update0 (x : Fin 9 → Bool) (p : Bool) (i : Fin 9) := if i=0 then p else x i

lemma plug_valid (t : Form) (x : Fin 9 → Bool) (p : Bool) :
    plug p (!p) x t = t.eval (update0 x p) := by
  induction t with
  | lit i s => cases s <;> by_cases hi : i=0 <;> simp [plug,DMFormula.eval,update0,hi]
  | and a b ia ib | or a b ia ib => simp [DMFormula.eval,plug,ia,ib]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma makePositive (t : Form) (h : clean t) (two : tally t 0 ≤ 2) (he : ∀ x, t.eval x=F x) :
    ∃ e : Expr, proper positive e ∧ sz e ≤ t.leaves ∧ ∀ x, val e x=F x := by
  have up (x : Fin 9 → Bool) : (plug true false x t || plug false true x t) = plug true false x t ∧
      (plug true false x t && plug false true x t) = plug false true x t := by
    have g : ∀ x : Fin 9 → Bool, (F (update0 x true) || F (update0 x false)) = F (update0 x true) ∧
        (F (update0 x true) && F (update0 x false)) = F (update0 x false) := by decide +kernel
    simpa only [← he,← plug_valid,Bool.not_true,Bool.not_false] using g x
  have same (x : Fin 9 → Bool) : update0 x (x 0) = x := by funext i; by_cases hi : i=0 <;> simp [update0,hi]
  have valid (x : Fin 9 → Bool) : plug (x 0) (!(x 0)) x t = F x := by rw [plug_valid,same,he]
  rcases (envelopes t).2 two with u | l
  · obtain ⟨p,s,v⟩ := replace_spec true t h
    refine ⟨_,p,s,fun x => ?_⟩
    rw [v,← valid x]
    cases eq : x 0 <;> simp [u x,(up x).1]
  · obtain ⟨p,s,v⟩ := replace_spec false t h
    refine ⟨_,p,s,fun x => ?_⟩
    rw [v,← valid x]
    cases eq : x 0 <;> simp [l x,(up x).2]

abbrev Wire := ℕ × Expr
def missing : Wire := (0,.inl false)
def Sound (w : Wire) := sz w.2 ≤ w.1+1 ∧ (sz w.2 = w.1+1 → proper clean w.2)
def gateExpr : GateOp → List Expr → Expr
  | .and, [] => .inl true
  | .not, [] => .inl true
  | .not, x::_ => invert x
  | .and, [x] | .or, [x] => x
  | .and, [x,y] => join false x y
  | .or, [x,y] => join true x y
  | _, _ => .inl false

-- Equality in the leaf budget leaves no room for an internal inversion.
def makeWire (op : GateOp) (l : List Wire) : Wire :=
  (1+(l.map Prod.fst).sum,gateExpr op (l.map Prod.snd))
def stepW (w : List Wire) (g : Gate) := w ++ [makeWire g.op (g.inputs.map fun i => w.getD i missing)]
def stepC (w : List ℕ) (g : Gate) := w ++ [1+(g.inputs.map fun i => w.getD i 0).sum]
def stepV (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma join_bound (o : Bool) (a b : Wire) (ha : Sound a) (hb : Sound b) : Sound (1+(a.1+b.1),join o a.2 b.2) := by
  obtain ⟨sa,ca⟩ := ha
  obtain ⟨sb,cb⟩ := hb
  have bound := join_size o a.2 b.2
  constructor
  · change sz (join o a.2 b.2) ≤ 1+(a.1+b.1)+1; omega
  · change sz (join o a.2 b.2) = 1+(a.1+b.1)+1 → proper clean (join o a.2 b.2)
    intro hit
    exact join_proper clean (fun _ _ p q => ⟨p,q⟩) (fun _ _ p q => ⟨p,q⟩) o _ _ (ca (by omega)) (cb (by omega))

def allowed (op : GateOp) := op = .and ∨ op = .or ∨ op = .not

lemma gate_ok (op : GateOp) (l : List Wire) (ok : allowed op) (arity : l.length ≤ 2)
    (unary : op = .not → l.length ≤ 1) (h : ∀ w ∈ l, Sound w) :
    Sound (makeWire op l) ∧ ∀ x, val (makeWire op l).2 x = op.eval (l.map fun w => val w.2 x) := by
  cases l with
  | nil => rcases ok with rfl | rfl | rfl <;> simp [Sound,makeWire,gateExpr,sz,proper,val,GateOp.eval]
  | cons a l =>
    have ha := h a List.mem_cons_self
    cases l with
    | nil =>
      have sa := ha.1
      rcases ok with rfl | rfl | rfl
      all_goals
        constructor
        · simp [Sound,makeWire,gateExpr,inv_sz] <;> omega
        · intro x; simp [makeWire,gateExpr,GateOp.eval,inv_val]
    | cons b l =>
      have hb := h b (by simp)
      cases l with
      | nil =>
        rcases ok with rfl | rfl | rfl
        · exact ⟨by simpa [makeWire,gateExpr] using join_bound false a b ha hb,fun x => by simp [makeWire,gateExpr,GateOp.eval,join_val,boolOp]⟩
        · exact ⟨by simpa [makeWire,gateExpr] using join_bound true a b ha hb,fun x => by simp [makeWire,gateExpr,GateOp.eval,join_val,boolOp]⟩
        · have bad := unary rfl; simp at bad
      | cons c l => simp at arity

lemma get_map {A B : Type} (f : A → B) (w : List A) (i : ℕ) (d : A) :
    (w.map f).getD i (f d) = f (w.getD i d) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi,List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

-- The ten free inputs include both polarities of vertex zero.
def raw : List Wire := (List.ofFn (fun i : Fin 9 => ((0,.inr (.lit i true)) : Wire))) ++ [(0,.inr (.lit 0 false))]
def readV (x : Fin 9 → Bool) (w : Wire) := val w.2 x

lemma initialV (x : Fin 9 → Bool) : raw.map (readV x) = List.ofFn x ++ [!(x 0)] := by
  simp [raw,readV,val,DMFormula.eval,Function.comp_def]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma wire_model (C : Circuit) (fan : FanInTwo C) (unary : ∀ g ∈ C.gates, g.op=.not → g.inputs.length≤1) :
    ∃ e : Expr, Sound ((C.gates.foldl stepC (List.replicate 10 0)).getD C.output 0,e) ∧
      ∀ x, val e x = C.eval (List.ofFn x ++ [!(x 0)]) := by
  have inductiveModel (gs : List Gate) (good : ∀ g ∈ gs, allowed g.op ∧ g.inputs.length≤2 ∧ (g.op=.not → g.inputs.length≤1))
      (w : List Wire) (hw : ∀ a ∈ w, Sound a) :
      (∀ a ∈ gs.foldl stepW w, Sound a) ∧
      (gs.foldl stepW w).map Prod.fst = gs.foldl stepC (w.map Prod.fst) ∧
      ∀ x, (gs.foldl stepW w).map (readV x) = gs.foldl stepV (w.map (readV x)) := by
    induction gs generalizing w with
    | nil => exact ⟨hw,rfl,fun _ => rfl⟩
    | cons g gs ih =>
      obtain ⟨ok,arity,un⟩ := good g List.mem_cons_self
      let ins := g.inputs.map fun i => w.getD i missing
      have hs (a) (ha : a ∈ ins) : Sound a := by
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
        by_cases hi : i < w.length
        · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem _)
        · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨by decide,fun _ => True.intro⟩
      have len : ins.length = g.inputs.length := by simp [ins]
      obtain ⟨valid,ev⟩ := gate_ok g.op ins ok (len ▸ arity) (fun z => len ▸ un z) hs
      obtain ⟨v,c,b⟩ := ih (fun a ha => good _ (List.mem_cons_of_mem _ ha)) (stepW w g) (by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hw _ ha
        · have eq := List.mem_singleton.mp ha; rw [eq]; exact valid)
      refine ⟨v,?_,fun x => ?_⟩
      · rw [List.foldl_cons,c,List.foldl_cons]
        congr 1
        simp only [stepW,stepC,List.map_append,List.map_cons,List.map_nil,makeWire,List.map_map,Function.comp_def]
        congr 3
        apply congrArg List.sum
        apply List.map_congr_left
        intro i _; exact (get_map Prod.fst w i missing).symm
      · rw [List.foldl_cons,b,List.foldl_cons]
        congr 1
        simp only [stepW,stepV,List.map_append,List.map_cons,List.map_nil]
        congr 2
        change val (makeWire g.op ins).2 x = _
        rw [ev,List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _; exact (get_map (readV x) w i missing).symm
  have hg (g) (hg : g ∈ C.gates) : allowed g.op ∧ g.inputs.length≤2 ∧ (g.op=.not → g.inputs.length≤1) := by
    obtain ⟨op,k⟩ := fan g hg
    exact ⟨op,k,unary g hg⟩
  obtain ⟨valid,cost,vals⟩ := inductiveModel C.gates hg raw (by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h; exact ⟨Nat.le_refl 1,fun _ => Or.inl rfl⟩
    · have : a = (0,.inr (.lit 0 false)) := List.mem_singleton.mp h
      subst a; exact ⟨by decide,fun _ => Or.inr rfl⟩)
  let ws := C.gates.foldl stepW raw
  have atOut : Sound (ws.getD C.output missing) := by
    by_cases hi : C.output < ws.length
    · rw [List.getD_eq_getElem _ _ hi]; exact valid _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨by decide,fun _ => True.intro⟩
  have count : (ws.getD C.output missing).1 = (C.gates.foldl stepC (List.replicate 10 0)).getD C.output 0 := by
    rw [← get_map Prod.fst ws C.output missing]
    change (List.map Prod.fst (C.gates.foldl stepW raw)).getD C.output 0 = _
    rw [cost]; rfl
  refine ⟨(ws.getD C.output missing).2,?_,fun x => ?_⟩
  · rw [← count]; exact atOut
  · change readV x (ws.getD C.output missing) = _
    rw [← get_map (readV x) ws C.output missing]
    change (List.map (readV x) (C.gates.foldl stepW raw)).getD C.output false = _
    rw [vals,initialV]; rfl

def linked (i j : Fin 9) : Bool :=
  ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).contains (9*i.val+j.val)
def graph : SimpleGraph (Fin 9) where
  Adj i j := (linked i j || linked j i) = true
  symm := ⟨fun i j h => (Bool.or_comm (linked j i) (linked i j)).trans h⟩
  loopless := ⟨by decide +kernel⟩

instance graphDec : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable ((linked i j || linked j i)=true))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma monotone_floor (t : Form) (h : positive t) (he : ∀ x, t.eval x=F x) : 16 ≤ t.leaves := by
  have mono : DMFormula.rec (motive := fun _ : Form => Prop) (fun _ s => s=true)
      (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b) t := by
    clear he
    induction t with
    | lit i s => exact h
    | and a b ia ib | or a b ia ib => exact ⟨ia h.1,ib h.2⟩
  have tri : ∀ a b c, ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c a) := by decide +kernel
  have sq : ∀ a b c d, a ≠ c → b ≠ d → ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by decide +kernel
  have eq : ∀ x : Fin 9 → Bool, F x = decide (∃ i j, graph.Adj i j ∧ x i=true ∧ x j=true) := by decide +kernel
  obtain ⟨T,cov,lower⟩ := monotone_bound 9 graph tri sq t mono (fun x => (he x).trans (eq x))
  have coverBound : ∀ U : Finset (Fin 9), (∀ i j, graph.Adj i j → i ∈ U ∨ j ∈ U) → 4 ≤ U.card := by decide +kernel
  have edgeBound : 12 ≤ graph.edgeFinset.card := by decide +kernel
  have size := coverBound T cov
  omega
lemma solve (C : Circuit) (fan : FanInTwo C) (unary : ∀ g ∈ C.gates, g.op=.not → g.inputs.length≤1)
    (computed : ∀ x, C.eval (List.ofFn x ++ [!(x 0)]) = F x) :
    15 ≤ (C.gates.foldl stepC (List.replicate 10 0)).getD C.output 0 := by
  obtain ⟨e,h,ev⟩ := wire_model C fan unary
  have target (x) : val e x = F x := (ev x).trans (computed x)
  have nonconstant (b : Bool) (bad : ∀ x, b = F x) : False := by
    have n := bad (fun _ => false)
    have y := bad (fun _ => true)
    change b=false at n
    change b=true at y
    simp_all
  by_contra! small
  rcases e with b | t
  · exact nonconstant b target
  obtain ⟨size,saturation⟩ := h
  change t.leaves ≤ (C.gates.foldl stepC (List.replicate 10 0)).getD C.output 0 + 1 at size
  have he : ∀ x, t.eval x=F x := target
  obtain ⟨exactSize,two⟩ := profile t he (by omega)
  have cl : clean t := saturation (show t.leaves = _ by omega)
  obtain ⟨pos,hpos,cap,eq⟩ := makePositive t cl (by omega) he
  rcases pos with b | u
  · exact nonconstant b eq
  · have low := monotone_floor u hpos eq
    change u.leaves ≤ t.leaves at cap
    omega

end PEqualNP.Outside.L_meta_5302

open PEqualNP.Outside.L_meta_5302

theorem PEqualNP.Outside.L_meta_5302 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ))]) = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (9 : ℕ) (x5 / (9 : ℕ))) && x4 (Fin.ofNat (9 : ℕ) (x5 % (9 : ℕ)))) → (15 : ℕ) ≤ (List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [(1 : ℕ) + (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs).sum]) (List.replicate (10 : ℕ) (0 : ℕ)) x1.gates).getD x1.output (0 : ℕ) := by
  exact solve
