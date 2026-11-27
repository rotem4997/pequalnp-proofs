import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5958_aux
def zeroSet {n : Nat} (L : Fin n → Finset (Fin n)) (Y : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun p => ∀ t∈Y, p∉L t)
end PEqualNP.Outside.L_meta_5958_aux

namespace PEqualNP.Outside.L_meta_5958_aux.Unfold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private noncomputable def degree {n : ℕ} (i : Fin n) (F : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => max a b) F

private noncomputable def positive {n : ℕ} (F : DMFormula n) : Bool :=
  DMFormula.rec (motive := fun _ => Bool) (fun _ b => b)
    (fun _ _ a b => a && b) (fun _ _ a b => a && b) F

private def shaped (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j g, gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j

private def leafAt {n : ℕ} (T : List (DMFormula n)) (i : ℕ) : ℕ :=
  (T[i]?.map DMFormula.leaves).getD 0

private def leafSum {n : ℕ} (T : List (DMFormula n)) (R : List ℕ) : ℕ :=
  (R.map (leafAt T)).sum

private lemma leafSum_append {n : ℕ} (T : List (DMFormula n)) (R S : List ℕ) :
    leafSum T (R ++ S) = leafSum T R + leafSum T S := by
  simp [leafSum]

private lemma leafSum_old {n : ℕ} (T : List (DMFormula n)) (F : DMFormula n)
    (R : List ℕ) (h : ∀ i ∈ R, i < T.length) :
    leafSum (T ++ [F]) R = leafSum T R := by
  unfold leafSum
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [leafAt, List.getElem?_append_left (h i hi)]

private lemma leafAt_last {n : ℕ} (T : List (DMFormula n)) (F : DMFormula n) :
    leafAt (T ++ [F]) T.length = F.leaves := by
  simp [leafAt]

private lemma getMap {n : ℕ} {α : Type} {T : List (DMFormula n)} {i : ℕ} {F : DMFormula n}
    (h : T[i]? = some F) (f : DMFormula n → α) (base : α) :
    (T.map f).getD i base = f F := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

private lemma snocBudget {n : ℕ} (gs : List Gate) (g : Gate)
    (T : List (DMFormula n)) (F : DMFormula n) (a b : ℕ)
    (len : T.length = n + gs.length) (inputs : g.inputs = [a,b])
    (oldA : a < T.length) (oldB : b < T.length)
    (newLeaves : F.leaves = leafAt T a + leafAt T b)
    (earlier : ∀ R : List ℕ,
      ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
      (∀ r ∈ R, r < T.length) → leafSum T R ≤ R.length + gs.length) :
    ∀ R : List ℕ,
      ((R ++ (gs ++ [g]).flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
      (∀ r ∈ R, r < (T ++ [F]).length) →
      leafSum (T ++ [F]) R ≤ R.length + (gs ++ [g]).length := by
  intro R unique valid
  let p := fun i : ℕ => decide (n ≤ i)
  let prev := (gs.flatMap Gate.inputs).filter p
  let pair := ([a,b] : List ℕ).filter p
  have packed : (R.filter p ++ (prev ++ pair)).Nodup := by
    simpa only [p, prev, pair, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, inputs, List.filter_append] using unique
  by_cases hR : T.length ∈ R
  · obtain ⟨L, S, rfl⟩ := List.append_of_mem hR
    have pop : p T.length = true := by simp [p, len]
    have packSplit : (L.filter p ++ T.length :: (S.filter p ++ (prev ++ pair))).Nodup := by
      simpa only [List.filter_append, List.filter_cons, pop, ite_true, List.append_assoc, List.cons_append] using packed
    have htail := (List.nodup_append.mp packSplit).2.1
    have noLeft : T.length ∉ L := by
      intro h
      have disjoint := (List.nodup_append.mp packSplit).2.2
      exact disjoint _ (List.mem_filter.mpr ⟨h,pop⟩) _ (by simp) rfl
    have noRight : T.length ∉ S := by
      intro h
      have miss := (List.nodup_cons.mp htail).1
      exact miss (List.mem_append_left _ (List.mem_filter.mpr ⟨h,pop⟩))
    have validL : ∀ i ∈ L, i < T.length := by
      intro i hi
      have inR : i ∈ L ++ T.length :: S := List.mem_append_left _ hi
      have bound := valid i inR
      have different : i ≠ T.length := fun he => noLeft (he ▸ hi)
      simp at bound
      omega
    have validS : ∀ i ∈ S, i < T.length := by
      intro i hi
      have inR : i ∈ L ++ T.length :: S := List.mem_append_right _
        (List.mem_cons_of_mem _ hi)
      have bound := valid i inR
      have different : i ≠ T.length := fun he => noRight (he ▸ hi)
      simp at bound
      omega
    let R' := (L ++ S) ++ [a,b]
    have deleted : ((L.filter p ++ S.filter p) ++ (prev ++ pair)).Nodup := by
      rw [List.append_assoc]
      exact ((List.sublist_cons_self _ _).append_left _).nodup packSplit
    have swapped : ((L.filter p ++ S.filter p) ++ (pair ++ prev)).Nodup :=
      (List.Perm.append_left _ List.perm_append_comm).nodup_iff.mp deleted
    have earlierNodup : ((R' ++ gs.flatMap Gate.inputs).filter p).Nodup := by
      simpa only [R', prev, pair, List.filter_append, List.append_assoc] using swapped
    have earlierValid : ∀ i ∈ R', i < T.length := by
      intro i hi
      simp only [R', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with (h | h) | rfl | rfl
      · exact validL i h
      · exact validS i h
      · exact oldA
      · exact oldB
    have earlierBound := earlier R' earlierNodup earlierValid
    have comparison : leafSum (T ++ [F]) (L ++ T.length :: S) = leafSum T R' := by
      rw [leafSum_append, leafSum_old _ _ _ validL]
      have one : (T.length :: S) = [T.length] ++ S := rfl
      rw [one, leafSum_append, leafSum_old _ _ _ validS]
      simp only [R', leafSum_append]
      have hsingle : leafSum (T ++ [F]) [T.length] = F.leaves := by
        simpa [leafSum] using leafAt_last T F
      rw [hsingle, newLeaves]
      simp [leafSum]
      omega
    rw [comparison]
    simp only [R', List.length_append, List.length_cons, List.length_nil] at earlierBound ⊢
    omega
  · have validOld : ∀ i ∈ R, i < T.length := by
      intro i hi
      have bound := valid i hi
      have different : i ≠ T.length := fun he => hR (he ▸ hi)
      simp at bound
      omega
    have simpler : ((R ++ gs.flatMap Gate.inputs).filter p).Nodup := by
      have initialPart : ((R.filter p ++ prev) ++ pair).Nodup := by
        simpa only [List.append_assoc] using packed
      simpa only [prev, List.filter_append] using (List.nodup_append.mp initialPart).1
    rw [leafSum_old _ _ _ validOld]
    have bound := earlier R simpler validOld
    simp
    omega

private lemma expandAll (n : ℕ) (gs : List Gate) (ok : shaped n gs) :
    ∃ T : List (DMFormula n), T.length = n + gs.length ∧
      (∀ (i : ℕ) (F : DMFormula n), T[i]? = some F → positive F = true) ∧
      (∀ x, T.map (fun F => F.eval x) = (Circuit.mk gs 0).wires (List.ofFn x)) ∧
      (∀ i : Fin n, T.map (degree i) = (Circuit.mk gs 0).lineDegrees n {i.val}) ∧
      ∀ R : List ℕ, ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
        (∀ r ∈ R, r < T.length) → leafSum T R ≤ R.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    let T := List.ofFn (fun i : Fin n => DMFormula.lit i true)
    refine ⟨T, by simp [T], ?_, ?_, ?_, ?_⟩
    · intro i F hi
      obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp hi
      have payload : T[i] = DMFormula.lit ⟨i, by simpa [T] using bound⟩ true := by simp [T]
      rw [payload]
      rfl
    · intro x
      simp [T, Circuit.wires, Function.comp_def, DMFormula.eval]
    · intro i
      apply List.ext_getElem
      · simp [Circuit.lineDegrees, T]
      · intro j hj hj'
        simp only [Circuit.lineDegrees, List.foldl_nil]
        rw [List.getElem_map, List.getElem_map]
        have jT : j < T.length := by simpa using hj
        have eqn : T[j]'jT = DMFormula.lit ⟨j, by simpa [T] using jT⟩ true := by simp [T]
        rw [eqn]
        simp [degree, List.getElem_range, Fin.ext_iff]
    · intro R _ valid
      have single (r : ℕ) (hr : r ∈ R) : leafAt T r = 1 := by
        have br := valid r hr
        have eqn : T[r] = DMFormula.lit ⟨r, by simpa [T] using br⟩ true := by simp [T]
        simp [leafAt, List.getElem?_eq_getElem br, eqn, DMFormula.leaves]
      have eqn : R.map (leafAt T) = R.map (fun _ => 1) := List.map_congr_left single
      simp [leafSum, eqn]
  | append_singleton gs g ih =>
    have early : shaped n gs := by
      intro j h atj
      have bound := (List.getElem?_eq_some_iff.mp atj).choose
      apply ok j h
      rwa [List.getElem?_append_left bound]
    obtain ⟨T, len, pos, evals, degs, budget⟩ := ih early
    have gateAt : (gs ++ [g])[gs.length]? = some g := by simp
    obtain ⟨operator, a, b, inputs, _, ha, hb⟩ := ok gs.length g gateAt
    have ba : a < T.length := len.symm ▸ ha
    have bb : b < T.length := len.symm ▸ hb
    let A := T[a]
    let B := T[b]
    have aAt : T[a]? = some A := List.getElem?_eq_getElem ba
    have bAt : T[b]? = some B := List.getElem?_eq_getElem bb
    let F := match g.op with
      | GateOp.and => DMFormula.and A B
      | _ => DMFormula.or A B
    have posF : positive F = true := by
      rcases operator with op | op <;>
        simpa [F, op, positive] using Bool.and_eq_true_iff.mpr ⟨pos a A aAt, pos b B bAt⟩
    have leafF : F.leaves = leafAt T a + leafAt T b := by
      rcases operator with op | op <;> simp [F, op, DMFormula.leaves, leafAt, aAt, bAt]
    refine ⟨T ++ [F], by simp [len, Nat.add_assoc], ?_, ?_, ?_,
      snocBudget gs g T F a b len inputs ba bb leafF budget⟩
    · intro j H h
      by_cases before : j < T.length
      · rw [List.getElem?_append_left before] at h
        exact pos j H h
      · have inside := (List.getElem?_eq_some_iff.mp h).choose
        have equality : j = T.length := by simp at inside; omega
        subst j
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at h
        exact h ▸ posF
    · intro x
      simp only [List.map_append, List.map_cons, List.map_nil]
      have unfoldStep :
          (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
            (Circuit.mk gs 0).wires (List.ofFn x) ++
              [g.op.eval (g.inputs.map fun j => ((Circuit.mk gs 0).wires (List.ofFn x)).getD j false)] := by
        simp [Circuit.wires, List.foldl_append]
      rw [unfoldStep, ← evals x, inputs]
      simp only [List.map_cons, List.map_nil, getMap aAt, getMap bAt]
      rcases operator with op | op <;> simp [F, op, DMFormula.eval, GateOp.eval]
    · intro i
      simp only [List.map_append, List.map_cons, List.map_nil]
      have unfoldStep :
          (Circuit.mk (gs ++ [g]) 0).lineDegrees n {i.val} =
            (Circuit.mk gs 0).lineDegrees n {i.val} ++
              [g.lineDegree ((Circuit.mk gs 0).lineDegrees n {i.val})] := by
        simp [Circuit.lineDegrees, List.foldl_append]
      rw [unfoldStep, ← degs i]
      rcases operator with op | op <;>
        simp [F, op, degree, Gate.lineDegree, inputs, List.getD_eq_getElem?_getD, aAt, bAt]

lemma unfoldTree (n : ℕ) (C : Circuit) (shape : shaped n C.gates)
    (single : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup)
    (accepts : C.eval (List.ofFn (fun _ : Fin n => true)) = true) :
    ∃ F : DMFormula n, positive F = true ∧ F.leaves ≤ C.size + 1 ∧
      (∀ x, F.eval x = C.eval (List.ofFn x)) ∧
      (∀ i : Fin n, degree i F = C.lineDeg n {i.val}) := by
  obtain ⟨T, len, pos, evals, degs, budget⟩ := expandAll n C.gates shape
  have bound : C.output < T.length := by
    by_contra hn
    change (C.wires (List.ofFn (fun _ : Fin n => true))).getD C.output false = true at accepts
    change ((Circuit.mk C.gates 0).wires (List.ofFn (fun _ : Fin n => true))).getD C.output false = true at accepts
    rw [← evals, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hn)] at accepts
    cases accepts
  let F := T[C.output]
  have found : T[C.output]? = some F := List.getElem?_eq_getElem bound
  have b := budget [C.output] single (by simpa using bound)
  have small : F.leaves ≤ C.size + 1 := by
    simpa [leafSum, leafAt, found, Circuit.size, Nat.add_comm] using b
  refine ⟨F, pos _ _ found, small, ?_, ?_⟩
  · intro x
    change F.eval x = ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD C.output false
    rw [← evals, getMap found]
  · intro i
    change degree i F = ((Circuit.mk C.gates 0).lineDegrees n {i.val}).getD C.output 0
    rw [← degs, getMap found]

end PEqualNP.Outside.L_meta_5958_aux.Unfold

namespace PEqualNP.Outside.L_meta_5958_aux.Protocol

open PEqualNP.MetaComplexity

private def leafLabel {n : ℕ} : (F : DMFormula n) → Fin F.leaves → Fin n
  | .lit i _, _ => i
  | .and a b, x => Fin.addCases (leafLabel a) (leafLabel b) x
  | .or a b, x => Fin.addCases (leafLabel a) (leafLabel b) x

private lemma partition_splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
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

private lemma partition_formulaRectanglesStrong {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) ∧
        label = leafLabel φ := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, ?_, ?_, ?_, rfl⟩
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
      obtain ⟨XA, YA, LA, totalA, xA, yA, eqA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB, eqB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply partition_splitUnique
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
      · simp only [label, leafLabel, eqA, eqB]; rfl
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA, eqA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB, eqB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply partition_splitUnique
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
      · simp only [label, leafLabel, eqA, eqB]; rfl

private noncomputable def degree {n : ℕ} (i : Fin n) (F : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => max a b) F

private noncomputable def positive {n : ℕ} (F : DMFormula n) : Bool :=
  DMFormula.rec (motive := fun _ => Bool) (fun _ b => b)
    (fun _ _ a b => a && b) (fun _ _ a b => a && b) F

private lemma mono_of_positive {n : ℕ} (F : DMFormula n) (hp : positive F = true) :
    DMFormula.rec (motive := fun _ : DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) F := by
  induction F with
  | lit _ _ => exact hp
  | and _ _ ihA ihB =>
    exact ⟨ihA (Bool.and_eq_true_iff.mp hp).1, ihB (Bool.and_eq_true_iff.mp hp).2⟩
  | or _ _ ihA ihB =>
    exact ⟨ihA (Bool.and_eq_true_iff.mp hp).1, ihB (Bool.and_eq_true_iff.mp hp).2⟩

private lemma degree_le_labels {n : ℕ} (F : DMFormula n) (i : Fin n) :
    degree i F ≤ Fintype.card {j : Fin F.leaves // leafLabel F j = i} := by
  have count (m : ℕ) (f : Fin m → Fin n) :
      Fintype.card {j : Fin m // f j = i} = ∑ j : Fin m, if f j = i then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_filter]
  simp only [count]
  induction F with
  | lit j b =>
    change (if j = i then 1 else 0) ≤ ∑ _ : Fin 1, if j = i then 1 else 0
    simp
  | and a b ihA ihB =>
    change degree i a + degree i b ≤ ∑ j : Fin (a.leaves + b.leaves),
      if Fin.addCases (leafLabel a) (leafLabel b) j = i then 1 else 0
    rw [Fin.sum_univ_add]
    simpa only [Fin.addCases_left, Fin.addCases_right] using Nat.add_le_add ihA ihB
  | or a b ihA ihB =>
    change max (degree i a) (degree i b) ≤ ∑ j : Fin (a.leaves + b.leaves),
      if Fin.addCases (leafLabel a) (leafLabel b) j = i then 1 else 0
    rw [Fin.sum_univ_add]
    have sumBound := Nat.add_le_add ihA ihB
    exact (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)).trans
      (by simpa only [Fin.addCases_left, Fin.addCases_right] using sumBound)

lemma partitionFormula (n : ℕ) (F : DMFormula n) (hp : positive F = true) :
    ∃ (A B : Fin F.leaves → (Fin n → Bool) → Prop) (tag : Fin F.leaves → Fin n),
      (∀ i x, A i x → x (tag i) = true) ∧
      (∀ i y, B i y → y (tag i) = false) ∧
      (∀ x y, F.eval x = true → F.eval y = false → ∃! i, A i x ∧ B i y) ∧
      (∀ v, degree v F ≤ Fintype.card {i : Fin F.leaves // tag i = v}) := by
  obtain ⟨A, B, label, partition, hA, hB, eq⟩ :=
    partition_formulaRectanglesStrong F (mono_of_positive F hp)
  exact ⟨A, B, label, (fun i x hx => (hA i x hx).2), (fun i y hy => (hB i y hy).2),
    partition, (fun v => by rw [eq]; exact degree_le_labels F v)⟩

end PEqualNP.Outside.L_meta_5958_aux.Protocol

namespace PEqualNP.Outside.L_meta_5958_aux.Table


private def inc (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3
private def lines (l : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter (fun p => p = l ∨ p = l + 1 ∨ p = l + 3)

private def pointData : ℕ := 0x6435360d1d6a22c8
private def lineData : ℕ := 0x6dadb246da489200
private def starData : ℕ := 0x2939460f7358b5250731483104148ae0e4354549c53311e30c980
private def masksData : ℕ := 0x2081840a409112818bc08308409902a5a0c086224cac2822e461439197177f
private def weightData : ℕ := 0x145965965965a75a769a5964539d35919d35935935935930114d64545164534535939d30116969d65964d65965a74d65964d65a76935915144564d64d14c04e745a9d65935965965935965939d65939d15966945165a75965965a759a4534d14c04d16a75935965935964e75934565145969d14d14d30134565965969d669a5964e75a74d65935964d15945114405935934e74d15934d64e74d16969d65965969d65965966965145965914da5969d35969d65965a76914d34c04675935964d64d64545164535966a75964d65a74d14d30115965969da5964d69d35935915144564d64da5a75965910135934e74564d34e74569d65965965966945165965a75a759659a4534da5a75964404d34d14d34d15a75965965145914d69d10134d34565936965a75969d65966934d34675965965945115934405a74d34d159359a9d65965a74d34d159659a5965a759651459659a5914d39d65965a75a75966914d35a75804d34534d15965945115936a75964d65965939d10134d15964d65969d659a4d34675965145914da5964d65a75914c05a74d34564d69d65a74d345659a5965945166965964674d35965965914d39d65969e759a4d359601345345651459a5914d65964e75914e75964d65964e70134564d65a759a4d15945116a75935964d65965935964d65964530274d14d69d69d34566965146965919d65964d35965964674d35965964d35969e76934d601145451a4675965935964d65964d65964d64539d64d64e70115935a76915146965965914e74d65919d35964d65964d64d65930274535969d1694
private def criticalData : ℕ := 0x569c4db84c4973dd7ca51618d383209

private def pointAt (r : Fin 21) : Fin 7 := ⟨((pointData >>> (3 * r.val)) % 8) % 7, Nat.mod_lt _ (by decide)⟩
private def lineAt (r : Fin 21) : Fin 7 := ⟨((lineData >>> (3 * r.val)) % 8) % 7, Nat.mod_lt _ (by decide)⟩
private def rowAt (v : Fin 14) (i : Fin 3) : Fin 21 :=
  ⟨((starData >>> (5 * (3 * v.val + i.val))) % 32) % 21, Nat.mod_lt _ (by decide)⟩
private def columnAt (c : Fin 37) : Finset (Fin 7) :=
  Finset.univ.filter fun l => (masksData >>> (7 * c.val)).testBit l.val
private def criticalAt (r : Fin 21) : Fin 37 :=
  ⟨((criticalData >>> (6 * r.val)) % 64) % 37, Nat.mod_lt _ (by decide)⟩
private def positive (r : Fin 21) (i : Fin 14) : Bool :=
  decide (i = Fin.castAdd 7 (pointAt r) ∨ i = Fin.natAdd 7 (lineAt r))
private def negative (c : Fin 37) : Fin 14 → Bool :=
  Fin.append (fun p => decide (p ∈ zeroSet lines (columnAt c))) (fun l => decide (l ∈ columnAt c))
private def weight (r : Fin 21) (c : Fin 37) : ℤ :=
  Int.ofNat ((weightData >>> (6 * (37 * r.val + c.val))) % 64) - 20
private def maskRows (v : Fin 14) (M : Finset (Fin 3)) : Finset (Fin 21) :=
  M.image (rowAt v)
private def mass (v : Fin 14) (M : Finset (Fin 3)) (c : Fin 37) : ℤ :=
  ∑ r ∈ maskRows v M, weight r c

set_option maxHeartbeats 0 in
private lemma edges_exact :
    (∀ r, inc (pointAt r) (lineAt r)) ∧
    ∀ p l, p = l ∨ p = l + 1 ∨ p = l + 3 →
      ∃ r, pointAt r = p ∧ lineAt r = l := by
  unfold inc
  decide +kernel

set_option maxHeartbeats 0 in
private lemma stars_exact :
    ∀ v r, positive r v = true ↔ ∃ a : Fin 3, rowAt v a = r := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma columns_maximal : ∀ c, ∀ l ∉ columnAt c,
    ∃ p ∈ zeroSet lines (columnAt c), p = l ∨ p = l + 1 ∨ p = l + 3 := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma total_weight : (∑ r : Fin 21, ∑ c : Fin 37, weight r c) = 1680 := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma pattern_bound : ∀ (v : Fin 14) (M : Finset (Fin 3)),
    (∑ c : Fin 37, if negative c v = false then max 0 (mass v M c) else 0) ≤ 60 := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma critical_pattern : ∀ (r : Fin 21) (v : Fin 14) (M : Finset (Fin 3)),
    r ∈ maskRows v M → negative (criticalAt r) v = false →
      0 ≤ mass v M (criticalAt r) → M = Finset.univ := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma overlap : ∀ (v : Fin 14) (M : Finset (Fin 3)), M.Nonempty →
    ∃ (a : Fin 3) (c : Fin 37), a ∈ M ∧ negative c v = false ∧
      0 < mass v M c ∧ 0 < mass v Finset.univ c := by
  decide +kernel

lemma verifyPartition_lower (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ r c, ∃! i, A i (positive r) ∧ B i (negative c)) : 28≤k := by
  classical
  let M (i : Fin k) : Finset (Fin 3) := Finset.univ.filter (fun a => A i (positive (rowAt (tag i) a)))
  let rows (i : Fin k) : Finset (Fin 21) := Finset.univ.filter (fun r => A i (positive r))
  have rows_eq (i : Fin k) : rows i = maskRows (tag i) (M i) := by
    ext r
    simp only [rows, M, maskRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr
      obtain ⟨a, ha⟩ := (stars_exact (tag i) r).mp (supportsA i (positive r) hr)
      exact ⟨a, ha.symm ▸ hr, ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  let actual (i : Fin k) (c : Fin 37) : ℤ :=
    if B i (negative c) then mass (tag i) (M i) c else 0
  let allowance (i : Fin k) (c : Fin 37) : ℤ :=
    if negative c (tag i) = false then max 0 (mass (tag i) (M i) c) else 0
  let total (i : Fin k) : ℤ := ∑ c : Fin 37, actual i c
  have pointwise (i : Fin k) (c : Fin 37) : actual i c ≤ allowance i c := by
    by_cases hb : B i (negative c)
    · simp only [actual, allowance, hb, supportsB i _ hb, ite_true]
      exact le_max_right _ _
    · unfold actual allowance
      rw [ite_eq_right hb]
      split <;> simp
  have each (i : Fin k) : total i ≤ 60 :=
    (Finset.sum_le_sum fun c _ => pointwise i c).trans (pattern_bound (tag i) (M i))
  have expand (i : Fin k) (c : Fin 37) :
      actual i c = ∑ r : Fin 21, if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
    by_cases hb : B i (negative c)
    · simp only [actual, hb, ite_true, and_true]
      change (∑ r ∈ maskRows (tag i) (M i), weight r c) = _
      rw [← rows_eq]
      change (∑ r ∈ Finset.univ.filter (fun r => A i (positive r)), weight r c) = _
      rw [Finset.sum_filter]
    · simp [actual, hb]
  have one (r : Fin 21) (c : Fin 37) :
      (∑ i : Fin k, if A i (positive r) ∧ B i (negative c) then weight r c else 0) = weight r c := by
    obtain ⟨i, hi, unique⟩ := covers r c
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left hi
    · intro j _ neq
      exact ite_eq_right (fun hj => neq (unique j hj))
    · simp
  have total_eq : (∑ i : Fin k, total i) = 1680 := by
    calc
      (∑ i : Fin k, total i) =
          ∑ i : Fin k, ∑ c : Fin 37, ∑ r : Fin 21,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        simp only [total, expand]
      _ = ∑ c : Fin 37, ∑ r : Fin 21, ∑ i : Fin k,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = 1680 := by
        simp only [one]
        rw [Finset.sum_comm]
        exact total_weight
  have bound : (∑ i : Fin k, total i) ≤ ∑ _i : Fin k, (60 : ℤ) := Finset.sum_le_sum (fun i _ => each i)
  rw [total_eq] at bound
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  have lower : (28 : ℤ)≤(k : ℤ) := by omega
  exact_mod_cast lower

lemma verifyPartition (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14) (limit : k ≤ 28)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ r c, ∃! i, A i (positive r) ∧ B i (negative c)) :
    ∀ p l, inc p l →
      Fintype.card {i : Fin k // tag i = Fin.castAdd 7 p} ≤ 1 ∨
      Fintype.card {i : Fin k // tag i = Fin.natAdd 7 l} ≤ 1 := by
  classical
  let M (i : Fin k) : Finset (Fin 3) := Finset.univ.filter (fun a => A i (positive (rowAt (tag i) a)))
  let rows (i : Fin k) : Finset (Fin 21) := Finset.univ.filter (fun r => A i (positive r))
  have rows_eq (i : Fin k) : rows i = maskRows (tag i) (M i) := by
    ext r
    simp only [rows, M, maskRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr
      obtain ⟨a, ha⟩ := (stars_exact (tag i) r).mp (supportsA i (positive r) hr)
      exact ⟨a, ha.symm ▸ hr, ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  let actual (i : Fin k) (c : Fin 37) : ℤ :=
    if B i (negative c) then mass (tag i) (M i) c else 0
  let allowance (i : Fin k) (c : Fin 37) : ℤ :=
    if negative c (tag i) = false then max 0 (mass (tag i) (M i) c) else 0
  let total (i : Fin k) : ℤ := ∑ c : Fin 37, actual i c
  have pointwise (i : Fin k) (c : Fin 37) : actual i c ≤ allowance i c := by
    by_cases hb : B i (negative c)
    · simp only [actual, allowance, hb, supportsB i _ hb, ite_true]
      exact le_max_right _ _
    · unfold actual allowance
      rw [ite_eq_right hb]
      split <;> simp
  have each (i : Fin k) : total i ≤ 60 :=
    (Finset.sum_le_sum fun c _ => pointwise i c).trans (pattern_bound (tag i) (M i))
  have expand (i : Fin k) (c : Fin 37) :
      actual i c = ∑ r : Fin 21, if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
    by_cases hb : B i (negative c)
    · simp only [actual, hb, ite_true, and_true]
      change (∑ r ∈ maskRows (tag i) (M i), weight r c) = _
      rw [← rows_eq]
      change (∑ r ∈ Finset.univ.filter (fun r => A i (positive r)), weight r c) = _
      rw [Finset.sum_filter]
    · simp [actual, hb]
  have one (r : Fin 21) (c : Fin 37) :
      (∑ i : Fin k, if A i (positive r) ∧ B i (negative c) then weight r c else 0) = weight r c := by
    obtain ⟨i, hi, unique⟩ := covers r c
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left hi
    · intro j _ neq
      exact ite_eq_right (fun hj => neq (unique j hj))
    · simp
  have total_eq : (∑ i : Fin k, total i) = 1680 := by
    calc
      (∑ i : Fin k, total i) =
          ∑ i : Fin k, ∑ c : Fin 37, ∑ r : Fin 21,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        simp only [total, expand]
      _ = ∑ c : Fin 37, ∑ r : Fin 21, ∑ i : Fin k,
            if A i (positive r) ∧ B i (negative c) then weight r c else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = 1680 := by
        simp only [one]
        rw [Finset.sum_comm]
        exact total_weight
  have totals_tight (i : Fin k) : total i = 60 := by
    have k' : (k : ℤ) ≤ 28 := by exact_mod_cast limit
    have noSlack : (∑ j : Fin k, ((60 : ℤ) - total j)) ≤ 0 := by
      rw [Finset.sum_sub_distrib, total_eq]
      simp
      omega
    have localSlack : 60 - total i ≤ ∑ j : Fin k, (60 - total j) :=
      Finset.single_le_sum (fun j _ => sub_nonneg.mpr (each j)) (Finset.mem_univ i)
    have bound := each i
    omega
  have tight (i : Fin k) (c : Fin 37) : actual i c = allowance i c := by
    have noSlack : (∑ j : Fin 37, (allowance i j - actual i j)) ≤ 0 := by
      rw [Finset.sum_sub_distrib]
      change (∑ j : Fin 37, allowance i j) - total i ≤ 0
      have upper := pattern_bound (tag i) (M i)
      change (∑ j : Fin 37, allowance i j) ≤ 60 at upper
      rw [totals_tight]
      omega
    have localSlack : allowance i c - actual i c ≤
        ∑ j : Fin 37, (allowance i j - actual i j) :=
      Finset.single_le_sum (fun j _ => sub_nonneg.mpr (pointwise i j)) (Finset.mem_univ c)
    have bound := pointwise i c
    omega
  have must (i : Fin k) (c : Fin 37) (legal : negative c (tag i) = false)
      (pos : 0 < mass (tag i) (M i) c) : B i (negative c) := by
    by_contra no
    have equal := tight i c
    simp only [actual, allowance, no, legal, ite_true, ite_false, max_eq_right pos.le] at equal
    omega
  have nonempty (i : Fin k) : (M i).Nonempty := by
    by_contra no
    have hempty : M i = ∅ := Finset.not_nonempty_iff_eq_empty.mp no
    have t := totals_tight i
    simp [total, actual, mass, maskRows, hempty] at t
  have singleton (i : Fin k) (full : M i = Finset.univ) :
      Fintype.card {j : Fin k // tag j = tag i} ≤ 1 := by
    rw [Fintype.card_subtype, Finset.card_le_one]
    have only (j : Fin k) (hj : tag j = tag i) : j = i := by
      obtain ⟨a, c, ha, legal, posJ, posI⟩ := overlap (tag j) (M j) (nonempty j)
      have hbJ := must j c legal posJ
      have hbI : B i (negative c) := must i c (by simpa only [hj] using legal)
        (by simpa only [hj, full] using posI)
      let r := rowAt (tag j) a
      have hAj : A j (positive r) := (Finset.mem_filter.mp ha).2
      have hAi : A i (positive r) := by
        have hr : r ∈ maskRows (tag i) (M i) := by
          rw [full]
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simp [r, hj]⟩
        rw [← rows_eq] at hr
        exact (Finset.mem_filter.mp hr).2
      obtain ⟨s, _, choose⟩ := covers r c
      exact (choose j ⟨hAj, hbJ⟩).trans (choose i ⟨hAi, hbI⟩).symm
    intro j hj j' hj'
    exact (only j (Finset.mem_filter.mp hj).2).trans (only j' (Finset.mem_filter.mp hj').2).symm
  intro p l flag
  obtain ⟨r, hp, hl⟩ := edges_exact.2 p l flag
  let c := criticalAt r
  obtain ⟨i, ⟨ha, hb⟩, _⟩ := covers r c
  have legal := supportsB i (negative c) hb
  have hr : r ∈ maskRows (tag i) (M i) := by
    rw [← rows_eq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  have value := tight i c
  simp only [actual, allowance, hb, legal, ite_true] at value
  have nonnegative : (0 : ℤ) ≤ mass (tag i) (M i) c :=
    (le_max_left _ _).trans_eq value.symm
  have full : M i = Finset.univ := critical_pattern r (tag i) (M i) hr legal nonnegative
  have lim := singleton i full
  have sees := supportsA i (positive r) ha
  simp only [positive, hp, hl, decide_eq_true_eq] at sees
  rcases sees with hit | hit
  · exact Or.inl (by simpa only [hit] using lim)
  · exact Or.inr (by simpa only [hit] using lim)

lemma rectangleRigidity (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14) (limit : k ≤ 28)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ a b : Fin 7, inc a b → ∀ Y : Finset (Fin 7),
      let X := zeroSet lines Y
      (∀ v ∉ Y, ∃ u ∈ X, inc u v) →
      ∃! i, A i (fun j => decide (j = Fin.castAdd 7 a ∨ j = Fin.natAdd 7 b)) ∧
        B i (Fin.append (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y)))) :
    ∀ p l : Fin 7, inc p l →
      Fintype.card {i : Fin k // tag i = Fin.castAdd 7 p} ≤ 1 ∨
      Fintype.card {i : Fin k // tag i = Fin.natAdd 7 l} ≤ 1 := by
  apply verifyPartition k A B tag limit supportsA supportsB
  intro r c
  exact covers (pointAt r) (lineAt r) (edges_exact.1 r) (columnAt c) (columns_maximal c)

lemma rectangleLowerBound (k : ℕ) (A B : Fin k → (Fin 14 → Bool) → Prop)
    (tag : Fin k → Fin 14)
    (supportsA : ∀ i x, A i x → x (tag i) = true)
    (supportsB : ∀ i y, B i y → y (tag i) = false)
    (covers : ∀ a b : Fin 7, inc a b → ∀ Y : Finset (Fin 7),
      let X := zeroSet lines Y
      (∀ v ∉ Y, ∃ u ∈ X, inc u v) →
      ∃! i, A i (fun j => decide (j = Fin.castAdd 7 a ∨ j = Fin.natAdd 7 b)) ∧
        B i (Fin.append (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y)))) : 28≤k := by
  apply verifyPartition_lower k A B tag supportsA supportsB
  intro r c
  exact covers (pointAt r) (lineAt r) (edges_exact.1 r) (columnAt c) (columns_maximal c)

end PEqualNP.Outside.L_meta_5958_aux.Table

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_5958_aux
lemma formula_rigidity :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x3 x4 → x1 x5 x6 → PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {↑x5} x4 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {(7 : ℕ) + ↑x6} x4 (1 : ℕ) := by
  intro inc valid tree C p l hC hTree hFlag
  obtain ⟨size, shaped, correct⟩ := hC
  have allTrue : C.eval (List.ofFn (fun _ : Fin 14 => true)) = true :=
    (correct _).mpr ⟨p,l,hFlag,rfl,rfl⟩
  obtain ⟨F, positive, leaves, agrees, degree⟩ := PEqualNP.Outside.L_meta_5958_aux.Unfold.unfoldTree 14 C shaped hTree allTrue
  obtain ⟨A, B, tag, supportsA, supportsB, partition, counts⟩ :=
    PEqualNP.Outside.L_meta_5958_aux.Protocol.partitionFormula 14 F positive
  have table := PEqualNP.Outside.L_meta_5958_aux.Table.rectangleRigidity F.leaves A B tag (by omega) supportsA supportsB
    (by
      intro a b hab Y X _
      apply partition
      · rw [agrees]
        exact (correct _).mpr ⟨a,b,hab,by simp,by simp⟩
      · rw [agrees]
        cases h : C.eval (List.ofFn (Fin.append
          (fun u => decide (u ∈ X)) (fun v => decide (v ∈ Y)))) with
        | false => rfl
        | true =>
          obtain ⟨u,v,huv,hu,hv⟩ := (correct _).mp h
          have hu' : u ∈ X := by simpa only [Fin.append_left, decide_eq_true_eq] using hu
          have hv' : v ∈ Y := by simpa only [Fin.append_right, decide_eq_true_eq] using hv
          change u ∈ Finset.univ.filter (fun p : Fin 7 => ∀ t ∈ Y,
            p ∉ Finset.univ.filter (fun r : Fin 7 => r = t ∨ r = t + 1 ∨ r = t + 3)) at hu'
          exact ((Finset.mem_filter.mp hu').2 v hv'
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩)).elim) p l hFlag
  rcases table with h | h
  · left
    have bound := (counts (Fin.castAdd 7 p)).trans h
    change C.lineDeg 14 {(Fin.castAdd 7 p).val} ≤ 1
    rw [← degree (Fin.castAdd 7 p)]
    exact bound
  · right
    have bound := (counts (Fin.natAdd 7 l)).trans h
    change C.lineDeg 14 {(Fin.natAdd 7 l).val} ≤ 1
    rw [← degree (Fin.natAdd 7 l)]
    exact bound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def df (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d

def cf (n : ℕ) (gs : List Gate) : List (List ℕ) :=
  gs.foldl (coneStep n) []

lemma getD_snoc_lt {α : Type} (L : List α) (a d : α) (k : ℕ) (h : k < L.length) :
    (L ++ [a]).getD k d = L.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt {α : Type} (L : List α) (a d : α) (k : ℕ) (h : L.length < k) :
    (L ++ [a]).getD k d = d := by
  rw [List.getD_eq_default]; simp; omega

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma df_len (gs : List Gate) : ∀ d : List ℕ, (df gs d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp [df]
  | cons g gs ih =>
    intro d
    have := ih (d ++ [g.lineDegree d])
    simp only [df, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_getD_lt (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < w.length →
    (wf gs w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; simp [wf]
  | cons g gs ih =>
    intro w k hk
    have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) k (by simp; omega)
    simp only [wf, List.foldl_cons] at h1 ⊢
    rw [h1, getD_snoc_lt w _ false k hk]

lemma df_getD_lt (gs : List Gate) : ∀ (d : List ℕ) (k : ℕ), k < d.length →
    (df gs d).getD k 0 = d.getD k 0 := by
  induction gs with
  | nil => intro d k _; simp [df]
  | cons g gs ih =>
    intro d k hk
    have h1 := ih (d ++ [g.lineDegree d]) k (by simp; omega)
    simp only [df, List.foldl_cons] at h1 ⊢
    rw [h1, getD_snoc_lt d _ 0 k hk]

lemma wf_append (gs1 gs2 : List Gate) (w : List Bool) :
    wf (gs1 ++ gs2) w = wf gs2 (wf gs1 w) := by
  simp [wf, List.foldl_append]

lemma df_append (gs1 gs2 : List Gate) (d : List ℕ) :
    df (gs1 ++ gs2) d = df gs2 (df gs1 d) := by
  simp [df, List.foldl_append]

lemma mem_le_sum (l : List ℕ) (a : ℕ) (ha : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.mem_cons] at ha
    simp only [List.sum_cons]
    rcases ha with rfl | ht
    · omega
    · have := ih ht; omega

lemma mem_le_foldr_max (l : List ℕ) (a : ℕ) (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.mem_cons] at ha
    simp only [List.foldr_cons]
    rcases ha with rfl | ht
    · exact le_max_left _ _
    · exact le_trans (ih ht) (le_max_right _ _)

lemma mem_le_lineDegree (g : Gate) (d : List ℕ) (w : ℕ) (hw : w ∈ g.inputs) :
    d.getD w 0 ≤ g.lineDegree d := by
  unfold Gate.lineDegree
  split_ifs
  · exact mem_le_sum _ _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  · exact mem_le_foldr_max _ _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

lemma cones_mono (n : ℕ) (gs : List Gate) :
    (cf n gs).length = gs.length ∧
    ∀ (d0 : List ℕ), d0.length = n →
      ∀ j < gs.length, ∀ i ∈ (cf n gs).getD j [],
        i < j ∧ (df gs d0).getD (n + i) 0 ≤ (df gs d0).getD (n + j) 0 := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [cf], ?_⟩
    intro d0 _ j hj
    simp at hj
  | append_singleton gs g ih =>
    obtain ⟨hlen, hmono⟩ := ih
    have hcf : cf n (gs ++ [g]) = coneStep n (cf n gs) g := by
      simp [cf, List.foldl_append]
    have hlen' : (cf n (gs ++ [g])).length = (gs ++ [g]).length := by
      rw [hcf]; simp [coneStep, hlen]
    refine ⟨hlen', ?_⟩
    intro d0 hd0 j hj i hi
    have hdl : (df gs d0).length = n + gs.length := by rw [df_len, hd0]
    have hdf : df (gs ++ [g]) d0 = df gs d0 ++ [g.lineDegree (df gs d0)] := by
      simp [df, List.foldl_append]
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [hcf, coneStep, getD_snoc_lt _ _ _ j (by omega)] at hi
      obtain ⟨hij, hle⟩ := hmono d0 hd0 j hlt i hi
      refine ⟨hij, ?_⟩
      rw [hdf, getD_snoc_lt _ _ 0 (n + i) (by omega), getD_snoc_lt _ _ 0 (n + j) (by omega)]
      exact hle
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [hcf, coneStep, ← hlen, getD_snoc_eq] at hi
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hi
      obtain ⟨w, ⟨hw_in, hnw, hwlt⟩, hwi⟩ := hi
      rw [hlen] at hwlt
      have hdeg_w : (df gs d0).getD w 0 ≤ g.lineDegree (df gs d0) :=
        mem_le_lineDegree g (df gs d0) w hw_in
      have htop : (df (gs ++ [g]) d0).getD (n + gs.length) 0 = g.lineDegree (df gs d0) := by
        rw [hdf, ← hdl, getD_snoc_eq]
      simp only [List.mem_cons] at hwi
      rcases hwi with rfl | hwi
      · refine ⟨by omega, ?_⟩
        rw [htop, hdf, getD_snoc_lt _ _ 0 (n + (w - n)) (by omega)]
        have hw_eq : n + (w - n) = w := by omega
        rw [hw_eq]
        exact hdeg_w
      · obtain ⟨hij, hle⟩ := hmono d0 hd0 (w - n) (by omega) i hwi
        refine ⟨by omega, ?_⟩
        rw [htop, hdf, getD_snoc_lt _ _ 0 (n + i) (by omega)]
        have hw_eq : n + (w - n) = w := by omega
        rw [hw_eq] at hle
        exact le_trans hle hdeg_w

lemma zero_deg_indep (n : ℕ) (S : Finset ℕ) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i < n, i ∉ S → x.getD i false = y.getD i false) (gs : List Gate) :
    let d0 := (List.range n).map fun i => if i ∈ S then 1 else 0
    ∀ w, (df gs d0).getD w 0 = 0 → (wf gs x).getD w false = (wf gs y).getD w false := by
  intro d0
  have hd0 : d0.length = n := by simp [d0]
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [wf, df, List.foldl_nil] at hw ⊢
    by_cases hwn : w < n
    · have hdw : d0.getD w 0 = if w ∈ S then 1 else 0 := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [d0, hwn]
      rw [hdw] at hw
      have hwS : w ∉ S := by
        intro hmem
        simp [hmem] at hw
      exact hxy w hwn hwS
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro w hw
    have hdl : (df gs d0).length = n + gs.length := by rw [df_len, hd0]
    have hxl : (wf gs x).length = n + gs.length := by rw [wf_len, hx]
    have hyl : (wf gs y).length = n + gs.length := by rw [wf_len, hy]
    have hdf : df (gs ++ [g]) d0 = df gs d0 ++ [g.lineDegree (df gs d0)] := by
      simp [df, List.foldl_append]
    have hwfx : wf (gs ++ [g]) x = wf gs x ++ [g.op.eval (g.inputs.map fun i => (wf gs x).getD i false)] := by
      simp [wf, List.foldl_append]
    have hwfy : wf (gs ++ [g]) y = wf gs y ++ [g.op.eval (g.inputs.map fun i => (wf gs y).getD i false)] := by
      simp [wf, List.foldl_append]
    rw [hdf] at hw
    rw [hwfx, hwfy]
    rcases Nat.lt_trichotomy w (n + gs.length) with hlt | heq | hgt
    · rw [getD_snoc_lt _ _ 0 w (by omega)] at hw
      rw [getD_snoc_lt _ _ false w (by omega), getD_snoc_lt _ _ false w (by omega)]
      exact ih w hw
    · subst heq
      rw [← hdl, getD_snoc_eq] at hw
      have hx_eq : (wf gs x ++ [g.op.eval (g.inputs.map fun i => (wf gs x).getD i false)]).getD (n + gs.length) false =
          g.op.eval (g.inputs.map fun i => (wf gs x).getD i false) := by
        rw [← hxl, getD_snoc_eq]
      have hy_eq : (wf gs y ++ [g.op.eval (g.inputs.map fun i => (wf gs y).getD i false)]).getD (n + gs.length) false =
          g.op.eval (g.inputs.map fun i => (wf gs y).getD i false) := by
        rw [← hyl, getD_snoc_eq]
      rw [hx_eq, hy_eq]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hdu : (df gs d0).getD u 0 = 0 := by
        have hle := mem_le_lineDegree g (df gs d0) u hu
        omega
      exact ih u hdu
    · rw [getD_snoc_gt _ _ false w (by omega), getD_snoc_gt _ _ false w (by omega)]

lemma gate_and_eval (n : ℕ) (C : Circuit) (j a b : ℕ) (g : Gate)
    (hget : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) (x : Fin n → Bool) :
    gateVal n C j x = (wireVal n C a x && wireVal n C b x) := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hget).1
  have hsplit : C.gates = C.gates.take j ++ [g] ++ C.gates.drop (j + 1) := by
    have h2 : C.gates.drop j = g :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]
      have hg : C.gates[j] = g := (List.getElem?_eq_some_iff.mp hget).2
      rw [hg]
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [h2]
    simp [List.append_assoc]
  have htake_len : (C.gates.take j).length = j := by simp [hj.le]
  let lx := List.ofFn x
  have hlx : lx.length = n := by simp [lx]
  let L1 := wf (C.gates.take j) lx
  have hL1_len : L1.length = n + j := by rw [wf_len, hlx, htake_len]
  have hcw : C.wires lx = wf (C.gates.drop (j + 1)) (L1 ++ [g.op.eval (g.inputs.map fun i => L1.getD i false)]) := by
    change wf C.gates lx = _
    conv_lhs => rw [hsplit]
    rw [wf_append, wf_append]
    simp [L1, wf]
  have hwire_lt : ∀ k < n + j, (C.wires lx).getD k false = L1.getD k false := by
    intro k hk
    rw [hcw, wf_getD_lt _ _ k (by simp [hL1_len]; omega), getD_snoc_lt _ _ false k (by omega)]
  have hgate : (C.wires lx).getD (n + j) false = g.op.eval (g.inputs.map fun i => L1.getD i false) := by
    rw [hcw, wf_getD_lt _ _ (n + j) (by simp [hL1_len]), ← hL1_len, getD_snoc_eq]
  change (C.wires lx).getD (n + j) false = ((C.wires lx).getD a false && (C.wires lx).getD b false)
  rw [hgate, hwire_lt a ha, hwire_lt b hb, hop, hin]
  simp [GateOp.eval]

lemma gate_and_deg (n : ℕ) (S : Finset ℕ) (C : Circuit) (j a b : ℕ) (g : Gate)
    (hget : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    (C.lineDegrees n S).getD (n + j) 0 =
      (C.lineDegrees n S).getD a 0 + (C.lineDegrees n S).getD b 0 := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hget).1
  have hsplit : C.gates = C.gates.take j ++ [g] ++ C.gates.drop (j + 1) := by
    have h2 : C.gates.drop j = g :: C.gates.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]
      have hg : C.gates[j] = g := (List.getElem?_eq_some_iff.mp hget).2
      rw [hg]
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [h2]
    simp [List.append_assoc]
  have htake_len : (C.gates.take j).length = j := by simp [hj.le]
  let d0 := (List.range n).map fun i => if i ∈ S then 1 else 0
  have hd0 : d0.length = n := by simp [d0]
  let D1 := df (C.gates.take j) d0
  have hD1_len : D1.length = n + j := by rw [df_len, hd0, htake_len]
  have hcd : C.lineDegrees n S = df (C.gates.drop (j + 1)) (D1 ++ [g.lineDegree D1]) := by
    change df C.gates d0 = _
    conv_lhs => rw [hsplit]
    rw [df_append, df_append]
    simp [D1, df]
  have hdeg_lt : ∀ k < n + j, (C.lineDegrees n S).getD k 0 = D1.getD k 0 := by
    intro k hk
    rw [hcd, df_getD_lt _ _ k (by simp [hD1_len]; omega), getD_snoc_lt _ _ 0 k (by omega)]
  have hdeg_j : (C.lineDegrees n S).getD (n + j) 0 = g.lineDegree D1 := by
    rw [hcd, df_getD_lt _ _ (n + j) (by simp [hD1_len]), ← hD1_len, getD_snoc_eq]
  rw [hdeg_j, hdeg_lt a ha, hdeg_lt b hb]
  simp [Gate.lineDegree, hop, hin]

lemma contra_one (C : Circuit)
    (hshape : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j)
    (hout_ge : 14 ≤ C.output) (hout_lt : C.output < 14 + C.gates.length)
    (m : ℕ) (p : Fin 14) (j : ℕ)
    (hdeg : HasLineDegree 14 {m} C 1)
    (hagree : ∀ i : Fin 14, i.val ≠ m → pairInput (0 : Fin 14) 7 i = pairInput p p i)
    (hj_and : (gateAt C j).op = GateOp.and)
    (hj_cone : 14 + j = C.output ∨ InCone 14 C j (C.output - 14))
    (hj_true : gateVal 14 C j (pairInput (0 : Fin 14) 7) = true)
    (hj_opnd : ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput p p) = false) :
    False := by
  have hmono := cones_mono 14 C.gates
  have hj_lt_and_le : j < C.gates.length ∧ (C.lineDegrees 14 {m}).getD (14 + j) 0 ≤ C.lineDeg 14 {m} := by
    rcases hj_cone with heq | hcone
    · refine ⟨by omega, ?_⟩
      rw [heq]
      exact le_refl _
    · have hout_sub : C.output - 14 < C.gates.length := by omega
      have h0 : ((List.range 14).map fun i => if i ∈ ({m} : Finset ℕ) then 1 else 0).length = 14 := by simp
      obtain ⟨hjl, hle⟩ := hmono.2 _ h0 (C.output - 14) hout_sub j hcone
      have h14 : 14 + (C.output - 14) = C.output := by omega
      refine ⟨by omega, ?_⟩
      change (df C.gates _).getD (14 + j) 0 ≤ (df C.gates _).getD C.output 0
      rw [← h14]
      exact hle
  obtain ⟨hj_lt, hdeg_j_le⟩ := hj_lt_and_le
  have hdeg_j : (C.lineDegrees 14 {m}).getD (14 + j) 0 ≤ 1 := le_trans hdeg_j_le hdeg
  let g := C.gates[j]
  have hget : C.gates[j]? = some g := List.getElem?_eq_getElem hj_lt
  have hgat : gateAt C j = g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hget]
  have hop : g.op = GateOp.and := by rwa [← hgat]
  obtain ⟨_, a, b, hin, _, ha, hb⟩ := hshape j g hget
  have hop0 : opnd C j 0 = a := by simp [opnd, hgat, hin]
  have hop1 : opnd C j 1 = b := by simp [opnd, hgat, hin]
  have hev := gate_and_eval 14 C j a b g hget hop hin ha hb (pairInput (0 : Fin 14) 7)
  rw [hj_true] at hev
  obtain ⟨hwa, hwb⟩ := Bool.and_eq_true_iff.mp hev.symm
  have hdg := gate_and_deg 14 {m} C j a b g hget hop hin ha hb
  have hsum : (C.lineDegrees 14 {m}).getD a 0 + (C.lineDegrees 14 {m}).getD b 0 ≤ 1 := by omega
  have hind : ∀ w, (C.lineDegrees 14 {m}).getD w 0 = 0 →
      wireVal 14 C w (pairInput (0 : Fin 14) 7) = wireVal 14 C w (pairInput p p) := by
    intro w hw
    apply zero_deg_indep 14 {m} (List.ofFn (pairInput (0 : Fin 14) 7)) (List.ofFn (pairInput p p))
      (by simp) (by simp) _ C.gates w hw
    intro i hi hni
    have hne : i ≠ m := by simpa using hni
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi])]
    simp only [List.getElem_ofFn]
    exact hagree ⟨i, hi⟩ hne
  have hzero : (C.lineDegrees 14 {m}).getD a 0 = 0 ∨ (C.lineDegrees 14 {m}).getD b 0 = 0 := by omega
  rcases hzero with hza | hzb
  · have h1 := hind a hza
    have h2 := hj_opnd 0
    rw [hop0] at h2
    rw [hwa, h2] at h1
    cases h1
  · have h1 := hind b hzb
    have h2 := hj_opnd 1
    rw [hop1] at h2
    rw [hwb, h2] at h1
    cases h1

end PEqualNP.Outside.L_meta_5958_aux

theorem PEqualNP.Outside.L_meta_5958 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) →       (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) →         (List.filter (fun (x5 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x5)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup →           have x6 : ℕ → Fin (14 : ℕ) → Prop := fun (x6 : ℕ) (x7 : Fin (14 : ℕ)) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x6 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x6 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x8 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x6 x8) (PEqualNP.EdgeOwnership.pairInput x7 x7) = Bool.false;           ∀ (x7 x8 : ℕ), x6 x7 (0 : Fin (14 : ℕ)) → ¬x6 x8 (7 : Fin (14 : ℕ))) := by
  intro x1 hsize hshape hcorr hnodup x6 x7 x8 hx7 hx8
  have hrig := PEqualNP.Outside.L_meta_5958_aux.formula_rigidity x1 0 0 ⟨hsize, hshape, hcorr⟩ hnodup (Or.inl rfl)
  have hout_lt : x1.output < 14 + x1.gates.length := by
    by_contra hge
    have hev : x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7)) = true :=
      (hcorr _).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
    have hlen : (x1.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7))).length = 14 + x1.gates.length := by
      have := PEqualNP.Outside.L_meta_5958_aux.wf_len x1.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7))
      simpa [PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_meta_5958_aux.wf] using this
    have hfalse : x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7)) = false := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      exact List.getD_eq_default _ _ (by omega)
    rw [hfalse] at hev
    cases hev
  have hout_ge : 14 ≤ x1.output := by
    by_contra hlt
    have hlt' : x1.output < 14 := by omega
    let k : Fin 14 := ⟨x1.output, hlt'⟩
    have hev : x1.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput k k)) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      change (PEqualNP.Outside.L_meta_5958_aux.wf x1.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput k k))).getD x1.output false = true
      rw [PEqualNP.Outside.L_meta_5958_aux.wf_getD_lt _ _ x1.output (by simp [hlt'])]
      rw [List.getD_eq_getElem _ _ (by simp [hlt'])]
      rw [List.getElem_ofFn]
      simp [k, PEqualNP.EdgeOwnership.pairInput]
    obtain ⟨p, l, _, hp, hl⟩ := (hcorr _).mp hev
    simp only [PEqualNP.EdgeOwnership.pairInput, or_self, decide_eq_true_eq] at hp hl
    have hpv := congrArg Fin.val hp
    have hlv := congrArg Fin.val hl
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hpv hlv
    have := p.isLt
    omega
  rcases hrig with h0 | h7
  · exact PEqualNP.Outside.L_meta_5958_aux.contra_one x1 hshape hout_ge hout_lt 0 7 x8 h0
      (by decide) hx8.1 hx8.2.1 hx8.2.2.1 hx8.2.2.2
  · exact PEqualNP.Outside.L_meta_5958_aux.contra_one x1 hshape hout_ge hout_lt 7 0 x7 h7
      (by decide) hx7.1 hx7.2.1 hx7.2.2.1 hx7.2.2.2
