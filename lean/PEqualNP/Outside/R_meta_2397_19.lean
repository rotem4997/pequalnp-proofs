import Mathlib.Data.List.Forall2
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2397_19
    (compile : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     have x6 : Set (Set (Fin x1)) := {∅, Set.univ} ∪ Set.range fun (x6 : Fin x2) => {x7 : Fin x1 | x3 x7 x6 = Bool.true};     ∃ (x7 : List (Set (Fin x1))),       x7.length ≤ x4.size ∧         (∀ (x8 : Fin x7.length),             have x9 : Set (Set (Fin x1)) := x6 ∪ {x9 : Set (Fin x1) | x9 ∈ List.take (↑x8) x7};             x7.getD x8.val ∅ ∉ x9 ∧ ∃ x10 ∈ x9, ∃ x11 ∈ x9, x7.getD x8.val ∅ = x10 ∪ x11 ∨ x7.getD x8.val ∅ = x10 ∩ x11) ∧           {x8 : Fin x1 | PEqualNP.MetaComplexity.circuitFun x2 x4 (x3 x8) = Bool.true} ∈ x6 ∪ {x8 : Set (Fin x1) | x8 ∈ x7})
    (separate : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∃ (x2 : ℕ) (x3 : Fin x2 → Finset (Fin (13 : ℕ))) (x4 : Fin x2 → Finset (Fin (13 : ℕ))) (x5 : Set (Fin x2)),   (∀ x6 ∈ x5, ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x3 x6 = {x8} ∧ x4 x6 = {x9}) ∧     (∀ x6 ∉ x5, (∀ x8 ∈ x3 x6, ∀ x10 ∈ x4 x6, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x3 x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x4 x6 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧       have x6 : Fin x2 → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x6 : Fin x2) => Fin.addCases (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 ∈ x3 x6)) fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x7 ∈ x4 x6);       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | x6 x8 x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))),         x8.length ≤ (63 : ℕ) →           (∀ (x10 : Fin x8.length),               have x11 : Set (Set (Fin x2)) := x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8};               x8.getD x10.val ∅ ∉ x11 ∧ ∃ x12 ∈ x11, ∃ x13 ∈ x11, x8.getD x10.val ∅ = x12 ∪ x13 ∨ x8.getD x10.val ∅ = x12 ∩ x13) →             x5 ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ x8}) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), (∀ x9 ∈ x6, x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true) → (∀ x10 ∈ x7, x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x8 = Bool.true := by
  classical
  have grow : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ x y : Fin n → Bool,
      (∀ i, x i = true → y i = true) → circuitFun n C x = true → circuitFun n C y = true := by
    intro n D hd x y hxy
    let leB := fun (a b : Bool) => a = true → b = true
    have readLE {u v : List Bool} (h : List.Forall₂ leB u v) (i : ℕ) :
        leB (u.getD i false) (v.getD i false) := by
      by_cases hi : i < u.length
      · have hj : i < v.length := h.length_eq ▸ hi
        rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
        exact h.get hi hj
      · have hj : v.length ≤ i := by have := h.length_eq; omega
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi), List.getD_eq_default _ _ hj]
        exact id
    let val := fun (g : Gate) (u : List Bool) => g.op.eval (g.inputs.map fun i => u.getD i false)
    have andValue (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orValue (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have each (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {u v : List Bool}
        (h : List.Forall₂ leB u v) : leB (val g u) (val g v) := by
      intro hgu
      rcases hg with ha | ho
      · have hu : ∀ i ∈ g.inputs, u.getD i false = true := by
          simpa [val,ha,andValue,List.all_map,Function.comp_def] using hgu
        simpa [val,ha,andValue,List.all_map,Function.comp_def] using
          (show ∀ i ∈ g.inputs, v.getD i false = true from fun i hi => readLE h i (hu i hi))
      · have hu : ∃ i ∈ g.inputs, u.getD i false = true := by
          simpa [val,ho,orValue,List.any_map,Function.comp_def] using hgu
        obtain ⟨i,hi,yes⟩ := hu
        simpa [val,ho,orValue,List.any_map,Function.comp_def] using
          (show ∃ j ∈ g.inputs, v.getD j false = true from ⟨i,hi,readLE h i yes⟩)
    let step := fun (u : List Bool) (g : Gate) => u ++ [val g u]
    have fold (gs : List Gate) (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
        {u v : List Bool} (h : List.Forall₂ leB u v) :
        List.Forall₂ leB (gs.foldl step u) (gs.foldl step v) := by
      induction gs generalizing u v with
      | nil => exact h
      | cons g gs ih =>
        exact ih (fun q hq => legal q (by simp [hq]))
          (List.rel_append h (.cons (each g (legal g (by simp)) h) .nil))
    have raw : List.Forall₂ leB (List.ofFn x) (List.ofFn y) := by
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp, ?_⟩
      intro i hi hj
      simpa [leB, List.get_eq_getElem, List.getElem_ofFn] using hxy ⟨i, by simpa using hi⟩
    exact readLE (fold D.gates (fun g hg => (hd g hg).1) raw) D.output
  dsimp only
  intro C hc size pos
  obtain ⟨m,P,L,T,hp,hn,hard⟩ := separate
  let X := fun (r : Fin m) => Fin.addCases (motive := fun _ => Bool)
        (fun i : Fin 13 => decide (i ∈ P r)) (fun j : Fin 13 => decide (j ∈ L r))
  obtain ⟨s, sl, rules, reach⟩ := compile m 26 X C hc
  by_contra hno
  have eqT : {r | circuitFun 26 C (X r) = true} = T := by
    ext r
    change circuitFun 26 C (X r) = true ↔ r ∈ T
    constructor
    · intro yes
      by_contra hr
      obtain ⟨dis,pc,lc⟩ := hn r hr
      apply hno
      refine ⟨P r, L r, dis, pc, lc, ?_⟩
      intro y yp yl
      apply grow 26 C hc (X r) y _ yes
      intro i
      refine Fin.addCases (m := 13) (n := 13)
        (motive := fun i => X r i = true → y i = true) ?_ ?_ i
      · intro j hj
        exact yp j (of_decide_eq_true (by simpa only [X, Fin.addCases_left] using hj))
      · intro j hj
        exact yl j (of_decide_eq_true (by simpa only [X, Fin.addCases_right] using hj))
    · intro hr
      obtain ⟨p,l,inc,hP,hL⟩ := hp r hr
      have same : X r = (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) := by
        funext i
        refine Fin.addCases (m := 13) (n := 13)
          (motive := fun i => X r i = decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) ?_ ?_ i
        · intro a
          simp only [X, Fin.addCases_left, hP, Finset.mem_singleton]
          exact (show ∀ a p l : Fin 13, decide (a=p) =
            decide (Fin.castAdd 13 a = Fin.castAdd 13 p ∨ Fin.castAdd 13 a = Fin.natAdd 13 l) by decide) a p l
        · intro a
          simp only [X, Fin.addCases_right, hL, Finset.mem_singleton]
          exact (show ∀ a p l : Fin 13, decide (a=l) =
            decide (Fin.natAdd 13 a = Fin.castAdd 13 p ∨ Fin.natAdd 13 a = Fin.natAdd 13 l) by decide) a p l
      rw [same]
      exact pos p l inc
  exact hard s (sl.trans size) rules (eqT ▸ reach)
