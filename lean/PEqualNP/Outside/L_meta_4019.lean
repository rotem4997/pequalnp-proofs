import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import PEqualNP.Defs

-- Wire evaluation transport adapts the checked relabeling lemmas of L_meta_1351.

namespace PEqualNP.Outside.L_meta_4019.Flags

def shiftSet : Finset (Fin 13) := {0, 1, 3, 9}

def incidence (p l : Fin 13) : Prop := p - l ∈ shiftSet

instance : DecidableRel incidence := fun p l =>
  inferInstanceAs (Decidable (p - l ∈ shiftSet))

private def translate (p : Fin 13) : Equiv.Perm (Fin 13) where
  toFun x := x - p
  invFun x := x + p
  left_inv x := sub_add_cancel x p
  right_inv x := add_sub_cancel_right x p

private theorem translate_incidence (a p l : Fin 13) :
    incidence (translate a p) (translate a l) ↔ incidence p l := by
  change (p - a) - (l - a) ∈ shiftSet ↔ p - l ∈ shiftSet
  rw [sub_sub_sub_cancel_right]

private def rotate : Equiv.Perm (Fin 13) where
  toFun x := 3 * x
  invFun x := 9 * x
  left_inv := by show ∀ x : Fin 13, 9 * (3 * x) = x; decide +kernel
  right_inv := by show ∀ x : Fin 13, 3 * (9 * x) = x; decide +kernel

private theorem rotate_incidence (p l : Fin 13) :
    incidence (rotate p) (rotate l) ↔ incidence p l :=
  (by decide +kernel : ∀ p l : Fin 13, incidence (rotate p) (rotate l) ↔ incidence p l) p l

private def pointSwap : Fin 13 → Fin 13 := ![0, 4, 2, 5, 1, 3, 6, 9, 12, 7, 10, 11, 8]
private def lineSwap : Fin 13 → Fin 13 := ![4, 1, 2, 5, 0, 3, 6, 9, 11, 7, 10, 8, 12]

private def swapPoints : Equiv.Perm (Fin 13) :=
  Function.Involutive.toPerm pointSwap (by
    show ∀ p : Fin 13, pointSwap (pointSwap p) = p
    decide +kernel)

private def swapLines : Equiv.Perm (Fin 13) :=
  Function.Involutive.toPerm lineSwap (by
    show ∀ l : Fin 13, lineSwap (lineSwap l) = l
    decide +kernel)

private theorem swap_incidence (p l : Fin 13) :
    incidence (swapPoints p) (swapLines l) ↔ incidence p l :=
  (by decide +kernel : ∀ p l : Fin 13, incidence (swapPoints p) (swapLines l) ↔ incidence p l) p l

private theorem normalize_from_zero {l : Fin 13} (h : incidence 0 l) :
    ∃ (σ τ : Equiv.Perm (Fin 13)), σ 0 = 0 ∧ τ l = 0 ∧
      ∀ p' l', incidence (σ p') (τ l') ↔ incidence p' l' := by
  have hl : l = 0 ∨ l = 4 ∨ l = 10 ∨ l = 12 :=
    (by decide +kernel : ∀ l : Fin 13, incidence 0 l → l = 0 ∨ l = 4 ∨ l = 10 ∨ l = 12) l h
  rcases hl with rfl | rfl | rfl | rfl
  · exact ⟨Equiv.refl _, Equiv.refl _, rfl, rfl, fun _ _ => Iff.rfl⟩
  · exact ⟨swapPoints, swapLines, by decide +kernel, by decide +kernel, swap_incidence⟩
  · refine ⟨rotate.trans swapPoints, rotate.trans swapLines, by decide +kernel,
      by decide +kernel, fun p' l' => ?_⟩
    exact (swap_incidence (rotate p') (rotate l')).trans (rotate_incidence p' l')
  · refine ⟨(rotate.trans rotate).trans swapPoints, (rotate.trans rotate).trans swapLines,
      by decide +kernel, by decide +kernel, fun p' l' => ?_⟩
    exact (swap_incidence (rotate (rotate p')) (rotate (rotate l'))).trans
      ((rotate_incidence (rotate p') (rotate l')).trans (rotate_incidence p' l'))

theorem flagTransitive {p l : Fin 13} (h : incidence p l) :
    ∃ (σ τ : Equiv.Perm (Fin 13)), σ p = 0 ∧ τ l = 0 ∧
      ∀ p' l', incidence (σ p') (τ l') ↔ incidence p' l' := by
  have hp : translate p p = 0 := sub_self p
  have h0 : incidence 0 (translate p l) := hp ▸ (translate_incidence p p l).mpr h
  obtain ⟨σ, τ, hσ, hτ, hinc⟩ := normalize_from_zero h0
  refine ⟨(translate p).trans σ, (translate p).trans τ, ?_, hτ, ?_⟩
  · change σ (translate p p) = 0
    rwa [hp]
  · intro p' l'
    exact (hinc (translate p p') (translate p l')).trans (translate_incidence p p' l')

end PEqualNP.Outside.L_meta_4019.Flags

namespace PEqualNP.Outside.L_meta_4019.Flags

def combine (σ τ : Equiv.Perm (Fin 13)) : Equiv.Perm (Fin 26) :=
  (finSumFinEquiv : Fin 13 ⊕ Fin 13 ≃ Fin 26).symm.trans
    ((Equiv.sumCongr σ τ).trans finSumFinEquiv)

@[simp] theorem combine_point (σ τ : Equiv.Perm (Fin 13)) (p : Fin 13) :
    combine σ τ (Fin.castAdd 13 p) = Fin.castAdd 13 (σ p) := by
  let e : Fin 13 ⊕ Fin 13 ≃ Fin 26 := finSumFinEquiv
  change e ((Equiv.sumCongr σ τ) (e.symm (Fin.castAdd 13 p))) = _
  have h : e.symm (Fin.castAdd 13 p) = Sum.inl p := e.symm_apply_apply (Sum.inl p)
  rw [h]
  rfl

@[simp] theorem combine_line (σ τ : Equiv.Perm (Fin 13)) (l : Fin 13) :
    combine σ τ (Fin.natAdd 13 l) = Fin.natAdd 13 (τ l) := by
  let e : Fin 13 ⊕ Fin 13 ≃ Fin 26 := finSumFinEquiv
  change e ((Equiv.sumCongr σ τ) (e.symm (Fin.natAdd 13 l))) = _
  have h : e.symm (Fin.natAdd 13 l) = Sum.inr l := e.symm_apply_apply (Sum.inr l)
  rw [h]
  rfl

def selects (I : Fin 13 → Fin 13 → Prop) (x : Fin 26 → Bool) : Prop :=
  ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

theorem selects_comp (I : Fin 13 → Fin 13 → Prop) (σ τ : Equiv.Perm (Fin 13))
    (h : ∀ p l, I (σ p) (τ l) ↔ I p l) (x : Fin 26 → Bool) :
    selects I (x ∘ combine σ τ) ↔ selects I x := by
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨σ p, τ l, (h p l).mpr hi,
      by simpa only [Function.comp_apply, combine_point] using hp,
      by simpa only [Function.comp_apply, combine_line] using hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨σ.symm p, τ.symm l, ?_, ?_, ?_⟩
    · exact (h _ _).mp (by simpa using hi)
    · simpa only [Function.comp_apply, combine_point, Equiv.apply_symm_apply] using hp
    · simpa only [Function.comp_apply, combine_line, Equiv.apply_symm_apply] using hl

theorem singleton_comp (σ : Equiv.Perm (Fin 26)) (z : Fin 26) :
    (fun w => decide (w = σ z)) ∘ σ = fun w => decide (w = z) := by
  funext w
  simp

end PEqualNP.Outside.L_meta_4019.Flags

namespace PEqualNP.Outside.L_meta_4019

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

variable {n : Nat}

def mapWire (σ : Equiv.Perm (Fin n)) (i : Nat) : Nat :=
  if hi : i < n then (σ ⟨i, hi⟩).val else i

@[simp] theorem mapWire_fin (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    mapWire σ i.val = (σ i).val := by
  simp [mapWire, i.isLt]

theorem mapWire_eq_self (σ : Equiv.Perm (Fin n)) (i : Nat) (hi : n ≤ i) :
    mapWire σ i = i := by
  simp [mapWire, Nat.not_lt_of_ge hi]

theorem mapWire_lt (σ : Equiv.Perm (Fin n)) (i m : Nat) (hm : n ≤ m) :
    mapWire σ i < m ↔ i < m := by
  by_cases hi : i < n
  · have hσ := (σ ⟨i, hi⟩).isLt
    simp only [mapWire, dite_eq_left hi]
    omega
  · rw [mapWire_eq_self σ i (by omega)]

@[simp] theorem mapWire_symm_apply (σ : Equiv.Perm (Fin n)) (i : Nat) :
    mapWire σ.symm (mapWire σ i) = i := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change mapWire σ.symm (mapWire σ j.val) = j.val
    simp
  · rw [mapWire_eq_self σ i (by omega), mapWire_eq_self σ.symm i (by omega)]

theorem mapWire_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (mapWire σ) := by
  intro i j h
  simpa only [mapWire_symm_apply] using congrArg (mapWire σ.symm) h

def renameGate (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire σ)⟩

def rename (σ : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate σ), mapWire σ C.output⟩

@[simp] theorem renameGate_op (σ : Equiv.Perm (Fin n)) (g : Gate) :
    (renameGate σ g).op = g.op := rfl

@[simp] theorem renameGate_inputs (σ : Equiv.Perm (Fin n)) (g : Gate) :
    (renameGate σ g).inputs = g.inputs.map (mapWire σ) := rfl

@[simp] theorem rename_gates (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (rename σ C).gates = C.gates.map (renameGate σ) := rfl

@[simp] theorem rename_output (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (rename σ C).output = mapWire σ C.output := rfl

@[simp] theorem size_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (rename σ C).size = C.size := by simp [Circuit.size]

@[simp] theorem getGate_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (j : Nat) :
    (rename σ C).gates[j]? = (C.gates[j]?).map (renameGate σ) := by simp

theorem gateAt_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (j : Nat) :
    gateAt (rename σ C) j = renameGate σ (gateAt C j) := by
  let d : Gate := ⟨GateOp.or, []⟩
  change (C.gates.map (renameGate σ)).getD j (renameGate σ d) = renameGate σ (C.gates.getD j d)
  exact List.getD_map _ _ _

theorem isAO2_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 n (rename σ C) := by
  obtain ⟨hop, hback, hlen⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact hop g' hg'
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    rw [gateAt_rename, renameGate_inputs] at hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    exact (mapWire_lt σ i' (n + j) (Nat.le_add_right n j)).mpr (hback j hj' i' hi')
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa only [renameGate_inputs, List.length_map] using hlen g' hg'

theorem nodup_rename (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : ∀ g ∈ C.gates, g.inputs.Nodup) : ∀ g ∈ (rename σ C).gates, g.inputs.Nodup := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  exact List.Nodup.map (mapWire_injective σ) (h g' hg')

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_rename (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ (w w' : List Bool), w'.length = w.length → n ≤ w.length →
      (∀ i, w'.getD (mapWire σ i) false = w.getD i false) → ∀ i,
      ((gs.map (renameGate σ)).foldl step w').getD (mapWire σ i) false =
        (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl hn h
    simp only [List.map_cons, List.foldl_cons]
    have hv : (renameGate σ g).op.eval ((renameGate σ g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [renameGate_op, renameGate_inputs, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    refine ih _ _ (by simp [step, hl]) (by simp [step]; omega) ?_
    intro i
    simp only [step, hv]
    by_cases hi : i < w.length
    · have his : mapWire σ i < w'.length := by rw [hl]; exact (mapWire_lt σ i _ hn).mpr hi
      rw [List.getD_append _ _ _ _ his, List.getD_append _ _ _ _ hi, h i]
    · rw [mapWire_eq_self σ i (by omega), List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hl]

private theorem ofFn_getD (x : Fin n → Bool) (i : Nat) :
    (List.ofFn x).getD i false = if hi : i < n then x ⟨i, hi⟩ else false := by
  by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]

theorem wires_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) (i : Nat) :
    ((rename σ C).wires (List.ofFn x)).getD (mapWire σ i) false =
      (C.wires (List.ofFn (x ∘ σ))).getD i false := by
  apply fold_rename σ C.gates _ _ (by simp) (by simp)
  intro j
  rw [ofFn_getD, ofFn_getD]
  by_cases hj : j < n
  · let k : Fin n := ⟨j, hj⟩
    change (if h : mapWire σ k.val < n then x ⟨mapWire σ k.val, h⟩ else false) =
      (if h : k.val < n then (x ∘ σ) ⟨k.val, h⟩ else false)
    simp [k.isLt, (σ k).isLt]
  · rw [mapWire_eq_self σ j (by omega), dite_eq_right hj, dite_eq_right hj]

theorem wires_rename_symm (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) (i : Nat) :
    ((rename σ C).wires (List.ofFn (x ∘ σ.symm))).getD (mapWire σ i) false =
      (C.wires (List.ofFn x)).getD i false := by
  rw [wires_rename]
  have h : (x ∘ σ.symm) ∘ σ = x := by funext j; simp
  rw [h]

theorem eval_rename (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    (rename σ C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) :=
  wires_rename σ C x C.output

theorem eval_rename_symm (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    (rename σ C).eval (List.ofFn (x ∘ σ.symm)) = C.eval (List.ofFn x) :=
  wires_rename_symm σ C x C.output

end PEqualNP.Outside.L_meta_4019

namespace PEqualNP.Outside.L_meta_4019

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

local instance : DecidableEq GateOp := gateOpDecEq

private theorem coneInputs_rename (σ : Equiv.Perm (Fin 26)) (k : ℕ) (ws : List ℕ) :
    ((ws.map (mapWire σ)).filter (fun w => decide (26 ≤ w ∧ w < 26 + k))) =
      ws.filter (fun w => decide (26 ≤ w ∧ w < 26 + k)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    by_cases ha : 26 ≤ a
    · rw [List.map_cons, mapWire_eq_self σ a ha, List.filter_cons, List.filter_cons, ih]
    · have hlt : mapWire σ a < 26 := (mapWire_lt σ a 26 (by omega)).mpr (by omega)
      have hm : ¬ (26 ≤ mapWire σ a ∧ mapWire σ a < 26 + k) := fun h => by omega
      have hm' : ¬ (26 ≤ a ∧ a < 26 + k) := fun h => ha h.1
      rw [List.map_cons, List.filter_cons, List.filter_cons, decide_eq_false hm, decide_eq_false hm']
      exact ih

private theorem coneStep_rename (σ : Equiv.Perm (Fin 26)) (cs : List (List ℕ)) (g : Gate) :
    coneStep 26 cs (renameGate σ g) = coneStep 26 cs g := by
  unfold coneStep
  change cs ++ [((g.inputs.map (mapWire σ)).filter _).flatMap _] = _
  rw [coneInputs_rename]

private theorem coneFold_rename (σ : Equiv.Perm (Fin 26)) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.map (renameGate σ)).foldl (coneStep 26) cs = gs.foldl (coneStep 26) cs := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, List.foldl_cons, coneStep_rename, ih]

private theorem cones_rename (σ : Equiv.Perm (Fin 26)) (C : Circuit) :
    cones 26 (rename σ C) = cones 26 C := coneFold_rename σ C.gates []

theorem gateAt_rename_op (σ : Equiv.Perm (Fin 26)) (C : Circuit) (j : ℕ) :
    (gateAt (rename σ C) j).op = (gateAt C j).op := by
  rw [gateAt_rename]
  rfl

theorem andPairs_rename (σ : Equiv.Perm (Fin 26)) (C : Circuit) :
    PEqualNP.TopForm.andPairs 26 (rename σ C) = PEqualNP.TopForm.andPairs 26 C := by
  have hlen : (rename σ C).gates.length = C.gates.length := by simp [rename]
  unfold PEqualNP.TopForm.andPairs
  rw [hlen]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p _
  simp only [gateAt_rename_op, InCone, cones_rename]

def sensStep (C : Circuit) (active : Fin 26) (u v : ℕ) : Prop :=
  ∃ (j : ℕ) (g : Gate) (w : ℕ),
    v = 26 + j ∧ C.gates[j]? = some g ∧ (g.inputs = [u, w] ∨ g.inputs = [w, u]) ∧
      (g.op = .or ∨ g.op = .and ∧
        (C.wires (List.ofFn fun i : Fin 26 => decide (i = active))).getD w false = true)

private theorem singleton_pull (σ : Equiv.Perm (Fin 26)) (active : Fin 26) :
    (fun i : Fin 26 => decide (i = σ active)) ∘ σ = fun i => decide (i = active) := by
  funext i
  change decide (σ i = σ active) = decide (i = active)
  by_cases h : i = active
  · subst i
    simp
  · have hσ : σ i ≠ σ active := fun e => h (σ.injective e)
    simp [h, hσ]

private theorem singleton_value (σ : Equiv.Perm (Fin 26)) (C : Circuit) (active : Fin 26) (w : ℕ) :
    ((rename σ C).wires (List.ofFn fun i : Fin 26 => decide (i = σ active))).getD (mapWire σ w) false =
      (C.wires (List.ofFn fun i : Fin 26 => decide (i = active))).getD w false := by
  simpa only [singleton_pull] using wires_rename σ C (fun i => decide (i = σ active)) w

private theorem mapWire_apply_symm (σ : Equiv.Perm (Fin 26)) (i : ℕ) :
    mapWire σ (mapWire σ.symm i) = i := by
  simpa only [Equiv.symm_symm] using mapWire_symm_apply σ.symm i

private theorem sensStep_rename (σ : Equiv.Perm (Fin 26)) (C : Circuit) (active : Fin 26)
    (u v : ℕ) : sensStep (rename σ C) (σ active) (mapWire σ u) (mapWire σ v) ↔ sensStep C active u v := by
  constructor
  · rintro ⟨j, g', w', hv', hg', hreads', hop'⟩
    have hj : mapWire σ (26 + j) = 26 + j := mapWire_eq_self σ _ (by omega)
    have hv : v = 26 + j := mapWire_injective σ (hv'.trans hj.symm)
    obtain ⟨g, hg, rfl⟩ : ∃ g, C.gates[j]? = some g ∧ renameGate σ g = g' := by
      cases h : C.gates[j]? with
      | none => simp [h] at hg'
      | some g =>
        exact ⟨g, rfl, Option.some.inj (by simpa only [getGate_rename, h, Option.map_some] using hg')⟩
    let w := mapWire σ.symm w'
    have hw : mapWire σ w = w' := mapWire_apply_symm σ w'
    refine ⟨j, g, w, hv, hg, ?_, ?_⟩
    · have hinj : Function.Injective (List.map (mapWire σ)) :=
        List.map_injective_iff.mpr (mapWire_injective σ)
      rcases hreads' with e | e
      · exact Or.inl (hinj (show g.inputs.map (mapWire σ) = [u, w].map (mapWire σ) by simpa [renameGate, hw] using e))
      · exact Or.inr (hinj (show g.inputs.map (mapWire σ) = [w, u].map (mapWire σ) by simpa [renameGate, hw] using e))
    · rw [← hw] at hop'
      simpa only [renameGate, singleton_value] using hop'
  · rintro ⟨j, g, w, rfl, hg, hreads, hop⟩
    refine ⟨j, renameGate σ g, mapWire σ w, mapWire_eq_self σ _ (by omega), ?_, ?_, ?_⟩
    · simp only [getGate_rename, hg, Option.map_some]
    · rcases hreads with e | e
      · exact Or.inl (by simp [renameGate, e])
      · exact Or.inr (by simp [renameGate, e])
    · simpa only [renameGate, singleton_value] using hop

theorem sensReach_rename (σ : Equiv.Perm (Fin 26)) (C : Circuit) (active : Fin 26) (u v : ℕ) :
    Relation.ReflTransGen (sensStep (rename σ C) (σ active)) (mapWire σ u) (mapWire σ v) ↔
      Relation.ReflTransGen (sensStep C active) u v := by
  constructor
  · intro h
    have hp : ∀ a b, sensStep (rename σ C) (σ active) a b →
        sensStep C active (mapWire σ.symm a) (mapWire σ.symm b) := by
      intro a b hab
      apply (sensStep_rename σ C active _ _).mp
      simpa only [mapWire_apply_symm] using hab
    have hh : Relation.ReflTransGen (sensStep C active)
        (mapWire σ.symm (mapWire σ u)) (mapWire σ.symm (mapWire σ v)) :=
      Relation.ReflTransGen.lift (mapWire σ.symm) hp _ _ h
    simpa only [mapWire_symm_apply] using hh
  · intro h
    exact Relation.ReflTransGen.lift (mapWire σ)
      (fun a b hab => (sensStep_rename σ C active a b).mpr hab) _ _ h

end PEqualNP.Outside.L_meta_4019

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4019.Flags PEqualNP.Outside.L_meta_4019

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.L_meta_4019 :
have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 - x6 ∈ x2 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧ ∃ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : Fin (26 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD ((26 : ℕ) + x4) Bool.false = Bool.true ∧ x3.eval (List.ofFn x5) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)), x3 x4 → x5 - x6 ∈ x2 → ¬Relation.ReflTransGen (x1 x4 (Fin.castAdd (13 : ℕ) x5)) ((13 : ℕ) + ↑x6) x4.output → ¬Relation.ReflTransGen (x1 x4 (Fin.natAdd (13 : ℕ) x6)) (↑x5) x4.output → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x3 x11 ∧ ¬Relation.ReflTransGen (x1 x11 (0 : Fin (26 : ℕ))) (13 : ℕ) x11.output ∧ ¬Relation.ReflTransGen (x1 x11 (13 : Fin (26 : ℕ))) (0 : ℕ) x11.output
:= by
  intro step D ok C p l hC hinc hpoint hline
  dsimp only [ok, D] at hC hinc ⊢
  obtain ⟨hsize, hao, hnodup, heval, hnested, k, hk, hop, x, htrue, hfalse⟩ := hC
  obtain ⟨σ, τ, hσ, hτ, hincPres⟩ := flagTransitive (show incidence p l from hinc)
  let π := combine σ τ
  have hπp : π (Fin.castAdd 13 p) = (0 : Fin 26) := by
    dsimp [π]
    rw [combine_point, hσ] <;> rfl
  have hπl : π (Fin.natAdd 13 l) = (13 : Fin 26) := by
    dsimp [π]
    rw [combine_line, hτ] <;> rfl
  have hmapP : mapWire π p.val = 0 := by
    have h := mapWire_fin π (Fin.castAdd 13 p)
    simpa [Fin.val_castAdd, hπp] using h
  have hmapL : mapWire π (13 + l.val) = 13 := by
    have h := mapWire_fin π (Fin.natAdd 13 l)
    rw [hπl] at h
    simpa [Fin.val_natAdd, Nat.add_comm] using h
  refine ⟨rename π C, ?_, ?_, ?_⟩
  · refine ⟨by rwa [size_rename], isAO2_rename π C hao, nodup_rename π C hnodup,
        ?_, by rwa [andPairs_rename], ?_⟩
    · intro y
      rw [eval_rename]
      exact (heval (y ∘ π)).trans (selects_comp incidence σ τ hincPres y)
    · refine ⟨k, ?_, ?_, x ∘ π.symm, ?_, ?_⟩
      · change k < (rename π C).size
        change k < C.size at hk
        rwa [size_rename]
      · rw [gateAt_rename_op]
        exact hop
      · have hx : (x ∘ π.symm) ∘ π = x := by
          funext z
          simp
        have hw := wires_rename π C (x ∘ π.symm) (26 + k)
        rw [mapWire_eq_self _ _ (by omega), hx] at hw
        exact hw.trans htrue
      · have hx : (x ∘ π.symm) ∘ π = x := by
          funext z
          simp
        rwa [eval_rename, hx]
  · intro h
    apply hpoint
    change Relation.ReflTransGen (sensStep C (Fin.castAdd 13 p)) (13 + l.val) C.output
    apply (sensReach_rename π C (Fin.castAdd 13 p) (13 + l.val) C.output).mp
    rw [hπp, hmapL]
    exact h
  · intro h
    apply hline
    change Relation.ReflTransGen (sensStep C (Fin.natAdd 13 l)) p.val C.output
    apply (sensReach_rename π C (Fin.natAdd 13 l) p.val C.output).mp
    rw [hπl, hmapP]
    exact h
