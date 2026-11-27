import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3268_1
    (separation :
      have read : (Fin 17 → (Fin 9 → Bool) → Bool) → (Bool ⊕ Fin 17) → (Fin 9 → Bool) → Bool :=
        fun z a x => Sum.elim id (fun j => z j x) a
      have good : (Fin 17 → (Fin 9 → Bool) → Bool) → Fin 17 → Prop := fun z i =>
        ∃ a b : Bool ⊕ Fin 17, (∀ j : Fin 17, a = Sum.inr j ∨ b = Sum.inr j → j < i) ∧
          ((∀ x, z i x = (read z a x && read z b x)) ∨ (∀ x, z i x = (read z a x || read z b x)))
      have edge : (Fin 9 → Bool) → Bool := fun x => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ z : Fin 17 → (Fin 9 → Bool) → Bool,
        (∀ (i : Fin 9) x, z (Fin.castAdd 8 i) x = x i) →
        (∀ x, z 9 x = (x 0 || x 2)) →
        (∀ i : Fin 17, 9 < (i : ℕ) → good z i) →
        ∀ S : Finset (Fin 17), S.card ≤ 6 →
          ∃ x y : Fin 9 → Bool, (∀ i ∈ S, z i x = z i y) ∧ edge x ≠ edge y)
    (representation :
      have read : (Fin 17 → (Fin 9 → Bool) → Bool) → (Bool ⊕ Fin 17) → (Fin 9 → Bool) → Bool :=
        fun z a x => Sum.elim id (fun j => z j x) a
      have good : (Fin 17 → (Fin 9 → Bool) → Bool) → Fin 17 → Prop := fun z i =>
        ∃ a b : Bool ⊕ Fin 17, (∀ j : Fin 17, a = Sum.inr j ∨ b = Sum.inr j → j < i) ∧
          ((∀ x, z i x = (read z a x && read z b x)) ∨ (∀ x, z i x = (read z a x || read z b x)))
      ∀ C : Circuit, Monotone2 C → C.size = 8 →
        ∀ i : Fin 17, 9 < (i : ℕ) → good (fun j x => (C.wires (List.ofFn x)).getD j.val false) i) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size = (8 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∀ (x6 : Finset ℕ), x6.card ≤ (6 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool) (x9 : Fin (9 : ℕ) → Bool), (∀ x10 ∈ x6, (x2.wires (List.ofFn x8)).getD x10 Bool.false = (x2.wires (List.ofFn x9)).getD x10 Bool.false) ∧ x1 x8 ≠ x1 x9 := by
  dsimp only
  intro C hC hs hfirst F hF
  let z (i : Fin 17) (x : Fin 9 → Bool) := (C.wires (List.ofFn x)).getD i.val false
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have foldLength (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have foldPrefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have raw (i : Fin 9) (x : Fin 9 → Bool) : z (Fin.castAdd 8 i) x = x i := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false = _
    rw [foldPrefix _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  have outside (i : ℕ) (hi : 17 ≤ i) (x : Fin 9 → Bool) :
      (C.wires (List.ofFn x)).getD i false = false := by
    apply List.getD_eq_default
    change (C.gates.foldl step (List.ofFn x)).length ≤ i
    rw [foldLength, List.length_ofFn]
    change C.gates.length = 8 at hs
    omega
  let bounded := F.filter (fun i => i < 17)
  let toFin (i : {i // i ∈ bounded}) : Fin 17 := ⟨i.val, (Finset.mem_filter.mp i.property).2⟩
  let S := bounded.attach.image toFin
  have hS : S.card ≤ 6 := calc
    S.card ≤ bounded.attach.card := Finset.card_image_le
    _ = bounded.card := Finset.card_attach
    _ ≤ F.card := Finset.card_filter_le _ _
    _ ≤ 6 := hF
  obtain ⟨x, y, hsame, hdiff⟩ :=
    separation z raw hfirst (representation C hC hs) S hS
  refine ⟨x, y, ?_, hdiff⟩
  intro i hi
  by_cases hb : i < 17
  · have hbi : i ∈ bounded := Finset.mem_filter.mpr ⟨hi, hb⟩
    let p : {i // i ∈ bounded} := ⟨i, hbi⟩
    exact hsame (toFin p) (Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩)
  · rw [outside _ (Nat.le_of_not_lt hb), outside _ (Nat.le_of_not_lt hb)]
