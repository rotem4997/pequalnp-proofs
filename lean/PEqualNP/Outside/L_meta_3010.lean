import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds

-- relabel input wires below 14 by a permutation, keep gate wires
def piN (τ : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ := if h : i < 14 then ((τ ⟨i, h⟩ : Fin 14) : ℕ) else i

def renG (τ : Equiv.Perm (Fin 14)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (piN τ)⟩

def ren (τ : Equiv.Perm (Fin 14)) (C : Circuit) : Circuit := ⟨C.gates.map (renG τ), piN τ C.output⟩

def K (p q r s : ℕ) : ℕ := (15 * min p q + max p q) * 225 + (15 * min r s + max r s)

theorem piN_lt (τ : Equiv.Perm (Fin 14)) (i m : ℕ) (hm : 14 ≤ m) : piN τ i < m ↔ i < m := by
  unfold piN
  by_cases hi : i < 14
  · rw [dif_pos hi]
    have := (τ ⟨i, hi⟩).isLt
    constructor <;> intro _ <;> omega
  · rw [dif_neg hi]

theorem piN_eq_self (τ : Equiv.Perm (Fin 14)) (i : ℕ) (h : 14 ≤ i) : piN τ i = i := by
  unfold piN; rw [dif_neg (by omega)]

theorem piN_of_lt (τ : Equiv.Perm (Fin 14)) (i : ℕ) (h : i < 14) : piN τ i = ((τ ⟨i, h⟩ : Fin 14) : ℕ) := by
  unfold piN; rw [dif_pos h]

theorem piN_inj (τ : Equiv.Perm (Fin 14)) {i j : ℕ} (h : piN τ i = piN τ j) : i = j := by
  by_cases hi : i < 14 <;> by_cases hj : j < 14
  · rw [piN_of_lt τ i hi, piN_of_lt τ j hj] at h
    have := τ.injective (Fin.ext h)
    exact congrArg Fin.val this
  · rw [piN_of_lt τ i hi, piN_eq_self τ j (by omega)] at h
    have := (τ ⟨i, hi⟩).isLt; omega
  · rw [piN_eq_self τ i (by omega), piN_of_lt τ j hj] at h
    have := (τ ⟨j, hj⟩).isLt; omega
  · rw [piN_eq_self τ i (by omega), piN_eq_self τ j (by omega)] at h
    exact h

theorem piN_mul (σ τ : Equiv.Perm (Fin 14)) (i : ℕ) : piN (σ * τ) i = piN σ (piN τ i) := by
  by_cases hi : i < 14
  · rw [piN_of_lt (σ * τ) i hi, piN_of_lt τ i hi, piN_of_lt σ _ (τ ⟨i, hi⟩).isLt]
    simp [Equiv.Perm.mul_apply]
  · rw [piN_eq_self (σ * τ) i (by omega), piN_eq_self τ i (by omega), piN_eq_self σ i (by omega)]

theorem x9_eq (σ : Equiv.Perm (Fin 14)) (m : ℕ) (hm : m < 15) :
    (if m < 14 then ((σ (Fin.ofNat 14 m) : Fin 14) : ℕ) else 14) = piN σ m := by
  by_cases h : m < 14
  · rw [if_pos h, piN_of_lt σ m h]
    have : (Fin.ofNat 14 m : Fin 14) = ⟨m, h⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt h])
    rw [this]
  · rw [if_neg h, piN_eq_self σ m (by omega)]; omega

theorem K_mm0 (p q r s : ℕ) : K (min p q) (max p q) (min r s) (max r s) = K p q r s := by
  unfold K; omega

theorem K_mm (f : ℕ → ℕ) (p q r s : ℕ) :
    K (f (min p q)) (f (max p q)) (f (min r s)) (f (max r s)) = K (f p) (f q) (f r) (f s) := by
  unfold K
  rcases le_total p q with h | h <;> rcases le_total r s with h' | h' <;>
    simp only [min_eq_left h, max_eq_right h, min_eq_right h, max_eq_left h, min_eq_left h',
      max_eq_right h', min_eq_right h', max_eq_left h'] <;> omega

theorem op_mm (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (W : List Bool) (A B : ℕ) :
    op.eval [W.getD (min A B) false, W.getD (max A B) false] = op.eval [W.getD A false, W.getD B false] := by
  rcases le_total A B with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

theorem getD_ofFn_lt (y : Fin 14 → Bool) (m : ℕ) (h : m < 14) : (List.ofFn y).getD m false = y ⟨m, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h), List.getElem_ofFn]

theorem getD_ofFn14 (y : Fin 14 → Bool) (i : ℕ) :
    (List.ofFn y).getD i false = if h : i < 14 then y ⟨i, h⟩ else false := by
  by_cases h : i < 14
  · rw [dif_pos h, getD_ofFn_lt y i h]
  · rw [dif_neg h]; simp [List.getD_eq_getElem?_getD, h]

theorem fold_ren (τ : Equiv.Perm (Fin 14)) (gs : List Gate) : ∀ (w w' : List Bool), w'.length = w.length →
    14 ≤ w.length → (∀ i, w'.getD (piN τ i) false = w.getD i false) →
    ∀ i, ((gs.map (renG τ)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD
        (piN τ i) false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' hl h14 h
    simp only [List.map_cons, List.foldl_cons]
    have hv : (renG τ g).op.eval ((renG τ g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [renG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    refine ih _ _ ?_ ?_ ?_
    · simp [hl]
    · simp; omega
    · intro i
      rw [hv]
      by_cases hi : i < w.length
      · have hpi : piN τ i < w'.length := by rw [hl]; exact (piN_lt τ i w.length h14).mpr hi
        rw [List.getD_append _ _ _ _ hpi, List.getD_append _ _ _ _ hi, h i]
      · have hpe : piN τ i = i := piN_eq_self τ i (by omega)
        rw [hpe, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

theorem eval_ren (τ : Equiv.Perm (Fin 14)) (C : Circuit) (y : Fin 14 → Bool) :
    (ren τ C).eval (List.ofFn y) = C.eval (List.ofFn (y ∘ τ)) := by
  unfold Circuit.eval Circuit.wires
  exact fold_ren τ C.gates (List.ofFn (y ∘ τ)) (List.ofFn y) (by simp) (by simp) (fun i => by
      rw [getD_ofFn14, getD_ofFn14]
      by_cases h : i < 14
      · rw [dif_pos h, piN_of_lt τ i h, dif_pos (τ ⟨i, h⟩).isLt]
        simp
      · rw [dif_neg h, piN_eq_self τ i (by omega), dif_neg h]) C.output

end PEqualNP.Outside.L_meta_3010

open PEqualNP.Outside.L_meta_3010 in
theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro x1 C hAO hnd h2 h26 hC
  dsimp only
  classical
  obtain ⟨hand, hrb, hlen⟩ := hAO
  obtain ⟨g0, g1, rest, hg⟩ : ∃ g0 g1 rest, C.gates = g0 :: g1 :: rest := by
    rcases hgs : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgs] at h2
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgs] at h2
    · exact ⟨g0, g1, rest, rfl⟩
  have hm0 : g0 ∈ C.gates := by simp [hg]
  have hm1 : g1 ∈ C.gates := by simp [hg]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hlen g0 hm0)
  obtain ⟨c, d, hcd⟩ := List.length_eq_two.mp (hlen g1 hm1)
  have ha : a < 14 := by
    have := hrb 0 (by simp [hg]) a (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg, hab]); omega
  have hb : b < 14 := by
    have := hrb 0 (by simp [hg]) b (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg, hab]); omega
  have hc : c < 15 := by
    have := hrb 1 (by simp [hg]) c (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg, hcd]); omega
  have hd : d < 15 := by
    have := hrb 1 (by simp [hg]) d (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg, hcd]); omega
  have hab' : a ≠ b := by
    have := hnd g0 hm0; rw [hab] at this; simpa using this
  have hcd' : c ≠ d := by
    have := hnd g1 hm1; rw [hcd] at this; simpa using this
  have hop0 := hand g0 hm0
  have hop1 := hand g1 hm1
  let S : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun τ => ∀ y : Fin 14 → Bool, x1 (y ∘ τ) = x1 y)
  have hS : S.Nonempty := ⟨1, by simp [S]⟩
  obtain ⟨τ, hτS, hτmin⟩ := S.exists_min_image
    (fun τ => K (piN τ a) (piN τ b) (piN τ c) (piN τ d)) hS
  have hτ : ∀ y : Fin 14 → Bool, x1 (y ∘ τ) = x1 y := (Finset.mem_filter.mp hτS).2
  have hA : piN τ a < 14 := (piN_lt τ a 14 le_rfl).mpr ha
  have hB : piN τ b < 14 := (piN_lt τ b 14 le_rfl).mpr hb
  have hC' : piN τ c < 15 := (piN_lt τ c 15 (by norm_num)).mpr hc
  have hD : piN τ d < 15 := (piN_lt τ d 15 (by norm_num)).mpr hd
  have hAB : piN τ a ≠ piN τ b := fun h => hab' (piN_inj τ h)
  have hCD : piN τ c ≠ piN τ d := fun h => hcd' (piN_inj τ h)
  have h1 : min (piN τ a) (piN τ b) < 14 := by omega
  have h2' : max (piN τ a) (piN τ b) < 14 := by omega
  have h3 : min (piN τ c) (piN τ d) < 15 := by omega
  have h4 : max (piN τ c) (piN τ d) < 15 := by omega
  refine ⟨⟨_, h1⟩, ⟨_, h2'⟩, ⟨_, h3⟩, ⟨_, h4⟩, g0.op, g1.op,
    ⟨rest.map (renG τ), piN τ C.output⟩, ?_, ?_, hop0, hop1, ?_, ?_, ?_, ?_⟩
  · rw [Fin.mk_lt_mk]; omega
  · rw [Fin.mk_lt_mk]; omega
  · intro σ hσ
    have hστ : σ * τ ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro y
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ, hσ]
    have hm := hτmin (σ * τ) hστ
    simp only [piN_mul] at hm
    have key : K (min (piN τ a) (piN τ b)) (max (piN τ a) (piN τ b)) (min (piN τ c) (piN τ d))
        (max (piN τ c) (piN τ d)) ≤ K (piN σ (min (piN τ a) (piN τ b))) (piN σ (max (piN τ a) (piN τ b)))
        (piN σ (min (piN τ c) (piN τ d))) (piN σ (max (piN τ c) (piN τ d))) := by
      rw [K_mm0, K_mm (piN σ)]; exact hm
    rw [piN_of_lt σ _ h1, piN_of_lt σ _ h2', ← x9_eq σ _ h3, ← x9_eq σ _ h4] at key
    exact key
  · unfold PEqualNP.MetaComplexity.Monotone2
    intro g hgm
    simp only [List.mem_map] at hgm
    obtain ⟨g', hg'm, rfl⟩ := hgm
    have hm : g' ∈ C.gates := by rw [hg]; simp [hg'm]
    refine ⟨?_, ?_⟩
    · rcases hand g' hm with h | h <;> simp [renG, h]
    · simp [renG, hlen g' hm]
  · have : C.gates.length ≤ 26 := h26
    rw [hg] at this
    show (rest.map (renG τ)).length ≤ 24
    simp at this ⊢; omega
  · intro y
    have hE : (ren τ C).eval (List.ofFn y) = x1 y := by rw [eval_ren, hC, hτ]
    have hsplit : (ren τ C).eval (List.ofFn y) =
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨rest.map (renG τ), piN τ C.output⟩
          ((List.ofFn y ++ [g0.op.eval ((g0.inputs.map (piN τ)).map fun i => (List.ofFn y).getD i false)]) ++
            [g1.op.eval ((g1.inputs.map (piN τ)).map fun i =>
              (List.ofFn y ++ [g0.op.eval ((g0.inputs.map (piN τ)).map fun i =>
                (List.ofFn y).getD i false)]).getD i false)]) := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires ren
      rw [hg]; rfl
    rw [hab, hcd] at hsplit
    simp only [List.map_cons, List.map_nil] at hsplit
    rw [← hE, hsplit, ← getD_ofFn_lt y _ h1, ← getD_ofFn_lt y _ h2', op_mm g0.op hop0, op_mm g1.op hop1]
