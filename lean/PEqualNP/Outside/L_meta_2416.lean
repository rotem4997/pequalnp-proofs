import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2416

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

theorem eval_mono2 (C : Circuit) (mono : Monotone2 C) {n : ℕ} (x y : Fin n → Bool)
    (hle : ∀ k, x k = true → y k = true) (hx : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn y) = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (mono g hg).1
    simpa using h
  refine wiresFrom_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) ?_
    C.output hx
  intro j hj
  by_cases hjlt : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjlt)] at hj ⊢
    simp only [List.getElem_ofFn] at hj ⊢
    exact hle ⟨j, hjlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

theorem far : ∀ l0 l : Fin 13, l ≠ l0 →
    ∃ p : Fin 13, (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d) ∧
      ¬ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l0 + d := by
  decide +kernel

theorem split26 : ∀ k : Fin 26, (∃ p : Fin 13, k = Fin.castAdd 13 p) ∨
    ∃ j : Fin 13, k = Fin.natAdd 13 j := by
  decide +kernel

theorem core (x1 : Finset (Fin (13 : ℕ))) (hx1 : x1 = {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}) : let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; have x6 : (Fin (26 : ℕ) → Bool) → Prop := fun (x6 : Fin (26 : ℕ) → Bool) => ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (∃ x9 ∈ x1, x7 = x8 + x9) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x4 x7 → ∀ (x10 : Fin (26 : ℕ) → Bool), x5 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 x10 = Bool.true ↔ x6 x10) := by
  subst hx1
  intro x2 x3 x4 x5 x6 C mono h4 x hx5
  obtain ⟨pos, rej⟩ := h4
  obtain ⟨l0, hl0⟩ := hx5
  constructor
  · intro hC
    have hC2 : C.eval (List.ofFn x) = true := hC
    by_contra hno
    have hno2 : ∀ p l : Fin 13, x2 p l → x (Fin.castAdd 13 p) = true →
        x (Fin.natAdd 13 l) = true → False :=
      fun p l h a b => hno ⟨p, l, h, a, b⟩
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 13),
        ∀ p, p ∈ S ↔ ¬ (x (Fin.natAdd 13 l0) = true ∧ x2 p l0) := by
      classical
      exact ⟨Finset.univ.filter (fun p => ¬ (x (Fin.natAdd 13 l0) = true ∧ x2 p l0)),
        fun p => by
          rw [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ p, h⟩⟩⟩
    have hclosed : ∀ q ∉ S, ∃ l : Fin 13, x3 S l ∧ x2 q l := by
      intro q hq
      have hq2 : x (Fin.natAdd 13 l0) = true ∧ x2 q l0 := by
        by_contra h
        exact hq ((hS q).mpr h)
      exact ⟨l0, fun p hp hinc => (hS p).mp hp ⟨hq2.1, hinc⟩, hq2.2⟩
    have hdeg : ∃ r : Fin 13, ∀ l : Fin 13, x3 S l → x2 r l := by
      refine ⟨l0, fun l hl => ?_⟩
      by_cases e : l = l0
      · rw [e]
        exact ⟨0, by decide, (add_zero l0).symm⟩
      · obtain ⟨p, hpl, hpn⟩ := far l0 l e
        exact absurd hpl (hl p ((hS p).mpr fun h => hpn h.2))
    have hrej := rej S hclosed (Or.inr hdeg)
    refine Bool.noConfusion (hrej.symm.trans (eval_mono2 C mono x _ ?_ hC2))
    intro k
    rcases split26 k with ⟨p, rfl⟩ | ⟨j, rfl⟩
    · intro hk
      exact decide_eq_true (Or.inl ⟨p, (hS p).mpr (fun h => hno2 p l0 h.2 hk h.1), rfl⟩)
    · intro hk
      have hj := hl0 j hk
      subst hj
      exact decide_eq_true (Or.inr ⟨j, rfl, fun q hq hinc => (hS q).mp hq ⟨hk, hinc⟩⟩)
  · intro h6
    obtain ⟨p, l, hinc, hp, hl⟩ := h6
    show C.eval (List.ofFn x) = true
    refine eval_mono2 C mono _ x ?_ (pos p l hinc)
    intro k hk
    rcases of_decide_eq_true hk with h | h
    · rw [h]; exact hp
    · rw [h]; exact hl

end PEqualNP.Outside.L_meta_2416

theorem PEqualNP.Outside.L_meta_2416 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; have x6 : (Fin (26 : ℕ) → Bool) → Prop := fun (x6 : Fin (26 : ℕ) → Bool) => ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (∃ x9 ∈ x1, x7 = x8 + x9) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x4 x7 → ∀ (x10 : Fin (26 : ℕ) → Bool), x5 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 x10 = Bool.true ↔ x6 x10) := by
  intro x1
  exact PEqualNP.Outside.L_meta_2416.core x1 rfl
