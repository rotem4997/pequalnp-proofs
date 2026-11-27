import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5849

def E : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]

def P2 (x2 : Fin (14 : ℕ) → Bool) : Prop :=
  ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ E ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true

theorem noloop : ∀ u : Fin 14, ((u : ℕ), (u : ℕ)) ∉ E := by decide

theorem crit (a b : Fin 14) (hab : ((a : ℕ), (b : ℕ)) ∈ E) :
    P2 (fun i : Fin 14 => decide (i = a ∨ i = b)) ∧ ∀ (x4 : Fin (14 : ℕ)),
      (fun i : Fin 14 => decide (i = a ∨ i = b)) x4 = Bool.true →
      ¬P2 (Function.update (fun i : Fin 14 => decide (i = a ∨ i = b)) x4 Bool.false) := by
  refine ⟨⟨a, b, hab, by simp, by simp⟩, ?_⟩
  intro x4 hx4
  rintro ⟨u, v, huv, hu, hv⟩
  have hx : x4 = a ∨ x4 = b := by simpa using hx4
  have hu' : u ≠ x4 ∧ (u = a ∨ u = b) := by
    rw [Function.update_apply] at hu
    split_ifs at hu with hh
    exact ⟨hh, by simpa using hu⟩
  have hv' : v ≠ x4 ∧ (v = a ∨ v = b) := by
    rw [Function.update_apply] at hv
    split_ifs at hv with hh
    exact ⟨hh, by simpa using hv⟩
  have key : u = v := by
    obtain ⟨hu1, hu2⟩ := hu'
    obtain ⟨hv1, hv2⟩ := hv'
    rcases hx with h | h <;> rcases hu2 with h2 | h2 <;> rcases hv2 with h3 | h3 <;>
      first
        | exact h2.trans h3.symm
        | exact absurd (h2.trans h.symm) hu1
        | exact absurd (h3.trans h.symm) hv1
  subst key
  exact noloop u huv

theorem c1 : (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [(fun i : Fin 14 => decide (i = 0 ∨ i = 7)) (0 : Fin (14 : ℕ)), (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) (1 : Fin (14 : ℕ))]]) = [true, false, false, false, false, false, false, true, false, false, false, false, false, false, true] := by decide +kernel

theorem c2 : (List.ofFn (fun i : Fin 14 => decide (i = 1 ∨ i = 9)) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [(fun i : Fin 14 => decide (i = 1 ∨ i = 9)) (0 : Fin (14 : ℕ)), (fun i : Fin 14 => decide (i = 1 ∨ i = 9)) (1 : Fin (14 : ℕ))]]) = [false, true, false, false, false, false, false, false, false, true, false, false, false, false, true] := by decide +kernel

theorem c3 : (List.ofFn (fun i : Fin 14 => decide (i = 2 ∨ i = 8)) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [(fun i : Fin 14 => decide (i = 2 ∨ i = 8)) (0 : Fin (14 : ℕ)), (fun i : Fin 14 => decide (i = 2 ∨ i = 8)) (1 : Fin (14 : ℕ))]]) = [false, false, true, false, false, false, false, false, true, false, false, false, false, false, false] := by decide +kernel

theorem fin (o : ℕ) (h1 : [true, false, false, false, false, false, false, true, false, false, false, false, false, false, true].getD o false = true) (h2 : [false, true, false, false, false, false, false, false, false, true, false, false, false, false, true].getD o false = true)
    (h3 : [false, false, true, false, false, false, false, false, true, false, false, false, false, false, false].getD o false = true) : False := by
  by_cases ho : o < 15
  · interval_cases o <;> simp at h1 h2 h3
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h1
    exact Bool.false_ne_true h1

theorem ev (x4 : PEqualNP.CircuitLowerBounds.Circuit) (hg : x4.gates = []) (l : List Bool) :
    x4.eval l = l.getD x4.output false := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [hg]
  rfl

end PEqualNP.Outside.L_meta_5849

theorem PEqualNP.Outside.L_meta_5849 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.gates = [] → (∀ (x7 : Fin (14 : ℕ) → Bool), x3 x7 → (x4.eval (List.ofFn x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x7 (0 : Fin (14 : ℕ)), x7 (1 : Fin (14 : ℕ))]]) = Bool.true ↔ x2 x7)) → (26 : ℕ) ≤ x4.size := by
  dsimp only
  intro x4 hm hg h
  exfalso
  have h1 := (h (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) (Or.inl (PEqualNP.Outside.L_meta_5849.crit 0 7 (by decide)))).mpr (PEqualNP.Outside.L_meta_5849.crit 0 7 (by decide)).1
  have h2 := (h (fun i : Fin 14 => decide (i = 1 ∨ i = 9)) (Or.inl (PEqualNP.Outside.L_meta_5849.crit 1 9 (by decide)))).mpr (PEqualNP.Outside.L_meta_5849.crit 1 9 (by decide)).1
  have h3 := (h (fun i : Fin 14 => decide (i = 2 ∨ i = 8)) (Or.inl (PEqualNP.Outside.L_meta_5849.crit 2 8 (by decide)))).mpr (PEqualNP.Outside.L_meta_5849.crit 2 8 (by decide)).1
  rw [PEqualNP.Outside.L_meta_5849.ev x4 hg, PEqualNP.Outside.L_meta_5849.c1] at h1
  rw [PEqualNP.Outside.L_meta_5849.ev x4 hg, PEqualNP.Outside.L_meta_5849.c2] at h2
  rw [PEqualNP.Outside.L_meta_5849.ev x4 hg, PEqualNP.Outside.L_meta_5849.c3] at h3
  exact PEqualNP.Outside.L_meta_5849.fin _ h1 h2 h3
