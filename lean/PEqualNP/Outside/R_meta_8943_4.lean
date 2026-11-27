import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_8943_4
    (hCovered : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      IsLeastAO G C → ∀ σ : Equiv.Perm (Fin 13), (∀ p : Fin 13, G.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 (σ p))) →
      (List.finRange 13).countP (fun p => !(decide (s(Fin.castAdd 13 p, Fin.natAdd 13 (σ p)) ∈ Ustar G C))) ≤ (tops G C \ centreless G C).card)
    (hResidual : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 63 →
      52 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 →
      (∀ σ : Equiv.Perm (Fin 13), (∀ p : Fin 13, G.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 (σ p))) →
        13 ≤ (tops G C \ centreless G C).card + (List.finRange 13).countP (fun p => decide (s(Fin.castAdd 13 p, Fin.natAdd 13 (σ p)) ∈ Ustar G C))) → False) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → x3.size ≤ (63 : ℕ) → (52 : ℕ) + (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + (PEqualNP.TopForm.Ustar x1 x3).card + (1 : ℕ) → (52 : ℕ) ≤ (4 : ℕ) * (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.Ustar x1 x3).card → (4 : ℕ) * ((PEqualNP.TopForm.junk x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) + (4 : ℕ) ≤ (5 : ℕ) * (PEqualNP.TopForm.Ustar x1 x3).card → False := by
  intro G inst C hG hLeast hTop hJunk hSize hCharge _ _
  apply hResidual G C hG hLeast hTop hJunk hSize hCharge
  intro σ hMatching
  have hcovered := hCovered G C hG hLeast σ hMatching
  let f : Fin 13 → Bool := fun p => decide (s(Fin.castAdd 13 p, Fin.natAdd 13 (σ p)) ∈ Ustar G C)
  change (List.finRange 13).countP (fun p => !f p) ≤ (tops G C \ centreless G C).card at hcovered
  change 13 ≤ (tops G C \ centreless G C).card + (List.finRange 13).countP f
  have partition : ∀ xs : List (Fin 13),
      xs.countP f + xs.countP (fun p => !f p) = xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons p xs ih =>
      cases h : f p <;> simp [List.countP_cons, h] <;> omega
  have hcount := partition (List.finRange 13)
  have hlength : (List.finRange 13).length = 13 := by decide
  omega
