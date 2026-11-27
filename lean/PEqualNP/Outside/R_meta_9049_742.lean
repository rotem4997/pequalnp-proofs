import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_9049_742
    (profiles :
      let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      let U := Ustar G C
      let A := (tops G C \ centreless G C).card
      let shifts : Finset (Fin 13) := {0,1,3,9}
      let loss (d : Fin 13) := (U ∩ (Finset.univ.image fun p : Fin 13 =>
        s(Fin.castAdd 13 p, Fin.natAdd 13 (d-p)))).card
      (∀ d ∈ shifts, 13 ≤ A + loss d) ∧ ∃ d ∈ shifts, 4 * loss d ≤ U.card)
    (low : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ (3 : ℕ) → (64 : ℕ) ≤ x3.size)
    (hard :
      let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size ≤ 63 →
      let U := Ustar G C
      let A := (tops G C \ centreless G C).card
      let J := (junk G C).card
      let H := 2 * (centreless G C).card + J + (orN G C \ lam G C).card
      let shifts : Finset (Fin 13) := {0,1,3,9}
      let loss (d : Fin 13) := (U ∩ (Finset.univ.image fun p : Fin 13 =>
        s(Fin.castAdd 13 p, Fin.natAdd 13 (d-p)))).card
      2 ≤ J → 4 ≤ H → 4 ≤ U.card → (∀ d ∈ shifts, H < U.card + loss d) →
      13 + U.card ≤ A + H) :
(∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → x3.size ≤ (63 : ℕ) → (13 : ℕ) + (PEqualNP.TopForm.Ustar x1 x3).card ≤ (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) := by
  let P := SimpleGraph.fromRel (fun u v : Fin 26 =>
    u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
  let instP : DecidableRel P.Adj := inferInstanceAs (DecidableRel
    (SimpleGraph.fromRel (fun u v : Fin 26 =>
      u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))).Adj)
  intro G inst C eq least top two small
  subst G
  have same : inst = instP := Subsingleton.elim _ _
  subst inst
  let U := Ustar P C
  let A := (tops P C \ centreless P C).card
  let H := 2 * (centreless P C).card + (junk P C).card + (orN P C \ lam P C).card
  let shifts : Finset (Fin 13) := {0,1,3,9}
  let loss (d : Fin 13) := (U ∩ (Finset.univ.image fun p : Fin 13 =>
    s(Fin.castAdd 13 p, Fin.natAdd 13 (d-p)))).card
  suffices goal : 13 + U.card ≤ A + H by
    change 13 + U.card ≤ A + 2 * (centreless P C).card +
      (junk P C).card + (orN P C \ lam P C).card
    have reassociate (a b c d : Nat) : a + (b + c + d) = a + b + c + d := by omega
    exact goal.trans (Nat.le_of_eq (reassociate A (2 * (centreless P C).card)
      (junk P C).card (orN P C \ lam P C).card))
  have hp : (∀ d ∈ shifts, 13 ≤ A + loss d) ∧ ∃ d ∈ shifts, 4 * loss d ≤ U.card :=
    profiles C least top
  obtain ⟨pointwise, d₀, hd₀, hmin⟩ := hp
  have hH : 4 ≤ H := by
    by_contra! h
    have bound := @low P instP C rfl least top two (show H ≤ 3 by omega)
    omega
  by_cases easy : ∃ d ∈ shifts, U.card + loss d ≤ H
  · obtain ⟨d, hd, affordable⟩ := easy
    have bound := pointwise d hd
    omega
  · have miss : ∀ d ∈ shifts, H < U.card + loss d := by
      intro d hd
      exact Nat.lt_of_not_ge (fun ok => easy ⟨d, hd, ok⟩)
    have hU : 4 ≤ U.card := by
      have hf := miss d₀ hd₀
      omega
    exact hard C least top small two hH hU miss
