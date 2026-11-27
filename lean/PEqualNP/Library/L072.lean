import PEqualNP.Library.L067
import PEqualNP.Library.L068
import PEqualNP.Library.L069
import PEqualNP.Library.Helpers.PaddedOracle

/-!
# L-lib-072: an oracle with P^A = NP^A, by padding

Baker, Gill and Solovay's Theorem 1, from an abstract enumeration `g` of the verifiers
relative to any oracle together with polynomial bounds `r` on how far each verifier looks into
its oracle. No universal machine is used.

A code `c` stands for a triple `(i, j, k)`: the verifier `g i`, the witness bound `e j` (for a
surjection `e : ℕ → Polynomial ℕ`) and a padding exponent `k`. The oracle `A` is defined by
recursion on length: the padded string `pad c k x` is in `A` exactly when some witness `w` with
`|w| ≤ (e j)(|x|)` has `(x, w) ∈ g i B`, where `B` is the part of `A` shorter than the padded
string. For `L ∈ NP^A` with verifier `R = g i A` and bound `p = e j`, choosing `k` so that
`(n + 2)^k` exceeds every query length of `g i` on the relevant pairs makes `x ↦ pad c k x` a
polynomial-time reduction of `L` to `A`, so `L ∈ P^A` by L-lib-067 and L-lib-068. The other
inclusion is L-lib-069.
-/

namespace PEqualNP.Library

open Helpers.PaddedOracle

theorem L072 : (∃ (g : ℕ → Language Bool → Set (List Bool × List Bool)) (r : ℕ → Polynomial ℕ), (∀ (A : Language Bool) (R : Set (List Bool × List Bool)), PEqualNP.Library.OracleDecidableInPolyTime A PEqualNP.Library.encodePair R → ∃ i : ℕ, g i A = R) ∧ ∀ (i : ℕ) (A A' : Language Bool) (x w : List Bool), (∀ y : List Bool, y.length ≤ (r i).eval (x.length + w.length) → (y ∈ A ↔ y ∈ A')) → ((x, w) ∈ g i A ↔ (x, w) ∈ g i A')) → ∃ A : Language Bool, PEqualNP.Library.OracleP A = PEqualNP.Library.OracleNP A := by
  rintro ⟨g, r, hcover, hloc⟩
  obtain ⟨e, he⟩ := exists_surj_poly
  let I : ℕ → ℕ := fun c => c.unpair.1
  let J : ℕ → ℕ := fun c => c.unpair.2.unpair.1
  let K : ℕ → ℕ := fun c => c.unpair.2.unpair.2
  let ψ : List Bool → Language Bool → Prop := fun s B =>
    ∃ (c : ℕ) (x : List Bool), s = pad c (K c) x ∧
      ∃ w : List Bool, w.length ≤ (e (J c)).eval x.length ∧ (x, w) ∈ g (I c) B
  obtain ⟨A, hA⟩ := exists_fix ψ
  refine ⟨A, Set.Subset.antisymm (L069 A) ?_⟩
  rintro L ⟨R, p, hR, hL⟩
  obtain ⟨i, hi⟩ := hcover A R hR
  obtain ⟨j, hj⟩ := he p
  obtain ⟨k, hk⟩ := exists_pad_exp (r i) p
  let c := Nat.pair i (Nat.pair j k)
  have hI : I c = i := by simp [I, c]
  have hJ : J c = j := by simp [J, c]
  have hK : K c = k := by simp [K, c]
  -- the part of `A` below the padded string agrees with `A` on all relevant queries
  have hagree : ∀ x w : List Bool, w.length ≤ p.eval x.length →
      ((x, w) ∈ g i A ↔
        (x, w) ∈ g i {y | y ∈ A ∧ y.length < (pad c k x).length}) := by
    intro x w hw
    apply hloc
    intro y hy
    have h1 := hk x.length w.length hw
    have h2 := pad_length c k x
    show y ∈ A ↔ y ∈ A ∧ y.length < (pad c k x).length
    exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
  have hLeq : L = (pad c k ⁻¹' A : Set (List Bool)) := by
    ext x
    rw [hL]
    show _ ↔ pad c k x ∈ A
    rw [hA]
    constructor
    · rintro ⟨w, hw, hxw⟩
      refine ⟨c, x, by rw [hK], w, by rw [hJ, hj]; exact hw, ?_⟩
      rw [hI]
      rw [← hi] at hxw
      exact (hagree x w hw).1 hxw
    · rintro ⟨c', x', heq, w, hw, hxw⟩
      have hc : c = c' := pad_prefix heq
      subst hc
      rw [hK] at heq
      have hx : x = x' := pad_inj heq
      subst hx
      rw [hJ, hj] at hw
      rw [hI] at hxw
      refine ⟨w, hw, ?_⟩
      rw [← hi]
      exact (hagree x w hw).2 hxw
  rw [hLeq]
  exact L068 A (pad c k) A (pad_cpt c k) (L067 A)

end PEqualNP.Library
