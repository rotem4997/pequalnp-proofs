import PEqualNP.Library.L067
import PEqualNP.Library.L068
import PEqualNP.Library.Helpers.PaddedOracle
import PEqualNP.Library.Helpers.AlgCollapseBase

/-!
# The algebrizing collapse NP^E inside P^A, from the verifier enumeration

The algebrizing analogue of L-lib-072. The oracle `A` is defined by recursion on length: the
padded string `pad c k x` (with `c` coding a verifier index, a witness bound and a padding
exponent) is in `A` exactly when some short witness `w` has `(x, w)` accepted by the verifier
relative to `extOracle codes (mlext B)`, where `B` is the part of `A` shorter than the padded
string. The extension is `E := mlext A`. The two hypotheses `hext` (the multilinear extension
is a multiquadratic extension) and `hcongr` (the encoded extension below length `L` depends
only on the oracle below length `L`) are taken as assumptions.
-/

namespace PEqualNP.Library.Helpers.AlgCollapse

open PEqualNP.Library PEqualNP.Library.Helpers.PaddedOracle
open PEqualNP.Library.Helpers.AlgCollapseBase

theorem of_enum (hext : ∀ A : Language Bool, PEqualNP.Library.IsMultiquadraticExtension A (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A)) (hcongr : ∀ (codes : PEqualNP.Library.FieldCodes) (A A' : Language Bool) (L : ℕ), (∀ y : List Bool, y.length < L → (y ∈ A ↔ y ∈ A')) → ∀ s : List Bool, s.length < L → (s ∈ PEqualNP.Library.extOracle codes (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A) ↔ s ∈ PEqualNP.Library.extOracle codes (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A'))) : (∃ (g : ℕ → Language Bool → Set (List Bool × List Bool)) (r : ℕ → Polynomial ℕ), (∀ (A : Language Bool) (R : Set (List Bool × List Bool)), PEqualNP.Library.OracleDecidableInPolyTime A PEqualNP.Library.encodePair R → ∃ i : ℕ, g i A = R) ∧ ∀ (i : ℕ) (A A' : Language Bool) (x w : List Bool), (∀ y : List Bool, y.length ≤ (r i).eval (x.length + w.length) → (y ∈ A ↔ y ∈ A')) → ((x, w) ∈ g i A ↔ (x, w) ∈ g i A')) → ∀ codes : PEqualNP.Library.FieldCodes, PEqualNP.Library.FieldCodes.Injective codes → ∃ (A : Language Bool) (E : PEqualNP.Library.AlgExtension), PEqualNP.Library.IsMultiquadraticExtension A E ∧ PEqualNP.Library.OracleNP (PEqualNP.Library.extOracle codes E) ⊆ PEqualNP.Library.OracleP A := by
  rintro ⟨g, r, hcover, hloc⟩ codes _
  obtain ⟨e, he⟩ := exists_surj_poly
  let I : ℕ → ℕ := fun c => c.unpair.1
  let J : ℕ → ℕ := fun c => c.unpair.2.unpair.1
  let K : ℕ → ℕ := fun c => c.unpair.2.unpair.2
  let ψ : List Bool → Language Bool → Prop := fun s B =>
    ∃ (c : ℕ) (x : List Bool), s = pad c (K c) x ∧
      ∃ w : List Bool, w.length ≤ (e (J c)).eval x.length ∧
        (x, w) ∈ g (I c) (extOracle codes (mlext B))
  obtain ⟨A, hA⟩ := exists_fix ψ
  refine ⟨A, mlext A, hext A, ?_⟩
  rintro L ⟨R, p, hR, hL⟩
  obtain ⟨i, hi⟩ := hcover _ R hR
  obtain ⟨j, hj⟩ := he p
  obtain ⟨k, hk⟩ := exists_pad_exp (r i) p
  let c := Nat.pair i (Nat.pair j k)
  have hI : I c = i := by simp [I, c]
  have hJ : J c = j := by simp [J, c]
  have hK : K c = k := by simp [K, c]
  have hagree : ∀ x w : List Bool, w.length ≤ p.eval x.length →
      ((x, w) ∈ g i (extOracle codes (mlext A)) ↔
        (x, w) ∈ g i (extOracle codes
          (mlext {y | y ∈ A ∧ y.length < (pad c k x).length}))) := by
    intro x w hw
    apply hloc
    intro y hy
    have h1 := hk x.length w.length hw
    have h2 := pad_length c k x
    apply hcongr codes A {y | y ∈ A ∧ y.length < (pad c k x).length} (pad c k x).length
    · intro z hz
      exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
    · omega
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

end PEqualNP.Library.Helpers.AlgCollapse
