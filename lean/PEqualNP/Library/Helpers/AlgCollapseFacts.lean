import PEqualNP.Library.Helpers.AlgCollapseBase

/-!
# Facts about the multilinear extension of an oracle

`mlext A` is a multiquadratic extension of `A`, and the extension oracle built from it depends
only on the short strings of `A`: oracles agreeing below length `L` give extension oracles
agreeing below length `L`.
-/

namespace PEqualNP.Library.Helpers.AlgCollapseFacts

open PEqualNP.Library.Helpers.QueryEvasion

theorem mlext_ext (A : Language Bool) :
    PEqualNP.Library.IsMultiquadraticExtension A
      (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A) := by
  classical
  intro p _ k m
  refine ⟨fun i => ?_, fun x => ?_⟩
  · exact (degreeOf_interp_le _ i).trans (by norm_num)
  · have h := eval_interp (F := GaloisField p k) (n := m)
      (fun z => if List.ofFn z ∈ A then (1 : GaloisField p k) else 0) x
    unfold PEqualNP.Library.Helpers.AlgCollapseBase.mlext
    convert h using 2
    rfl

theorem algEncodeNat_length_pos (n : ℕ) : 0 < (PEqualNP.Library.algEncodeNat n).length := by
  simp [PEqualNP.Library.algEncodeNat]

theorem mlext_congr (A A' : Language Bool) (m : ℕ)
    (h : ∀ y : List Bool, y.length = m → (y ∈ A ↔ y ∈ A')) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    PEqualNP.Library.Helpers.AlgCollapseBase.mlext A p k m =
      PEqualNP.Library.Helpers.AlgCollapseBase.mlext A' p k m := by
  unfold PEqualNP.Library.Helpers.AlgCollapseBase.mlext
  congr 1
  funext z
  have := h (List.ofFn z) (List.length_ofFn)
  by_cases hz : List.ofFn z ∈ A
  · simp [hz, this.mp hz]
  · have hz' : List.ofFn z ∉ A' := fun h' => hz (this.mpr h')
    simp [hz, hz']

theorem extOracle_mlext_mono (codes : PEqualNP.Library.FieldCodes) (A A' : Language Bool)
    (L : ℕ) (h : ∀ y : List Bool, y.length < L → (y ∈ A ↔ y ∈ A')) (s : List Bool)
    (hs : s.length < L)
    (hA : s ∈ PEqualNP.Library.extOracle codes
      (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A)) :
    s ∈ PEqualNP.Library.extOracle codes
      (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A') := by
  obtain ⟨p, hp, k, m, y, j, rfl, hbit⟩ := hA
  have hm : m < L := by
    have h1 := algEncodeNat_length_pos p
    have h2 := algEncodeNat_length_pos k
    have h3 := algEncodeNat_length_pos j
    have h4 : m ≤ (List.ofFn fun i =>
        PEqualNP.Library.algEncodeNat (codes p k (y i))).flatten.length := by
      rw [List.length_flatten]
      rw [List.map_ofFn, List.sum_ofFn]
      calc m = ∑ _ : Fin m, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => algEncodeNat_length_pos _
    simp only [List.length_append] at hs
    omega
  have heq := mlext_congr A A' m (fun y hy => h y (hy ▸ hm)) p k
  exact ⟨p, hp, k, m, y, j, rfl, heq ▸ hbit⟩

theorem extOracle_mlext_congr (codes : PEqualNP.Library.FieldCodes) (A A' : Language Bool)
    (L : ℕ) (h : ∀ y : List Bool, y.length < L → (y ∈ A ↔ y ∈ A')) :
    ∀ s : List Bool, s.length < L →
      (s ∈ PEqualNP.Library.extOracle codes
          (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A) ↔
        s ∈ PEqualNP.Library.extOracle codes
          (PEqualNP.Library.Helpers.AlgCollapseBase.mlext A')) := by
  intro s hs
  exact ⟨extOracle_mlext_mono codes A A' L h s hs,
    extOracle_mlext_mono codes A' A L (fun y hy => (h y hy).symm) s hs⟩

end PEqualNP.Library.Helpers.AlgCollapseFacts
