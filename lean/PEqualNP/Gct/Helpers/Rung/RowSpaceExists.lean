import PEqualNP.Gct.Helpers.Rung.Statements

/-!
# The superquadratic rung: a good row space exists

Helper module, proofs only. It proves the step `RowSpaceExists` of
`PEqualNP.Gct.Rung` from the two steps `Avoidance` and `LemmaE`, which are taken as hypotheses.

The vectors of `ℂ^b` with at most `r - 1` distinct coordinate values lie in the finitely many
subspaces `colourRange b (r - 1) c`, one for each colouring `c : Fin b → Fin (r - 1)`, each of
dimension at most `r - 1`. `Avoidance` gives a subspace of dimension `b - (r - 1)` meeting all
of them in `0`; a basis of it is the family `P`.
-/

namespace PEqualNP.Gct.Rung

namespace RowSp

/-- The vectors of `ℂ^b` that are constant on the classes of the colouring `c`: the range of
`w ↦ w ∘ c`. -/
def colourRange (b k : ℕ) (c : Fin b → Fin k) : Submodule ℂ (Fin b → ℂ) :=
  LinearMap.range (LinearMap.funLeft ℂ ℂ c)

theorem finrank_colourRange_le (b k : ℕ) (c : Fin b → Fin k) :
    Module.finrank ℂ (colourRange b k c) ≤ k := by
  have h := LinearMap.finrank_range_le (LinearMap.funLeft ℂ ℂ c)
  rw [Module.finrank_fin_fun] at h
  exact h

/-- A vector with at most `k` distinct coordinate values is constant on the classes of some
colouring with `k` colours. -/
theorem exists_colour (b k : ℕ) (z : Fin b → ℂ) (h : (Finset.univ.image z).card ≤ k) :
    ∃ c : Fin b → Fin k, z ∈ colourRange b k c := by
  classical
  let s : Finset ℂ := Finset.univ.image z
  let g : s → Fin k := fun x => Fin.castLE h (s.equivFin x)
  have hg : Function.Injective g := fun x x' hx =>
    s.equivFin.injective (Fin.castLE_injective h hx)
  let p : Fin b → s := fun i => ⟨z i, Finset.mem_image_of_mem z (Finset.mem_univ i)⟩
  refine ⟨fun i => g (p i), Function.extend g (fun x => (x : ℂ)) 0, ?_⟩
  funext i
  simp only [LinearMap.funLeft_apply]
  rw [hg.extend_apply]

end RowSp

open RowSp in
theorem rowSpaceExists : Avoidance → LemmaE → RowSpaceExists := by
  intro hA hE b r l hr hl
  obtain ⟨U, hU, hW⟩ := hA (Fin b → ℂ) (Fin b → Fin (r - 1))
    (fun c => colourRange b (r - 1) c) (r - 1) (fun c => finrank_colourRange_le b (r - 1) c)
  have hUl : Module.finrank ℂ U = l := by
    rw [hU, Module.finrank_fin_fun]
    omega
  let B := Module.finBasisOfFinrankEq ℂ U hUl
  refine ⟨fun n s => (B s : Fin b → ℂ) n, fun y hy => ?_⟩
  have hv : (fun n => ∑ s, (B s : Fin b → ℂ) n * y s)
      = ((∑ s, y s • B s : U) : Fin b → ℂ) := by
    funext n
    simp [mul_comm]
  rw [hv] at hy
  obtain ⟨c, hc⟩ := exists_colour b (r - 1) _ (hE b r _ hr hy)
  have hmem : ((∑ s, y s • B s : U) : Fin b → ℂ) ∈ U ⊓ colourRange b (r - 1) c :=
    ⟨(∑ s, y s • B s : U).2, hc⟩
  rw [hW c, Submodule.mem_bot] at hmem
  have h0 : (∑ s, y s • B s : U) = 0 := Subtype.ext hmem
  funext s
  exact Fintype.linearIndependent_iff.1 B.linearIndependent y h0 s

end PEqualNP.Gct.Rung
