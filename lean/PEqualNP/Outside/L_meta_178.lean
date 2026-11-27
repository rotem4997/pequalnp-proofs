import Mathlib
import PEqualNP.Defs

/-! An embedding of `H` into `Gh` carries cycles to cycles of the same length, and three
  distinct neighbours of a vertex to three distinct neighbours of its image. A vertex with
  nonzero label has exactly the neighbours `a` and `b`, so a vertex of degree three maps to a
  vertex of label zero. -/

theorem PEqualNP.Outside.L_meta_178 : ∀ (k N : ℕ) (Gh : SimpleGraph (Fin N)) (pos : Fin N → ℕ), (∀ u v : Fin N, Gh.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) → (∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, Gh.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → Gh.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (e : RelEmbedding H.Adj Gh.Adj), (∀ (L : ℕ) (c : ℕ → Fin m), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → H.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L) ∧ ∀ u x y z : Fin m, H.Adj u x → H.Adj u y → H.Adj u z → x ≠ y → x ≠ z → y ≠ z → pos (e u) = 0
 := by
  intro k N Gh pos _hedge hpos hcyc m H e
  refine ⟨?_, ?_⟩
  · intro L c hL hinj hadj
    refine hcyc L (fun i => e (c i)) hL ?_ ?_
    · intro i j hi hj hij
      exact hinj i j hi hj (e.injective hij)
    · intro i hi
      exact e.map_rel_iff.mpr (hadj i hi)
  · intro u x y z hx hy hz hxy hxz hyz
    by_contra hp
    obtain ⟨-, a, b, hab, -, -⟩ := hpos (e u) hp
    have hx' := (hab (e x)).mp (e.map_rel_iff.mpr hx)
    have hy' := (hab (e y)).mp (e.map_rel_iff.mpr hy)
    have hz' := (hab (e z)).mp (e.map_rel_iff.mpr hz)
    have ixy : e x ≠ e y := fun h => hxy (e.injective h)
    have ixz : e x ≠ e z := fun h => hxz (e.injective h)
    have iyz : e y ≠ e z := fun h => hyz (e.injective h)
    rcases hx' with h1 | h1 <;> rcases hy' with h2 | h2 <;> rcases hz' with h3 | h3 <;>
      first
        | exact ixy (h1.trans h2.symm)
        | exact ixz (h1.trans h3.symm)
        | exact iyz (h2.trans h3.symm)
