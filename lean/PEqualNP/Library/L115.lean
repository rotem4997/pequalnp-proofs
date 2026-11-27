import PEqualNP.Search.Helpers.Hierarchy.Root

/-- Sum of squares on parity systems (Grigoriev 2001; Schoenebeck 2008): if a parity system has
no refutation by adding equations in which every line has at most `d` variables, then its
polynomial system in sign variables over the reals has no sum-of-squares refutation of
half-degree `D` (degree `2 * D`) whenever `2 * D ≤ d`. -/
theorem PEqualNP.Library.L115 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d D : ℕ), 2 * D ≤ d → ¬ PEqualNP.Search.XorRefutable F d → ¬ PEqualNP.Search.SoSRefutable (PEqualNP.Search.xorSystem F) D :=
  PEqualNP.Search.Helpers.HierarchyDraft.sosWall_root
