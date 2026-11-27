import PEqualNP.MetaComplexity.Helpers.FewNotFamily

/-!
# L-meta-708

The sets of a family missing a given set `y` can be re-indexed by `Fin m'` injectively, `m'`
their number, keeping set size and pairwise intersections.
-/

theorem PEqualNP.MetaComplexity.L708 : ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∃ (m' : ℕ) (e : Fin m' → Fin m), m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧ Function.Injective e ∧ (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧ (∀ i : Fin m', (S (e i)).card = q + 1) ∧ (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) :=
  fun n m q S y hcard hmeet =>
    PEqualNP.MetaComplexity.FewNot.fn_family_reindex n m q S y hcard hmeet
