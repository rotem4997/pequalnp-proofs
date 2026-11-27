import Mathlib

/-!
# Few NOT gates: re-indexing the sets of a family that miss a given set

Step 3 of the few-NOT build plan. The sets of a family `S : Fin m → Finset (Fin n)` that are
disjoint from a set `y` are re-indexed by `Fin m'`, with `m'` their number, through an
injective map whose image is exactly those indices. Set sizes and pairwise intersection
bounds pass to the re-indexed family.
-/

namespace PEqualNP.MetaComplexity.FewNot

/-- The sets of a family disjoint from `y`, re-indexed injectively by `Fin m'`, keeping set
size and pairwise intersections. -/
theorem fn_family_reindex (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∃ (m' : ℕ) (e : Fin m' → Fin m),
      m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧
      Function.Injective e ∧
      (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧
      (∀ i : Fin m', (S (e i)).card = q + 1) ∧
      (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) := by
  classical
  set F := Finset.univ.filter (fun w : Fin m => Disjoint (S w) y) with hF
  let f := F.orderEmbOfFin (rfl : F.card = F.card)
  refine ⟨F.card, fun i => f i, rfl, f.injective, ?_, fun i => hcard _, ?_⟩
  · intro w
    have hr : Set.range f = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    constructor
    · intro hw
      have : w ∈ (F : Set (Fin m)) := by simp [hF, hw]
      rw [← hr] at this
      exact this
    · rintro ⟨i, rfl⟩
      have : f i ∈ (F : Set (Fin m)) := hr ▸ Set.mem_range_self i
      simpa [hF] using this
  · intro i j hij
    exact hmeet _ _ (fun h => hij (f.injective h))

end PEqualNP.MetaComplexity.FewNot
