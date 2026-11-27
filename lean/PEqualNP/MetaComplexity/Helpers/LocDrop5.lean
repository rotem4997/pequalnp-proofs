import PEqualNP.MetaComplexity.Helpers.LocRes

/-!
# Local class: the drop at `x_v := 1` beside a vertex with two further neighbours

Sibling of `ToolDrop1` (plan `LocPlan.lean`, proof `LocRes.lean`): `v` has neighbours exactly
`u1`, `u2`; `u1` has at most two further neighbours, `u2` at most one. Then at most five edges
meet `{v, u1, u2}`, the free set grows by `|{u1, u2}|`, and the cover number falls by at most
`|{u1, u2}|`, so the potential `Phi1` drops by at most 5. No hypothesis `u1 ≠ u2` is needed.
Paper: the direct form of the run-of-four argument, its drop tool (P1).
-/

namespace PEqualNP.MetaComplexity.Loc

open PEqualNP.MetaComplexity.Helpers.Forest SimpleGraph

/-- TOOL. Drop at `x_v := 1`, `v` with neighbours exactly `u1`, `u2`; `u1` has at most two
further neighbours, `u2` at most one: at most 5. -/
def ToolDrop1Five : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v u1 u2 c1 c1' c2 : Fin n),
    (∀ w, G.Adj v w ↔ w = u1 ∨ w = u2) → (∀ w, G.Adj u1 w → w = v ∨ w = c1 ∨ w = c1') →
    (∀ w, G.Adj u2 w → w = v ∨ w = c2) → u1 ∉ A → u2 ∉ A →
    Phi1 G A ≤ Phi1 (delV G (insert v {u1, u2})) (A ∪ {u1, u2}) + 5 ∧
      (delV G (insert v {u1, u2})).edgeSet.ncard < G.edgeSet.ncard

end PEqualNP.MetaComplexity.Loc

namespace PEqualNP.MetaComplexity.Loc.Res

open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.Helpers.Forest SimpleGraph

theorem card_le_five' {α : Type*} [DecidableEq α] (a b c d e : α) :
    ({a, b, c, d, e} : Finset α).card ≤ 5 :=
  (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (card_le_four' b c d e))

theorem ToolDrop1Five_proof : ToolDrop1Five := by
  intro n G A v u1 u2 c1 c1' c2 hv h1 h2 hu1 hu2
  have hvu1 : G.Adj v u1 := (hv u1).2 (Or.inl rfl)
  refine ⟨?_, edges_lt G _ v u1 hvu1 (Finset.mem_insert_self _ _)⟩
  have hE := edges_le G (insert v {u1, u2})
    {s(v, u1), s(v, u2), s(u1, c1), s(u1, c1'), s(u2, c2)} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases (hv j).1 hij with rfl | rfl <;> simp
    · rcases h1 j hij with rfl | rfl | rfl <;> simp [Sym2.eq_swap]
    · rcases h2 j hij with rfl | rfl <;> simp [Sym2.eq_swap])
  have hT := tau_delV G (insert v {u1, u2}) {u1, u2} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases (hv j).1 hij with rfl | rfl <;> simp
    · simp
    · simp)
  have hS := card_le_five' (s(v, u1)) (s(v, u2)) (s(u1, c1)) (s(u1, c1')) (s(u2, c2))
  have hdis : A ∩ {u1, u2} = ∅ := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and]
    rintro hw (rfl | rfl)
    · exact hu1 hw
    · exact hu2 hw
  have hA := Finset.card_union_add_card_inter A {u1, u2}
  rw [hdis, Finset.card_empty] at hA
  unfold Phi1
  omega

end PEqualNP.MetaComplexity.Loc.Res
