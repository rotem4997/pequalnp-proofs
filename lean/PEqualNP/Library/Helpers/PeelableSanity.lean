import PEqualNP.Defs.Peelable
import PEqualNP.MetaComplexity.Helpers.EdgeFnGraphPlan
import PEqualNP.MetaComplexity.Helpers.EdgeFnFinal
import PEqualNP.MetaComplexity.Helpers.ForestGraph

/-!
Scratch for the root module `Defs/Peelable.lean`: the first API lemmas, the bridge to the helper
notions of the full-basis bound (`GoodLeaf`, `Run`, `delV`, `Hered`, `Dich`), the bound itself on
every peelable graph, and the sanity examples of the concept.
-/

namespace PEqualNP.Library.Peel.Scratch

open PEqualNP.Library.Peel
open SimpleGraph

/-! ## API -/

theorem delVerts_adj {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i j : Fin n) :
    (delVerts G X).Adj i j ↔ G.Adj i j ∧ i ∉ X ∧ j ∉ X := Iff.rfl

theorem delVerts_empty {n : ℕ} (G : SimpleGraph (Fin n)) : delVerts G ∅ = G := by
  ext i j
  simp [delVerts_adj]

theorem delVerts_delVerts {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) :
    delVerts (delVerts G X) Y = delVerts G (X ∪ Y) := by
  ext i j
  simp only [delVerts_adj, Finset.mem_union, not_or]
  tauto

theorem delVerts_le {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : delVerts G X ≤ G :=
  fun _ _ h => h.1

theorem Peelable.hasPeel {n : ℕ} {G : SimpleGraph (Fin n)} (h : Peelable G) : HasPeel G := by
  have := h ∅
  rwa [delVerts_empty] at this

/-- Closure under deleting vertices (arity kept). -/
theorem Peelable.delVerts {n : ℕ} {G : SimpleGraph (Fin n)} (h : Peelable G)
    (X : Finset (Fin n)) : Peelable (delVerts G X) := by
  intro Y
  rw [delVerts_delVerts]
  exact h _

/-- No run below six vertices. -/
theorem not_isRun_of_lt {n : ℕ} (hn : n < 6) (G : SimpleGraph (Fin n))
    (a' a s t b b' : Fin n) : ¬ IsRun G a' a s t b b' := by
  intro h
  have := h.1.length_le_card
  simp at this
  omega

theorem peelable_of_goodLeaf {n : ℕ} (G : SimpleGraph (Fin n))
    (h : ∀ X : Finset (Fin n), (∃ i j, (delVerts G X).Adj i j) → GoodLeaf (delVerts G X)) :
    Peelable G :=
  fun X hE => Or.inl (h X hE)

/-! ## Bridge to the helper notions of the full-basis bound -/

section Bridge

open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

theorem delV_eq {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    delV G X = Peel.delVerts G X := by
  ext i j
  rw [delV_adj]
  rfl

theorem goodLeaf_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    PEqualNP.MetaComplexity.EdgeFn.GoodLeaf G ↔ Peel.GoodLeaf G := Iff.rfl

theorem run_iff {n : ℕ} (G : SimpleGraph (Fin n)) (a' a s t b b' : Fin n) :
    Run G a' a s t b b' ↔ IsRun G a' a s t b b' :=
  ⟨fun h => ⟨h.nd, h.ha, h.hs, h.ht, h.hb, h.ha', h.hb'⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

/-- The class hypothesis `Hered` of `a1_of_pieces` holds for `Peelable`. -/
theorem hered_peelable : Hered (fun _ G => Peelable G) := by
  intro n G X h
  rw [delV_eq]
  exact Peelable.delVerts h X

/-- The class hypothesis `Dich` of `a1_of_pieces` holds for `Peelable`. -/
theorem dich_peelable : Dich (fun _ G => Peelable G) := by
  intro n G h hE
  rcases Peelable.hasPeel h hE with h1 | ⟨a', a, s, t, b, b', h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨a', a, s, t, b, b', (run_iff G _ _ _ _ _ _).2 h2⟩

/-- Conversely, a class with both hypotheses lies inside `Peelable`. -/
theorem peelable_of_class {P : (n : ℕ) → SimpleGraph (Fin n) → Prop} (hH : Hered P)
    (hD : Dich P) {n : ℕ} {G : SimpleGraph (Fin n)} (hG : P n G) : Peelable G := by
  intro X hE
  have hP := hH n G X hG
  rw [delV_eq] at hP
  rcases hD n _ hP hE with h1 | ⟨a', a, s, t, b, b', h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨a', a, s, t, b, b', (run_iff _ _ _ _ _ _ _).1 h2⟩

/-- The full-basis bound (class form) on every peelable graph, every piece proved. -/
theorem a1_peelable : StmtA1 (fun _ G => Peelable G) :=
  a1_of_pieces hered_peelable dich_peelable stmtG3 stmtG6 stmtML_final Res.ToolRes0_proof
    Res.ToolRes1_proof Res.ToolDrop0_proof Res.ToolDrop1_proof

/-- The class (T) of the bound (cycles at least 7, branch vertices at distance at least 7) is
peelable. -/
theorem peelable_of_T7 {n : ℕ} {G : SimpleGraph (Fin n)} (h : T7 G) : Peelable G :=
  peelable_of_class (P := fun _ G => T7 G) stmtG1 (dich_of_g4 stmtG4) h

end Bridge

/-! ## Forests -/

theorem peelable_of_isAcyclic {n : ℕ} {G : SimpleGraph (Fin n)} (h : G.IsAcyclic) :
    Peelable G := by
  intro X hE
  exact Or.inl (PEqualNP.MetaComplexity.Helpers.Forest.forest_good_leaf _ (h.anti (delVerts_le G X)) hE)

/-! ## Sanity examples -/

instance decFromRel {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r] :
    DecidableRel (SimpleGraph.fromRel r).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (r x y ∨ r y x)))

/-- The path on 3 vertices. -/
theorem row_path3 : Peelable (SimpleGraph.fromRel fun i j : Fin 3 => j.val = i.val + 1) :=
  peelable_of_goodLeaf _ (by decide)

/-- The star with 3 leaves. -/
theorem row_star : Peelable (SimpleGraph.fromRel fun i j : Fin 4 => i.val = 0 ∧ j.val ≠ 0) :=
  peelable_of_goodLeaf _ (by decide)

/-- Every forest. -/
theorem row_forest : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsAcyclic → Peelable G :=
  fun _ _ h => peelable_of_isAcyclic h

/-- The 6-cycle: the run `0 - 1 - 2 - 3 - 4 - 5` with the ends `0` and `5` adjacent, and a good
leaf in every proper induced subgraph with an edge. -/
theorem row_cycle6 : Peelable (SimpleGraph.fromRel fun i j : Fin 6 => j.val = (i.val + 1) % 6) := by
  intro X
  by_cases hX : X = ∅
  · subst hX
    intro _
    exact Or.inr ⟨0, 1, 2, 3, 4, 5, by decide⟩
  · intro hE
    exact Or.inl ((by decide : ∀ X : Finset (Fin 6), X ≠ ∅ →
      (∃ i j, (delVerts (SimpleGraph.fromRel fun i j : Fin 6 => j.val = (i.val + 1) % 6) X).Adj i j) →
      GoodLeaf (delVerts (SimpleGraph.fromRel fun i j : Fin 6 => j.val = (i.val + 1) % 6) X))
      X hX hE)

/-- The 5-cycle is not peelable: no leaf, and no six distinct vertices. -/
theorem row_not_cycle5 : ¬ Peelable (SimpleGraph.fromRel fun i j : Fin 5 => j.val = (i.val + 1) % 5) := by
  intro h
  rcases h ∅ (by decide) with h1 | ⟨a', a, s, t, b, b', h2⟩
  · exact (by decide : ¬ GoodLeaf (delVerts
      (SimpleGraph.fromRel fun i j : Fin 5 => j.val = (i.val + 1) % 5) ∅)) h1
  · exact not_isRun_of_lt (by norm_num) _ _ _ _ _ _ _ h2

/-- The 6-cycle `0 .. 5` with a pendant vertex `6` at `0` is not peelable. The candidate run
`1 - 2 - 3 - 4 - 5 - 0` fails at its end `0`: besides `5` it has the two neighbours `1` and `6`. -/
theorem row_not_cycle6_pendant : ¬ Peelable (SimpleGraph.fromRel fun i j : Fin 7 =>
    (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) := by
  intro h
  rcases h ∅ (by decide) with h1 | ⟨a', a, s, t, b, b', h2⟩
  · exact (by decide : ¬ GoodLeaf (delVerts (SimpleGraph.fromRel fun i j : Fin 7 =>
      (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) ∅)) h1
  · have key : ∀ a' a : Fin 7, (delVerts (SimpleGraph.fromRel fun i j : Fin 7 =>
          (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) ∅).Adj a a' →
        ∀ s, (delVerts (SimpleGraph.fromRel fun i j : Fin 7 =>
          (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) ∅).Adj a s →
        ∀ t, (delVerts (SimpleGraph.fromRel fun i j : Fin 7 =>
          (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) ∅).Adj s t →
        ∀ b, (delVerts (SimpleGraph.fromRel fun i j : Fin 7 =>
          (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) ∅).Adj t b →
        ∀ b', (delVerts (SimpleGraph.fromRel fun i j : Fin 7 =>
          (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) ∅).Adj b b' →
        ¬ IsRun (delVerts (SimpleGraph.fromRel fun i j : Fin 7 =>
          (i.val < 6 ∧ j.val = (i.val + 1) % 6) ∨ (i.val = 0 ∧ j.val = 6)) ∅) a' a s t b b' := by
      set_option synthInstance.maxSize 2048 in set_option synthInstance.maxHeartbeats 400000 in decide
    exact key a' a ((h2.2.1 a').2 (Or.inl rfl)) s ((h2.2.1 s).2 (Or.inr rfl))
      t ((h2.2.2.1 t).2 (Or.inr rfl)) b ((h2.2.2.2.1 b).2 (Or.inr rfl))
      b' ((h2.2.2.2.2.1 b').2 (Or.inr rfl)) h2

/-- Closure under deleting vertices. -/
theorem row_delVerts : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)),
    Peelable G → Peelable (delVerts G X) :=
  fun _ _ X h => Peelable.delVerts h X

end PEqualNP.Library.Peel.Scratch
