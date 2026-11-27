import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7973 : ∀ (x1 : Fin (26 : ℕ)), ∃ (x2 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x2 ∧ (PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)).getD (↑x1) Bool.false = Bool.true := by
  intro x1
  fin_cases x1
  · exact ⟨{0, 1, 2, 5}, by decide⟩
  · exact ⟨{0, 1, 2, 5}, by decide⟩
  · exact ⟨{0, 1, 2, 5}, by decide⟩
  · exact ⟨{0, 2, 3, 4}, by decide⟩
  · exact ⟨{0, 1, 4, 6}, by decide⟩
  · exact ⟨{0, 1, 2, 5}, by decide⟩
  · exact ⟨{0, 1, 2, 6}, by decide⟩
  · exact ⟨{0, 1, 2, 7}, by decide⟩
  · exact ⟨{0, 1, 4, 8}, by decide⟩
  · exact ⟨{0, 2, 4, 9}, by decide⟩
  · exact ⟨{0, 1, 5, 10}, by decide⟩
  · exact ⟨{0, 1, 2, 11}, by decide⟩
  · exact ⟨{0, 1, 4, 12}, by decide⟩
  · exact ⟨{2, 4, 5, 6}, by decide⟩
  · exact ⟨{0, 3, 5, 6}, by decide⟩
  · exact ⟨{0, 1, 4, 6}, by decide⟩
  · exact ⟨{0, 1, 2, 5}, by decide⟩
  · exact ⟨{1, 2, 3, 6}, by decide⟩
  · exact ⟨{0, 2, 3, 4}, by decide⟩
  · exact ⟨{0, 1, 4, 8}, by decide⟩
  · exact ⟨{0, 1, 2, 5}, by decide⟩
  · exact ⟨{0, 1, 2, 5}, by decide⟩
  · exact ⟨{0, 1, 2, 6}, by decide⟩
  · exact ⟨{1, 2, 3, 7}, by decide⟩
  · exact ⟨{0, 2, 3, 4}, by decide⟩
  · exact ⟨{1, 3, 4, 5}, by decide⟩
