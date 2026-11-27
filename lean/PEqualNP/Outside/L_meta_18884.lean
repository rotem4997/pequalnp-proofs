import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18884.Helpers
lemma matching_cover (n : ℕ) (π : Fin n → Fin n) (hπ : Function.Injective π) (G : SimpleGraph (Fin (n+n)))
    (hedge : ∀ i : Fin n,G.Adj (Fin.castAdd n i) (Fin.natAdd n (π i)))
    (T : Finset (Fin (n+n))) (hT : ∀ a b,G.Adj a b → a ∈ T ∨ b ∈ T) : n ≤ T.card := by
  classical
  let f : Fin n → Fin (n+n) := fun i => if Fin.castAdd n i ∈ T then Fin.castAdd n i else Fin.natAdd n (π i)
  have hinj : Function.Injective f := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have hpi := (π i).isLt
    have hpj := (π j).isLt
    dsimp only [f] at h
    split_ifs at h with h1 h2 h2
    · have hv := congrArg Fin.val h
      exact Fin.ext hv
    · have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    · have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    · apply hπ
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
  have hsub : Finset.univ.image f ⊆ T := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    dsimp only [f]
    split_ifs with h
    · exact h
    · exact (hT _ _ (hedge i)).resolve_left h
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin] using hc

abbrev G : SimpleGraph (Fin 26) := SimpleGraph.fromRel
  (fun u v : Fin 26 => u.val<13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ))

lemma cover_lower : ∀ T : Finset (Fin 26),PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → 13 ≤ T.card := by
  intro T hT
  apply matching_cover 13 (fun i : Fin 13 => -i) (by intro a b h;simpa using congrArg Neg.neg h) G _ T hT
  decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1500000 in
lemma geometry : PEqualNP.TopForm.NoFourCycle G := by
  unfold PEqualNP.TopForm.NoFourCycle
  decide
end PEqualNP.Outside.L_meta_18884.Helpers


theorem PEqualNP.Outside.L_meta_18884 : (∀ (x1 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (SimpleGraph.fromRel fun (x2 x3 : Fin (26 : ℕ)) => ↑x2 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x3 ∧ (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) x1 → (13 : ℕ) ≤ x1.card) := by
  exact PEqualNP.Outside.L_meta_18884.Helpers.cover_lower
