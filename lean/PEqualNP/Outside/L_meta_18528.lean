import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18528

private def edges : List (Fin 10 × Fin 10) := [(0, 1), (0, 5), (5, 7), (1, 2), (1, 6), (6, 8), (2, 3), (2, 7), (7, 9), (3, 4), (3, 8), (8, 5), (4, 0), (4, 9), (9, 6)]

private def adj (a b : Fin 10) : Prop := (a,b) ∈ edges ∨ (b,a) ∈ edges

private instance (a b : Fin 10) : Decidable (adj a b) := by
  unfold adj
  infer_instance

private def graph (x : Fin 10 → Bool) : Bool :=
  edges.any fun e => x e.1 && x e.2

private theorem graphSpec (x : Fin 10 → Bool) : graph x = true ↔
    ∃ a b : Fin 10, adj a b ∧ x a = true ∧ x b = true := by
  simp only [graph, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, h, ha, hb⟩
    exact ⟨a, b, Or.inl h, ha, hb⟩
  · rintro ⟨a,b,h | h,ha,hb⟩
    · exact ⟨(a,b), h, ha, hb⟩
    · exact ⟨(b,a), h, hb, ha⟩

private def images : Array (Array (Fin 10)) := #[
  #[9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
  #[4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
  #[0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
  #[0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
  #[4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
  #[4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
  #[0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
  #[0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
  #[0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]

private def image (v a : Fin 10) : Fin 10 := ((images[v.val]?).getD #[])[a.val]?.getD 0

private theorem hit : ∀ v : Fin 10, image v v = 9 := by decide +kernel

private theorem bij : ∀ v : Fin 10, Function.Bijective (image v) := by decide +kernel

private theorem preserves : ∀ v a b : Fin 10,
    adj (image v a) (image v b) ↔ adj a b := by decide +kernel

private theorem graphFormula (x : Fin 10 → Bool) : graph x =
  (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x (Fin.castAdd (5 : ℕ) x2) && x (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x (Fin.castAdd (5 : ℕ) x2) && x (Fin.natAdd (5 : ℕ) x2) || x (Fin.natAdd (5 : ℕ) x2) && x (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))) := by
  simp [graph, edges, List.finRange, Fin.castAdd, Fin.natAdd, Bool.or_assoc]

theorem main (v : Fin 10) : ∃ p : Equiv.Perm (Fin 10),
    p v = 9 ∧ ∀ x : Fin 10 → Bool, graph (x ∘ p) = graph x := by
  classical
  let p := Equiv.ofBijective (image v) (bij v)
  refine ⟨p, hit v, fun x => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [graphSpec, graphSpec]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨p a, p b, (preserves v a b).mpr h, ha, hb⟩
  · rintro ⟨a,b,h,ha,hb⟩
    refine ⟨p.symm a, p.symm b, (preserves v _ _).mp ?_, ?_, ?_⟩
    · change adj (p (p.symm a)) (p (p.symm b))
      simpa using h
    · simpa [Function.comp_apply] using ha
    · simpa [Function.comp_apply] using hb

end PEqualNP.Outside.L_meta_18528

open PEqualNP.Outside.L_meta_18528 in
theorem PEqualNP.Outside.L_meta_18528 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : Fin (10 : ℕ)), ∃ (x3 : Equiv.Perm (Fin (10 : ℕ))), x3 x2 = (9 : Fin (10 : ℕ)) ∧ ∀ (x4 : Fin (10 : ℕ) → Bool), x1 (x4 ∘ ⇑x3) = x1 x4 := by
  intro f v
  obtain ⟨p, hp, he⟩ := main v
  refine ⟨p, hp, fun x => ?_⟩
  exact (graphFormula (x ∘ p)).symm.trans ((he x).trans (graphFormula x))
