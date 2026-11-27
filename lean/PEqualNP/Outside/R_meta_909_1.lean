import PEqualNP.Defs

-- The finite synthesis child retains 15 negative rows and 70 positive rows.
-- The other children certify graph completeness and monotone propagation.
theorem PEqualNP.Outside.R_meta_909_1 :
  (let d : ℕ → Finset (Fin 10) := fun m : ℕ => Finset.univ.filter (fun v : Fin 10 => m.testBit (v : ℕ) = true)
    let R : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
    ∃ C : PEqualNP.AndCount.AndCountCircuit 10,
      C.WellFormed ∧ C.size ≤ 6 ∧
      (∀ v : Fin 10,
        let readers : Finset (Fin C.size) := Finset.univ.filter (fun i : Fin C.size =>
          v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
        readers.card ≤ 2) ∧
      ∀ m ∈ R, C.eval (d m) = false ∧
        ((d m).card = 3 → ∀ w : Fin 10, w ∉ d m → C.eval (insert w (d m)) = true)) →
  (∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
    let d : ℕ → Finset (Fin 10) := fun m : ℕ => Finset.univ.filter (fun v : Fin 10 => m.testBit (v : ℕ) = true)
    let R : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
    ∀ I : Finset (Fin 10),
      (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      (∃ m ∈ R, I = d m) ∧
      (I.card = 3 ∨ ∀ w : Fin 10, w ∉ I →
        ∃ m ∈ R, (d m).card = 3 ∧
          ∃ v : Fin 10, v ∉ d m ∧ insert v (d m) ⊆ insert w I)) →
  (∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n)
    (U V : Finset (Fin n)), U ⊆ V → C.eval U = true → C.eval V = true) →
  ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true) := by
  intro hsmall hclass hmono G hG
  obtain ⟨C, hformed, hsize, hreads, hrows⟩ := hsmall
  refine ⟨C, hformed, hsize, hreads, ?_⟩
  intro I hind hmax
  obtain ⟨⟨m, hm, rfl⟩, hcover⟩ := hclass G hG I hind hmax
  refine ⟨(hrows m hm).1, ?_⟩
  intro w hw
  rcases hcover with hthree | hcover
  · exact (hrows m hm).2 hthree w hw
  · obtain ⟨r, hr, hthree, v, hv, hsub⟩ := hcover w hw
    exact hmono 10 C _ _ hsub ((hrows r hr).2 hthree v hv)
