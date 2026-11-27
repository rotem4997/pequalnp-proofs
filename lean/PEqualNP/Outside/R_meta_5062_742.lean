import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5062_742
    (hCover : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n) (G : SimpleGraph (Fin n)),
      C.Computes G → C.outVars = ∅ → ∀ T : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) →
      (∀ S : Finset (Fin n), S ⊆ T →
        (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → T ⊆ S) →
      ∃ L R : Finset (Fin C.size), Disjoint L R ∧
        (L.biUnion C.leftVars ∪ R.biUnion C.rightVars) = T)
    (hBirth : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n) (G : SimpleGraph (Fin n)),
      C.Computes G → C.outVars = ∅ →
      (∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)) →
      ∀ u v : Fin n, G.Adj u v → ∃ i : Fin C.size,
        (u ∈ C.leftVars i ∧ v ∈ C.rightVars i) ∨
        (v ∈ C.leftVars i ∧ u ∈ C.rightVars i))
    (hFinite : let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel (fun a b : Fin 42 => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ));
      ∀ (k : ℕ) (A B : Fin k → Finset (Fin 42)), k = 20 →
      (∀ i, Disjoint (A i) (B i)) →
      (∀ v : Fin 42, {i : Fin k | v ∈ A i ∨ v ∈ B i}.ncard ≤ 4) →
      (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
        {i : Fin k | p ∈ A i ∨ p ∈ B i ∨ l ∈ A i ∨ l ∈ B i}.ncard ≤ 6) →
      (∀ T : Finset (Fin 42),
        (∀ u v : Fin 42, G.Adj u v → u ∈ T ∨ v ∈ T) →
        (∀ S : Finset (Fin 42), S ⊆ T →
          (∀ u v : Fin 42, G.Adj u v → u ∈ S ∨ v ∈ S) → T ⊆ S) →
        ∃ L R : Finset (Fin k), Disjoint L R ∧ (L.biUnion A ∪ R.biUnion B) = T) →
      (∀ u v : Fin 42, G.Adj u v → ∃ i : Fin k,
        (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) → False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (20 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) → False := by
  dsimp only
  intro C hWF hComp hOut hSingle hDisjoint hSize hDegree hPair
  apply hFinite C.size C.leftVars C.rightVars hSize hDisjoint hDegree hPair
  · intro T hT hmin
    exact hCover 42 C _ hComp hOut T hT hmin
  · intro u v huv
    exact hBirth 42 C _ hComp hOut hDisjoint u v huv
