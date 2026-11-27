import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2640_401
  (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A K : Finset (Fin n))
    (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin n),
    ((∀ a ∉ A, (G.neighborSet a).ncard = 3) ∧ 7 ≤ G.egirth ∧ ∀ a b : Fin n, G.Adj a b → a ∉ A) →
    PEqualNP.MetaComplexity.IsMinimalCircuit n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) →
    (∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K) →
    (∀ K' : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ K' ∨ b ∈ K') → K.card ≤ K'.card) →
    u ∈ K →
    ∃ C : ℕ → PEqualNP.CircuitLowerBounds.Circuit,
      (PEqualNP.MetaComplexity.FanInTwo (C 0) ∧ (C 0).size ≤ D.size ∧
        PEqualNP.MetaComplexity.circuitFun n (C 0) = PEqualNP.MetaComplexity.circuitFun n D) ∧
      (∀ x : Fin n → Bool, x u = false → (C 4).eval (List.ofFn x) = D.eval (List.ofFn x)) ∧
      ∀ i < 4, ∃ m p : ℕ,
        (m < (C i).size ∧ (p < n + m ∨ n + (C i).size ≤ p) ∧
          C (i + 1) = PEqualNP.CircuitMoves.eraseGate n (C i) m p) ∧
        ((∀ x : Fin n → Bool, x u = false →
          let w := (C i).wires (List.ofFn x)
          w.getD (n + m) false = w.getD p false) ∨
        ((C i).output ≠ n + m ∧ ∀ g ∈ (C i).gates.drop (m + 1), n + m ∉ g.inputs)))
  (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A K : Finset (Fin n))
    (D E : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n),
    ((∀ a ∉ A, (G.neighborSet a).ncard = 3) ∧ 7 ≤ G.egirth ∧ ∀ a b : Fin n, G.Adj a b → a ∉ A) →
    PEqualNP.MetaComplexity.IsMinimalCircuit n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) →
    (∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K) →
    (∀ K' : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ K' ∨ b ∈ K') → K.card ≤ K'.card) →
    (G.Adj u v ∧ u ∈ K ∧ v ∈ K ∧ PEqualNP.MetaComplexity.FanInTwo E ∧ E.size + 4 ≤ D.size) →
    (∀ x : Fin n → Bool, x u = false → E.eval (List.ofFn x) = D.eval (List.ofFn x)) →
    ∃ C : ℕ → PEqualNP.CircuitLowerBounds.Circuit, C 0 = E ∧
      ∀ i < 3, ∃ m p : ℕ,
        (m < (C i).size ∧ (p < n + m ∨ n + (C i).size ≤ p) ∧
          C (i + 1) = PEqualNP.CircuitMoves.eraseGate n (C i) m p) ∧
        ((∀ x : Fin n → Bool, x u = false → x v = false →
          let w := (C i).wires (List.ofFn x)
          w.getD (n + m) false = w.getD p false) ∨
        ((C i).output ≠ n + m ∧ ∀ g ∈ (C i).gates.drop (m + 1), n + m ∉ g.inputs))) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  have fanInTwo_eraseGate : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ),
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.FanInTwo (PEqualNP.CircuitMoves.eraseGate n C m p) := by
    intro n C m p h
    unfold PEqualNP.CircuitMoves.eraseGate
    split_ifs with hm
    · intro g hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact h g (List.mem_of_mem_take hg)
      · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
        exact ⟨h1, by simpa using h2⟩
    · exact h
  have size_eraseGate : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ),
      m < C.size → (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size := by
    intro n C m p hm
    unfold PEqualNP.CircuitMoves.eraseGate PEqualNP.CircuitLowerBounds.Circuit.size at *
    simp only [hm, ↓reduceIte, List.length_append, List.length_take, List.length_map,
      List.length_drop]
    omega
  -- A minimum vertex cover of a graph that is not two-colourable contains both ends of an edge.
  have cover_edge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ¬ G.Colorable 2 →
      ∃ K : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K) ∧
        (∀ K' : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ K' ∨ b ∈ K') →
          K.card ≤ K'.card) ∧
        ∃ u v : Fin n, G.Adj u v ∧ u ∈ K ∧ v ∈ K := by
    intro n G hnon
    classical
    have hex : ∃ k : ℕ, ∃ K : Finset (Fin n),
        (∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K) ∧ K.card = k :=
      ⟨_, Finset.univ, fun a _ _ => Or.inl (Finset.mem_univ a), rfl⟩
    obtain ⟨K, hK, hKc⟩ := Nat.find_spec hex
    refine ⟨K, hK, ?_, ?_⟩
    · intro K' hK'
      rw [hKc]
      exact Nat.find_min' hex ⟨K', hK', rfl⟩
    · by_contra hno
      simp only [not_exists, not_and] at hno
      apply hnon
      refine ⟨SimpleGraph.Coloring.mk (fun a => if a ∈ K then (0 : Fin 2) else 1) ?_⟩
      intro a b hab
      have hc := hK a b hab
      by_cases ha : a ∈ K
      · have hb : b ∉ K := hno a b hab ha
        simp [ha, hb]
      · have hb : b ∈ K := hc.resolve_left ha
        simp [ha, hb]
  intro n G A D hnon hdeg hgirth hiso _hedge hmin hfun
  have hg : (7 : ℕ∞) ≤ G.egirth :=
    SimpleGraph.le_egirth.2 (fun a w hw => by exact_mod_cast hgirth a w hw)
  obtain ⟨K, hK, hKmin, u, v, huv, hu, hv⟩ :=
    cover_edge n G hnon
  obtain ⟨C, ⟨h0F, h0s, h0f⟩, h4fun, hst⟩ :=
    h1 n G A K D u ⟨hdeg, hg, hiso⟩ hmin hfun hK hKmin hu
  have hFan : ∀ i, i ≤ 4 → PEqualNP.MetaComplexity.FanInTwo (C i) ∧ (C i).size + i = (C 0).size := by
    intro i
    induction i with
    | zero => intro _; exact ⟨h0F, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨m, p, ⟨hm, -, he⟩, -⟩ := hst k (by omega)
      obtain ⟨ihF, ihs⟩ := ih (by omega)
      have hsz := size_eraseGate n (C k) m p hm
      rw [he]
      exact ⟨fanInTwo_eraseGate n (C k) m p ihF, by omega⟩
  obtain ⟨hF4, hs4⟩ := hFan 4 le_rfl
  obtain ⟨E, hE0, hEst⟩ := h2 n G A K D (C 4) u v ⟨hdeg, hg, hiso⟩ hmin hfun hK hKmin
    ⟨huv, hu, hv, hF4, by omega⟩ h4fun
  have huv' : v ≠ u := (G.ne_of_adj huv).symm
  refine ⟨u, v, huv, fun i => if i ≤ 4 then C i else E (i - 4), ?_, ?_, ?_, ?_⟩
  · simpa using h0F
  · simpa using h0s
  · simpa using h0f
  · intro i hi
    by_cases hi4 : i < 4
    · obtain ⟨m, p, ⟨hm, hp, he⟩, hj⟩ := hst i hi4
      refine ⟨m, p, ?_, ?_, ?_, ?_⟩
      · simpa [show i ≤ 4 by omega] using hm
      · simpa [show i ≤ 4 by omega] using hp
      · simpa [show i ≤ 4 by omega, show i + 1 ≤ 4 by omega] using he
      · simp only [show i ≤ 4 by omega, ↓reduceIte]
        rcases hj with hj | hj
        · left
          intro x
          exact hj _ (by simp [G.ne_of_adj huv])
        · right
          exact hj
    · have hk : ∀ j, 4 ≤ j → (if j ≤ 4 then C j else E (j - 4)) = E (j - 4) := by
        intro j hj
        by_cases hj4 : j ≤ 4
        · have : j = 4 := by omega
          subst this
          simp [hE0]
        · simp [hj4]
      obtain ⟨m, p, ⟨hm, hp, he⟩, hj⟩ := hEst (i - 4) (by omega)
      have hi' : i + 1 - 4 = i - 4 + 1 := by omega
      refine ⟨m, p, ?_, ?_, ?_, ?_⟩
      · beta_reduce; rw [hk i (by omega)]; exact hm
      · beta_reduce; rw [hk i (by omega)]; exact hp
      · beta_reduce; rw [hk i (by omega), hk (i + 1) (by omega), hi']; exact he
      · beta_reduce; rw [hk i (by omega)]
        rcases hj with hj | hj
        · left
          intro x
          exact hj _ (by simp [G.ne_of_adj huv])
            (by simp)
        · right
          exact hj
