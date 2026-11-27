import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- The counting obligation is the pair-clean lower bound from L-meta-1602.
theorem PEqualNP.Outside.R_meta_3688_643
    (normalize : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
      (col : Fin m → Bool) (mate : Fin m → Fin m) (C : Circuit),
      NoFourCycle G → (∀ u v, G.Adj u v → col u ≠ col v) →
      Function.Involutive mate → (∀ u, G.Adj u (mate u)) →
      IsAO2 m C → circuitFun m C = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 m D ∧ D.size ≤ C.size ∧ circuitFun m D = graphFun G ∅ ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∀ u v, ¬ G.Adj u v → gateVal m D j (pairInput u v) = false))
    (count : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (D : Circuit),
      NoFourCycle G → IsAO2 m D → circuitFun m D = graphFun G ∅ →
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ u v, ¬ G.Adj u v → gateVal m D j (pairInput u v) = false) →
      ∃ T : Finset (Fin m), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeFinset.card + T.card ≤ D.size + 1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n E p C hdense hlower hrect hmatch hC heval
  let L (i : Fin n) : Fin (n + n) := Fin.castAdd n i
  let R (i : Fin n) : Fin (n + n) := Fin.natAdd n i

  have L_injective : Function.Injective L := by
    intro i j h
    have hv := congrArg Fin.val h
    exact Fin.ext hv

  have R_injective : Function.Injective R := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    change n + i.val = n + j.val at hval
    omega

  have LR (i j : Fin n) : L i ≠ R j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = n + j.val at hv
    omega

  have parts (w : Fin (n + n)) : (∃ i : Fin n, w = L i) ∨ (∃ j : Fin n, w = R j) :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) w

  let arc (E : Finset (Fin n × Fin n)) (u v : Fin (n + n)) : Prop :=
    ∃ i j : Fin n, (i, j) ∈ E ∧ u = L i ∧ v = R j

  let graph (E : Finset (Fin n × Fin n)) : SimpleGraph (Fin (n + n)) :=
    SimpleGraph.fromRel (arc E)

  have adj (E : Finset (Fin n × Fin n)) (u v : Fin (n + n)) :
      (graph E).Adj u v ↔ arc E u v ∨ arc E v u := by
    change (u ≠ v ∧ (arc E u v ∨ arc E v u)) ↔ _
    refine ⟨And.right, ?_⟩
    intro h
    refine ⟨?_, h⟩
    rcases h with ⟨i, j, _, rfl, rfl⟩ | ⟨i, j, _, rfl, rfl⟩
    · exact LR i j
    · exact (LR i j).symm

  have adj_left (E : Finset (Fin n × Fin n)) (i : Fin n) (v : Fin (n + n)) :
      (graph E).Adj (L i) v ↔ ∃ j : Fin n, (i, j) ∈ E ∧ v = R j := by
    rw [adj]
    constructor
    · rintro (⟨a, b, hE, hi, hv⟩ | ⟨a, b, _, _, hi⟩)
      · have he := L_injective hi
        subst a
        exact ⟨b, hE, hv⟩
      · exact (LR i b hi).elim
    · rintro ⟨j, hj, rfl⟩
      exact Or.inl ⟨i, j, hj, rfl, rfl⟩

  have adj_right (E : Finset (Fin n × Fin n)) (j : Fin n) (u : Fin (n + n)) :
      (graph E).Adj (R j) u ↔ ∃ i : Fin n, (i, j) ∈ E ∧ u = L i := by
    rw [adj]
    constructor
    · rintro (⟨a, _, _, hj, _⟩ | ⟨a, b, hE, hu, hj⟩)
      · exact (LR a j hj.symm).elim
      · have he := R_injective hj
        subst b
        exact ⟨a, hE, hu⟩
    · rintro ⟨i, hi, rfl⟩
      exact Or.inr ⟨i, j, hi, rfl, rfl⟩

  have connected (E : Finset (Fin n × Fin n)) {i j : Fin n} (h : (i, j) ∈ E) :
      (graph E).Adj (L i) (R j) := (adj_left E i _).mpr ⟨j, h, rfl⟩

  let color (u : Fin (n + n)) : Bool := decide (n ≤ u.val)

  have opposite_colors {E : Finset (Fin n × Fin n)} {u v : Fin (n + n)}
      (h : (graph E).Adj u v) : color u ≠ color v := by
    have hL (i : Fin n) : color (L i) = false := by
      simp [color, L, Nat.not_le_of_lt i.isLt]
    have hR (j : Fin n) : color (R j) = true := by simp [color, R]
    rcases (adj E u v).mp h with ⟨i, j, _, rfl, rfl⟩ | ⟨i, j, _, rfl, rfl⟩ <;>
      simp [hL, hR]

  have no_four_cycle (E : Finset (Fin n × Fin n)) [DecidableRel (graph E).Adj]
      (hrect : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
        ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) :
      PEqualNP.TopForm.NoFourCycle (graph E) := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    by_contra huv
    rcases parts a with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨k, hik, rfl⟩ := (adj_left E i u).mp hu'.1
      obtain ⟨l, hil, rfl⟩ := (adj_left E i v).mp hv'.1
      obtain ⟨t, htk, rfl⟩ := (adj_right E k b).mp hu'.2.symm
      obtain ⟨s, hsl, he⟩ := (adj_right E l (L t)).mp hv'.2.symm
      have hts := L_injective he
      subst s
      exact hrect i t k l (fun eq => hab (congrArg L eq))
        (fun eq => huv (congrArg R eq)) ⟨hik, hil, htk, hsl⟩
    · obtain ⟨k, hkj, rfl⟩ := (adj_right E j u).mp hu'.1
      obtain ⟨l, hlj, rfl⟩ := (adj_right E j v).mp hv'.1
      obtain ⟨t, hkt, rfl⟩ := (adj_left E k b).mp hu'.2.symm
      obtain ⟨s, hls, he⟩ := (adj_left E l (R t)).mp hv'.2.symm
      have hts := R_injective he
      subst s
      exact hrect k l j t (fun eq => huv (congrArg L eq))
        (fun eq => hab (congrArg R eq)) ⟨hkj, hkt, hlj, hls⟩

  have incidence_fun (E : Finset (Fin n × Fin n)) [DecidableRel (graph E).Adj]
      (x : Fin (n + n) → Bool) : graphFun (graph E) ∅ x =
        decide (∃ i j : Fin n, (i, j) ∈ E ∧ x (L i) = true ∧ x (R j) = true) := by
    unfold graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    congr 1
    apply propext
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases (adj E u v).mp huv with ⟨i, j, hE, rfl, rfl⟩ | ⟨i, j, hE, rfl, rfl⟩
      · exact ⟨i, j, hE, hu, hv⟩
      · exact ⟨i, j, hE, hv, hu⟩
    · rintro ⟨i, j, hE, hi, hj⟩
      exact ⟨L i, R j, connected E hE, hi, hj⟩

  have card_edges (E : Finset (Fin n × Fin n)) [DecidableRel (graph E).Adj] :
      (graph E).edgeFinset.card = E.card := by
    let f : Fin n × Fin n → Sym2 (Fin (n + n)) := fun e => s(L e.1, R e.2)
    have hf : Function.Injective f := by
      intro u v h
      rcases Sym2.eq_iff.mp h with ⟨hl, hr⟩ | ⟨hl, _⟩
      · exact Prod.ext (L_injective hl) (R_injective hr)
      · exact (LR _ _ hl).elim
    have hEq : (graph E).edgeFinset = E.image f := by
      ext e
      refine Sym2.inductionOn e ?_
      intro a b
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image, adj]
      constructor
      · rintro (⟨i, j, hE, rfl, rfl⟩ | ⟨i, j, hE, rfl, rfl⟩)
        · exact ⟨(i, j), hE, rfl⟩
        · exact ⟨(i, j), hE, Sym2.eq_swap⟩
      · rintro ⟨⟨i,j⟩, hE, he⟩
        rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨i, j, hE, ha.symm, hb.symm⟩
        · exact Or.inr ⟨i, j, hE, ha.symm, hb.symm⟩
    rw [hEq, Finset.card_image_of_injective _ hf]

  have matching_cover (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n))
      (hm : ∀ i, (i, p i) ∈ E) (T : Finset (Fin (n + n)))
      (hT : ∀ u v, (graph E).Adj u v → u ∈ T ∨ v ∈ T) : n ≤ T.card := by
    let f (i : Fin n) := if L i ∈ T then L i else R (p i)
    have hf : Function.Injective f := by
      intro u v h
      by_cases hu : L u ∈ T <;> by_cases hv : L v ∈ T
      · exact L_injective (by simpa [f, hu, hv] using h)
      · exact (LR u (p v) (by simpa [f, hu, hv] using h)).elim
      · exact ((LR v (p u)).symm (by simpa [f, hu, hv] using h)).elim
      · exact p.injective (R_injective (by simpa [f, hu, hv] using h))
    have hin : Finset.univ.image f ⊆ T := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      by_cases h : L i ∈ T
      · simp [f, h]
      · have hr : R (p i) ∈ T := (hT _ _ (connected E (hm i))).resolve_left h
        simpa [f, h] using hr
    have h := Finset.card_le_card hin
    rwa [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at h
  let G := graph E
  have h4 : NoFourCycle G := no_four_cycle E hrect
  have hcolor : ∀ u v, G.Adj u v → color u ≠ color v := fun _ _ h => opposite_colors h
  let mate : Fin (n+n) → Fin (n+n) := Fin.addCases (fun i => R (p i)) (fun j => L (p.symm j))
  have mateL (i : Fin n) : mate (L i) = R (p i) := Fin.addCases_left i
  have mateR (j : Fin n) : mate (R j) = L (p.symm j) := Fin.addCases_right j
  have hMate : Function.Involutive mate := by
    intro w
    rcases parts w with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [mateL, mateR, p.symm_apply_apply]
    · rw [mateR, mateL, p.apply_symm_apply]
  have hMatched : ∀ w, G.Adj w (mate w) := by
    intro w
    rcases parts w with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [mateL]
      exact connected E (hmatch i)
    · rw [mateR]
      have h := (connected E (hmatch (p.symm j))).symm
      simpa using h
  have hGraph : circuitFun (n+n) C = graphFun G ∅ := by
    funext x
    rw [heval x, incidence_fun E x]
  have hCard : G.edgeFinset.card = E.card := card_edges E
  have hCover : ∀ T : Finset (Fin (n+n)), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → n ≤ T.card :=
    matching_cover E p hmatch
  obtain ⟨D, hD, hSize, hFun, hClean⟩ := normalize (n+n) G color mate C h4 hcolor hMate hMatched hC hGraph
  obtain ⟨T, hT, hBound⟩ := count (n+n) G D h4 hD hFun hClean
  have hMatch := hCover T hT
  omega
