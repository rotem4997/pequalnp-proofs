import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8935_436
    (bound : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ))
    (relabel : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)),   ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2.size ≃ Fin x4.size),     x4.size = x2.size ∧       (PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4) ∧         (∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 (x6 ∘ ⇑x3)) ∧           ∀ (x6 : Fin x2.size),             have x7 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.get x6;             have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.gates.get (x5 x6);             x8.op = x7.op ∧ x8.inputs.length = x7.inputs.length ∧ (x7.inputs.Nodup → x8.inputs.Nodup) ∧ ((∀ x9 ∈ x7.inputs, x9 < x1 + ↑x6) → ∀ x10 ∈ x8.inputs, x10 < x1 + ↑(x5 x6)) ∧ ∀ (x9 : Fin x1), ↑(x3 x9) ∈ x8.inputs ↔ ↑x9 ∈ x7.inputs) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro n G inst C bip _ four least _ _
  obtain ⟨col⟩ := bip
  have two : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  obtain ⟨a, b, σ, h0, h1⟩ : ∃ (a b : ℕ) (σ : Fin (a + b) ≃ Fin n),
      (∀ p : Fin a, col (σ (Fin.castAdd b p)) = 0) ∧ (∀ l : Fin b, col (σ (Fin.natAdd a l)) ≠ 0) := by
    refine ⟨Fintype.card {v // col v = 0}, Fintype.card {v // ¬ col v = 0},
      finSumFinEquiv.symm.trans ((Equiv.sumCongr (Fintype.equivFin _).symm
        (Fintype.equivFin _).symm).trans (Equiv.sumCompl (fun v => col v = 0))), ?_, ?_⟩
    · intro p
      simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl]
      exact ((Fintype.equivFin _).symm p).2
    · intro l
      simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr]
      exact ((Fintype.equivFin _).symm l).2
  have hab : a + b = n := by simpa using Fintype.card_congr σ
  subst hab
  have split : ∀ i : Fin (a + b), (∃ p : Fin a, i = Fin.castAdd b p) ∨ (∃ l : Fin b, i = Fin.natAdd a l) := by
    intro i
    have hi' := i.isLt
    by_cases hi : i.val < a
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · refine Or.inr ⟨⟨i.val - a, by omega⟩, Fin.ext ?_⟩
      show i.val = a + (i.val - a)
      omega
  have side : ∀ u : Fin (a + b), (∃ p, u = σ (Fin.castAdd b p)) ∨ (∃ l, u = σ (Fin.natAdd a l)) := by
    intro u
    rcases split (σ.symm u) with ⟨p, hp⟩ | ⟨l, hl⟩
    · exact Or.inl ⟨p, by rw [← hp]; simp⟩
    · exact Or.inr ⟨l, by rw [← hl]; simp⟩
  have mixed : ∀ u v, G.Adj u v → ∃ p l, (u = σ (Fin.castAdd b p) ∧ v = σ (Fin.natAdd a l)) ∨
      (v = σ (Fin.castAdd b p) ∧ u = σ (Fin.natAdd a l)) := by
    intro u v huv
    have hc := col.valid huv
    rcases side u with ⟨p, rfl⟩ | ⟨l, rfl⟩ <;> rcases side v with ⟨q, rfl⟩ | ⟨m, rfl⟩
    · exact absurd ((h0 p).trans (h0 q).symm) hc
    · exact ⟨p, m, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨q, l, Or.inr ⟨rfl, rfl⟩⟩
    · exact absurd (((two _).resolve_left (h1 l)).trans ((two _).resolve_left (h1 m)).symm) hc
  let E : Finset (Fin a × Fin b) :=
    Finset.univ.filter (fun e => G.Adj (σ (Fin.castAdd b e.1)) (σ (Fin.natAdd a e.2)))
  have memE : ∀ p l, (p, l) ∈ E ↔ G.Adj (σ (Fin.castAdd b p)) (σ (Fin.natAdd a l)) := by
    intro p l
    simp [E]
  obtain ⟨hA, hfunC, -⟩ := least
  obtain ⟨C2, e, hsize, -, hfun, hg⟩ := relabel (a + b) C σ.symm
  have hF : ∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C2 z =
      decide (∃ (p : Fin a) (l : Fin b), (p, l) ∈ E ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) := by
    intro z
    rw [hfun z, hfunC]
    show (decide (∃ w ∈ (∅ : Finset (Fin (a + b))), (z ∘ σ.symm) w = true) ||
      decide (∃ u v, G.Adj u v ∧ (z ∘ σ.symm) u = true ∧ (z ∘ σ.symm) v = true)) = _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false,
      false_or, Function.comp_apply]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := mixed u v huv
      · exact ⟨p, l, (memE p l).mpr huv, by simpa using hu, by simpa using hv⟩
      · exact ⟨p, l, (memE p l).mpr huv.symm, by simpa using hv, by simpa using hu⟩
    · rintro ⟨p, l, hE, hp, hl⟩
      exact ⟨σ (Fin.castAdd b p), σ (Fin.natAdd a l), (memE p l).mp hE, by simpa using hp,
        by simpa using hl⟩
  obtain ⟨hAO, hRB, h2⟩ := hA
  have getC : ∀ g ∈ C2.gates, ∃ j : Fin C.size, C2.gates.get (e j) = g := by
    intro g hgm
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hgm
    exact ⟨e.symm k, (congrArg C2.gates.get (e.apply_symm_apply k)).trans hk⟩
  have hA2 : PEqualNP.TopForm.IsAO2 (a + b) C2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hgm
      obtain ⟨j, rfl⟩ := getC g hgm
      rw [(hg j).1]
      exact hAO _ (List.mem_iff_get.mpr ⟨j, rfl⟩)
    · intro j hj i hi
      have hgk : PEqualNP.MetaComplexity.NestedCover.gateAt C2 j = C2.gates.get ⟨j, hj⟩ := by
        show C2.gates.getD j _ = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        rfl
      have key : (∀ x9 ∈ (C.gates.get (e.symm ⟨j, hj⟩)).inputs, x9 < a + b + ↑(e.symm ⟨j, hj⟩)) →
          ∀ x10 ∈ (C2.gates.get (e (e.symm ⟨j, hj⟩))).inputs, x10 < a + b + ↑(e (e.symm ⟨j, hj⟩)) :=
        (hg (e.symm ⟨j, hj⟩)).2.2.2.1
      rw [Equiv.apply_symm_apply] at key
      refine key ?_ i (hgk ▸ hi)
      intro x9 hx9
      have hlt : (e.symm ⟨j, hj⟩).val < C.gates.length := (e.symm ⟨j, hj⟩).isLt
      have hgk2 : PEqualNP.MetaComplexity.NestedCover.gateAt C (e.symm ⟨j, hj⟩).val = C.gates.get (e.symm ⟨j, hj⟩) := by
        show C.gates.getD _ _ = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        rfl
      exact hRB _ hlt x9 (hgk2 ▸ hx9)
    · intro g hgm
      obtain ⟨j, rfl⟩ := getC g hgm
      rw [(hg j).2.1]
      exact h2 _ (List.mem_iff_get.mpr ⟨j, rfl⟩)
  have hfour : ∀ (x5 x6 : Fin a) (x7 x8 : Fin b), x5 ≠ x6 → x7 ≠ x8 →
      ¬((x5, x7) ∈ E ∧ (x5, x8) ∈ E ∧ (x6, x7) ∈ E ∧ (x6, x8) ∈ E) := by
    rintro p q l s hpq hls ⟨e1, e2, e3, e4⟩
    have hne : σ (Fin.castAdd b p) ≠ σ (Fin.castAdd b q) := by
      intro h
      exact hpq (by simpa using σ.injective h)
    have hc := four _ _ hne
    have hL : σ (Fin.natAdd a l) ∈ Finset.univ.filter
        (fun w => G.Adj (σ (Fin.castAdd b p)) w ∧ G.Adj (σ (Fin.castAdd b q)) w) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(memE _ _).mp e1, (memE _ _).mp e3⟩
    have hS : σ (Fin.natAdd a s) ∈ Finset.univ.filter
        (fun w => G.Adj (σ (Fin.castAdd b p)) w ∧ G.Adj (σ (Fin.castAdd b q)) w) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(memE _ _).mp e2, (memE _ _).mp e4⟩
    exact hls (by simpa using σ.injective (Finset.card_le_one.mp hc _ hL _ hS))
  obtain ⟨A, B, hcov, hbd⟩ := bound a b E C2 hfour hA2 hF
  refine ⟨A.image (fun p => σ (Fin.castAdd b p)) ∪ B.image (fun l => σ (Fin.natAdd a l)), ?_, ?_⟩
  · intro u v huv
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe]
    obtain ⟨p, l, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := mixed u v huv
    · rcases hcov (p, l) ((memE p l).mpr huv) with h | h
      · exact Or.inl (Or.inl ⟨p, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨l, h, rfl⟩)
    · rcases hcov (p, l) ((memE p l).mpr huv.symm) with h | h
      · exact Or.inr (Or.inl ⟨p, h, rfl⟩)
      · exact Or.inl (Or.inr ⟨l, h, rfl⟩)
  · have hsub : G.edgeFinset ⊆ E.image (fun e => s(σ (Fin.castAdd b e.1), σ (Fin.natAdd a e.2))) := by
      intro x hx
      induction x using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hx
        rw [Finset.mem_image]
        obtain ⟨p, l, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := mixed u v hx
        · exact ⟨(p, l), (memE p l).mpr hx, rfl⟩
        · exact ⟨(p, l), (memE p l).mpr hx.symm, Sym2.eq_swap⟩
    have c1 := Finset.card_le_card hsub
    have c2 := Finset.card_image_le (s := E) (f := fun e => s(σ (Fin.castAdd b e.1), σ (Fin.natAdd a e.2)))
    have c3 := Finset.card_union_le (A.image (fun p => σ (Fin.castAdd b p))) (B.image (fun l => σ (Fin.natAdd a l)))
    have c4 := Finset.card_image_le (s := A) (f := fun p => σ (Fin.castAdd b p))
    have c5 := Finset.card_image_le (s := B) (f := fun l => σ (Fin.natAdd a l))
    omega
