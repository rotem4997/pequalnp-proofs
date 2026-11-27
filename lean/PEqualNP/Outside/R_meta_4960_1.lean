import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Assemble the zero-junk side of the coarse bound from a TopForm normal form,
-- the 1491 charge, and emptiness of leftover edges when there is no junk AND.
-- The remaining hypothesis is the same bound for already-normalized circuits
-- that still have a junk gate.
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4960_1
    (hTopForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ u v, G.Adj u v) → IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧ TopForm G C')
    (hCharge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → (∃ u v, G.Adj u v) → IsLeastAO G C → TopForm G C →
        G.edgeSet.ncard + (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤
            C.size + (Ustar G C).card + 1 ∧
        ∀ K : Finset (Fin n),
          IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
            K.card ≤ (tops G C \ centreless G C).card)
    (hUstar : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      (∃ u v, G.Adj u v) → IsLeastAO G C → TopForm G C →
      junk G C = ∅ → Ustar G C = ∅)
    (hJunk : ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (M : Finset (Sym2 (Fin n))),
      NoFourCycle G → (∃ u v, G.Adj u v) → IsLeastAO G C → TopForm G C →
      (junk G C).Nonempty → (∀ e ∈ M, e ∈ G.edgeSet) →
      (∀ e ∈ M, ∀ f ∈ M, ∀ v : Fin n, v ∈ e → v ∈ f → e = f) →
      G.edgeSet.ncard + M.card ≤ C.size + 1 + K * Nat.sqrt (n + 1)) :
  ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 x5 : Finset (Fin x2 × Fin x3)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x7 x8 : Fin x2) (x9 x10 : Fin x3), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x4 ∧ (x7, x10) ∈ x4 ∧ (x8, x9) ∈ x4 ∧ (x8, x10) ∈ x4)) → PEqualNP.TopForm.IsAO2 (x2 + x3) x6 → (∀ (x9 : Fin (x2 + x3) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x3) x6 x9 = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x3), (x10, x11) ∈ x4 ∧ x9 (Fin.castAdd x3 x10) = Bool.true ∧ x9 (Fin.natAdd x2 x11) = Bool.true)) → x5 ⊆ x4 → (∀ x11 ∈ x5, ∀ x13 ∈ x5, x11.1 = x13.1 → x11 = x13) → (∀ x12 ∈ x5, ∀ x14 ∈ x5, x12.2 = x14.2 → x12 = x14) → x4.card + x5.card ≤ x6.size + (1 : ℕ) + x1 * (x2 + x3 + (1 : ℕ)).sqrt := by
  classical
  obtain ⟨K, hJunkK⟩ := hJunk
  refine ⟨K, ?_⟩
  intro np nl E M C hC4 hAO hFun hsub hMpt hMln
  let n : ℕ := np + nl
  let pair : Fin np × Fin nl → Sym2 (Fin n) :=
    fun e => s(Fin.castAdd nl e.1, Fin.natAdd np e.2)
  have pair_ne : ∀ e : Fin np × Fin nl,
      (Fin.castAdd nl e.1 : Fin n) ≠ Fin.natAdd np e.2 := by
    intro e h
    have hp : (Fin.castAdd nl e.1 : ℕ) < np := by simp
    have hl : np ≤ (Fin.natAdd np e.2 : ℕ) := by simp
    have eqv : (Fin.castAdd nl e.1 : ℕ) = (Fin.natAdd np e.2 : ℕ) := congrArg Fin.val h
    omega
  have pair_eq : ∀ (e : Fin np × Fin nl) (p : Fin np) (l : Fin nl),
      pair e = s(Fin.castAdd nl p, Fin.natAdd np l) ↔ e = (p, l) := by
    intro e p l
    constructor
    · intro hs
      rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hp : e.1 = p := Fin.ext (by
          have := congrArg Fin.val h1; simpa using this)
        have hl : e.2 = l := Fin.ext (by
          have := congrArg Fin.val h2; simpa using this)
        exact Prod.ext hp hl
      · have hp : (Fin.castAdd nl e.1 : ℕ) < np := by simp
        have hl : np ≤ (Fin.natAdd np l : ℕ) := by simp
        have eqv : (Fin.castAdd nl e.1 : ℕ) = (Fin.natAdd np l : ℕ) := congrArg Fin.val h1
        omega
    · intro h
      cases h
      rfl
  have pair_inj : Function.Injective pair := by
    intro e e' h
    exact (pair_eq e e'.1 e'.2).mp h
  let G : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (E.image pair)
  have : DecidableRel G.Adj := inferInstance
  have mem_pair : ∀ e : Fin np × Fin nl,
      e ∈ E ↔ G.Adj (Fin.castAdd nl e.1) (Fin.natAdd np e.2) := by
    intro e
    constructor
    · intro he
      exact (SimpleGraph.fromEdgeSet_adj
          (s := (↑(E.image pair) : Set (Sym2 (Fin n))))).mpr
        ⟨Finset.mem_image_of_mem pair he, pair_ne e⟩
    · intro hadj
      have hset := ((SimpleGraph.fromEdgeSet_adj
          (s := (↑(E.image pair) : Set (Sym2 (Fin n))))).mp hadj).1
      obtain ⟨e', he', hs⟩ := Finset.mem_image.mp hset
      exact pair_inj hs ▸ he'
  have ncardE : G.edgeSet.ncard = E.card := by
    have hs : G.edgeSet = ↑(E.image pair) := by
      change (SimpleGraph.fromEdgeSet (↑(E.image pair) : Set (Sym2 (Fin n)))).edgeSet =
        ↑(E.image pair)
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      constructor
      · intro h
        exact h.1
      · intro he
        refine ⟨he, ?_⟩
        intro hdiag
        obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
        have hdiag' : (pair e').IsDiag := (Sym2.mem_diagSet).mp hdiag
        exact pair_ne e' ((Sym2.mk_isDiag_iff).mp hdiag')
    rw [hs, Set.ncard_coe_finset, Finset.card_image_of_injective _ pair_inj]
  have asPt : ∀ v : Fin n, (hv : (v : ℕ) < np) → v = Fin.castAdd nl ⟨v.val, hv⟩ := by
    intro v hv; ext; simp
  have asLn : ∀ v : Fin n, (hv : np ≤ (v : ℕ)) →
      v = Fin.natAdd np ⟨v.val - np, Nat.sub_lt_left_of_lt_add hv v.isLt⟩ := by
    intro v hv; ext; simp [Fin.val_natAdd]; omega
  have adj_to_E : ∀ (u v : Fin n) (hu : (u : ℕ) < np) (hv : np ≤ (v : ℕ)),
      G.Adj u v → (⟨u.val, hu⟩, ⟨v.val - np, Nat.sub_lt_left_of_lt_add hv v.isLt⟩) ∈ E := by
    intro u v hu hv hadj
    have u_eq := asPt u hu
    have v_eq := asLn v hv
    rw [u_eq, v_eq] at hadj
    exact (mem_pair _).mpr hadj
  have opp : ∀ u v : Fin n, G.Adj u v →
      ((u : ℕ) < np ∧ np ≤ (v : ℕ)) ∨ ((v : ℕ) < np ∧ np ≤ (u : ℕ)) := by
    intro u v hadj
    have hmem : s(u, v) ∈ E.image pair :=
      ((SimpleGraph.fromEdgeSet_adj (s := (E.image pair : Set (Sym2 (Fin n))))).mp hadj).1
    obtain ⟨e, he, hs⟩ := Finset.mem_image.mp hmem
    rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨by simp, by simp⟩
    · exact Or.inr ⟨by simp, by simp⟩
  have hNo4 : NoFourCycle G := by
    intro a b hab
    by_contra hmore
    have : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card := by
      have : ¬ (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hmore
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp this
    have hxab : G.Adj a x ∧ G.Adj b x := (Finset.mem_filter.mp hx).2
    have hyab : G.Adj a y ∧ G.Adj b y := (Finset.mem_filter.mp hy).2
    rcases Nat.lt_or_ge (a : ℕ) np with ha | ha
    · rcases Nat.lt_or_ge (b : ℕ) np with hb | hb
      · have hxL : np ≤ (x : ℕ) := by
          rcases opp a x hxab.1 with h | h <;> omega
        have hyL : np ≤ (y : ℕ) := by
          rcases opp a y hyab.1 with h | h <;> omega
        have hap : (⟨a.val, ha⟩ : Fin np) ≠ ⟨b.val, hb⟩ := by
          intro h; exact hab (Fin.ext (congrArg (fun z : Fin np => (z : ℕ)) h))
        have hxl : (⟨x.val - np, Nat.sub_lt_left_of_lt_add hxL x.isLt⟩ : Fin nl) ≠
            ⟨y.val - np, Nat.sub_lt_left_of_lt_add hyL y.isLt⟩ := by
          intro h
          have hv := congrArg (fun z : Fin nl => (z : ℕ)) h
          exact hxy (Fin.ext (by simp at hv; omega))
        exact hC4 _ _ _ _ hap hxl
          ⟨adj_to_E a x ha hxL hxab.1, adj_to_E a y ha hyL hyab.1,
            adj_to_E b x hb hxL hxab.2, adj_to_E b y hb hyL hyab.2⟩
      · rcases opp a x hxab.1 with h1 | h1
        · rcases opp b x hxab.2 with h2 | h2 <;> omega
        · omega
    · rcases Nat.lt_or_ge (b : ℕ) np with hb | hb
      · rcases opp a x hxab.1 with h1 | h1
        · omega
        · rcases opp b x hxab.2 with h2 | h2 <;> omega
      · have hxP : (x : ℕ) < np := by
          rcases opp a x hxab.1 with h | h <;> omega
        have hyP : (y : ℕ) < np := by
          rcases opp a y hyab.1 with h | h <;> omega
        have hxl : (⟨a.val - np, Nat.sub_lt_left_of_lt_add ha a.isLt⟩ : Fin nl) ≠
            ⟨b.val - np, Nat.sub_lt_left_of_lt_add hb b.isLt⟩ := by
          intro h
          have hv := congrArg (fun z : Fin nl => (z : ℕ)) h
          exact hab (Fin.ext (by simp at hv; omega))
        have hap : (⟨x.val, hxP⟩ : Fin np) ≠ ⟨y.val, hyP⟩ := by
          intro h; exact hxy (Fin.ext (congrArg (fun z : Fin np => (z : ℕ)) h))
        exact hC4 _ _ _ _ hap hxl
          ⟨adj_to_E x a hxP ha hxab.1.symm, adj_to_E x b hxP hb hxab.2.symm,
            adj_to_E y a hyP ha hyab.1.symm, adj_to_E y b hyP hb hyab.2.symm⟩
  by_cases hEn : E.Nonempty
  · haveI : Inhabited (Fin n) := ⟨Fin.castAdd nl (Classical.choose hEn).1⟩
    have hGne : ∃ u v, G.Adj u v := by
      obtain ⟨e, he⟩ := hEn
      exact ⟨Fin.castAdd nl e.1, Fin.natAdd np e.2, (mem_pair e).mp he⟩
    have hFunG : circuitFun n C = graphFun G ∅ := by
      funext z
      have hgf : graphFun G ∅ z =
          (decide (∃ a ∈ (∅ : Finset (Fin n)), z a = true) ||
            decide (∃ u v, G.Adj u v ∧ z u = true ∧ z v = true)) := rfl
      rw [hFun z, hgf]
      simp [Finset.notMem_empty]
      constructor
      · rintro ⟨p, l, hp, hz1, hz2⟩
        exact ⟨Fin.castAdd nl p, Fin.natAdd np l, (mem_pair (p, l)).mp hp, hz1, hz2⟩
      · rintro ⟨u, v, hadj, hu, hv⟩
        have hset := ((SimpleGraph.fromEdgeSet_adj
            (s := (↑(E.image pair) : Set (Sym2 (Fin n))))).mp hadj).1
        obtain ⟨e, he, hs⟩ := Finset.mem_image.mp hset
        rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2
          exact ⟨e.1, e.2, he, hu, hv⟩
        · subst h1; subst h2
          exact ⟨e.1, e.2, he, hv, hu⟩
    have hExist : ∃ s, ∃ D : Circuit,
        IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = s :=
      ⟨C.size, C, hAO, hFunG, rfl⟩
    obtain ⟨Cmin, hAOmin, hFunmin, hsz⟩ := Nat.find_spec hExist
    have hLeast : IsLeastAO G Cmin := by
      refine ⟨hAOmin, hFunmin, ?_⟩
      intro D hD hf
      rw [hsz]
      exact Nat.find_min' hExist ⟨D, hD, hf, rfl⟩
    have hsize_le : Cmin.size ≤ C.size := by
      rw [hsz]
      exact Nat.find_min' hExist ⟨C, hAO, hFunG, rfl⟩
    obtain ⟨C', hLeast', hsz', hTop⟩ := hTopForm n G Cmin hGne hLeast
    have hszC : C'.size ≤ C.size := hsz' ▸ hsize_le
    let MG : Finset (Sym2 (Fin n)) := M.image pair
    have cardM : MG.card = M.card := Finset.card_image_of_injective _ pair_inj
    have subM : ∀ e ∈ MG, e ∈ G.edgeSet := by
      intro e he
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
      exact Iff.mpr (SimpleGraph.mem_edgeSet G) ((mem_pair m).mp (hsub hm))
    have matchM : ∀ e ∈ MG, ∀ f ∈ MG, ∀ v : Fin n, v ∈ e → v ∈ f → e = f := by
      intro e he f hf v hve hvf
      obtain ⟨me, hme, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨mf, hmf, rfl⟩ := Finset.mem_image.mp hf
      have hve' : v = Fin.castAdd nl me.1 ∨ v = Fin.natAdd np me.2 :=
        (Sym2.mem_iff).mp hve
      have hvf' : v = Fin.castAdd nl mf.1 ∨ v = Fin.natAdd np mf.2 :=
        (Sym2.mem_iff).mp hvf
      rcases hve' with h1 | h1
      · rcases hvf' with h2 | h2
        · have : me.1 = mf.1 := by
            have := h1.symm.trans h2
            exact Fin.castAdd_inj.mp this
          exact congrArg pair (hMpt me hme mf hmf this)
        · have hp : (v : ℕ) < np := by simp [h1]
          have hl : np ≤ (v : ℕ) := by simp [h2]
          omega
      · rcases hvf' with h2 | h2
        · have hp : (v : ℕ) < np := by simp [h2]
          have hl : np ≤ (v : ℕ) := by simp [h1]
          omega
        · have : me.2 = mf.2 := Fin.ext (by
            have := congrArg Fin.val (h1.symm.trans h2)
            simpa using this)
          exact congrArg pair (hMln me hme mf hmf this)
    have girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length := by
      intro v p hp
      have h3 := hp.three_le_length
      by_contra hlt
      have hle : p.length ≤ 4 := by omega
      have h34 : p.length = 3 ∨ p.length = 4 := by omega
      have adj_i : ∀ i, i < p.length → G.Adj (p.getVert i) (p.getVert (i + 1)) :=
        fun i hi => p.adj_getVert_succ hi
      have p0 : p.getVert 0 = v := p.getVert_zero
      have pend : p.getVert p.length = v := p.getVert_length
      rcases h34 with hlen | hlen
      · have e01 : G.Adj (p.getVert 0) (p.getVert 1) := by
          simpa using adj_i 0 (by omega)
        have e12 : G.Adj (p.getVert 1) (p.getVert 2) := by
          simpa using adj_i 1 (by omega)
        have e20 : G.Adj (p.getVert 2) (p.getVert 0) := by
          have pend3 : p.getVert 3 = v := by rw [← hlen]; exact pend
          have : p.getVert 3 = p.getVert 0 := pend3.trans p0.symm
          simpa [this] using adj_i 2 (by omega)
        rcases opp _ _ e01 with hab | hab
        · rcases opp _ _ e12 with hbc | hbc <;> try omega
          rcases opp _ _ e20 with hca | hca <;> omega
        · rcases opp _ _ e12 with hbc | hbc <;> try omega
          rcases opp _ _ e20 with hca | hca <;> omega
      · have e01 : G.Adj (p.getVert 0) (p.getVert 1) := by
          simpa using adj_i 0 (by omega)
        have e12 : G.Adj (p.getVert 1) (p.getVert 2) := by
          simpa using adj_i 1 (by omega)
        have e23 : G.Adj (p.getVert 2) (p.getVert 3) := by
          simpa using adj_i 2 (by omega)
        have pend4 : p.getVert 4 = v := by rw [← hlen]; exact pend
        have e30 : G.Adj (p.getVert 3) (p.getVert 0) := by
          have : p.getVert 4 = p.getVert 0 := pend4.trans p0.symm
          simpa [this] using adj_i 3 (by omega)
        have inj := hp.getVert_injOn
        have mem1 : 1 ≤ (1 : ℕ) ∧ 1 ≤ p.length := by omega
        have mem2 : 1 ≤ (2 : ℕ) ∧ 2 ≤ p.length := by omega
        have mem3 : 1 ≤ (3 : ℕ) ∧ 3 ≤ p.length := by omega
        have mem4 : 1 ≤ (4 : ℕ) ∧ 4 ≤ p.length := by omega
        have ne02 : p.getVert 0 ≠ p.getVert 2 := by
          intro h
          have h42 : p.getVert 4 = p.getVert 2 := pend4.trans (p0.symm.trans h)
          have := inj mem4 mem2 h42
          omega
        have ne13 : p.getVert 1 ≠ p.getVert 3 := by
          intro h
          have := inj mem1 mem3 h
          omega
        rcases Nat.lt_or_ge (p.getVert 0 : ℕ) np with h0 | h0
        · have h1L : np ≤ (p.getVert 1 : ℕ) := by
            rcases opp _ _ e01 with h | h <;> omega
          have h2P : (p.getVert 2 : ℕ) < np := by
            rcases opp _ _ e12 with h | h <;> omega
          have h3L : np ≤ (p.getVert 3 : ℕ) := by
            rcases opp _ _ e23 with h | h <;> omega
          have hap : (⟨(p.getVert 0).val, h0⟩ : Fin np) ≠ ⟨(p.getVert 2).val, h2P⟩ := by
            intro h
            have hv := congrArg (fun z : Fin np => (z : ℕ)) h
            exact ne02 (Fin.ext (by simpa using hv))
          have hxl : (⟨(p.getVert 1).val - np,
              Nat.sub_lt_left_of_lt_add h1L (p.getVert 1).isLt⟩ : Fin nl) ≠
              ⟨(p.getVert 3).val - np,
              Nat.sub_lt_left_of_lt_add h3L (p.getVert 3).isLt⟩ := by
            intro h
            have hv := congrArg (fun z : Fin nl => (z : ℕ)) h
            have : (p.getVert 1).val = (p.getVert 3).val := by
              simp at hv
              omega
            exact ne13 (Fin.ext this)
          exact hC4 _ _ _ _ hap hxl
            ⟨adj_to_E (p.getVert 0) (p.getVert 1) h0 h1L e01,
              adj_to_E (p.getVert 0) (p.getVert 3) h0 h3L e30.symm,
              adj_to_E (p.getVert 2) (p.getVert 1) h2P h1L e12.symm,
              adj_to_E (p.getVert 2) (p.getVert 3) h2P h3L e23⟩
        · have h1P : (p.getVert 1 : ℕ) < np := by
            rcases opp _ _ e01 with h | h <;> omega
          have h2L : np ≤ (p.getVert 2 : ℕ) := by
            rcases opp _ _ e12 with h | h <;> omega
          have h3P : (p.getVert 3 : ℕ) < np := by
            rcases opp _ _ e23 with h | h <;> omega
          have hap : (⟨(p.getVert 1).val, h1P⟩ : Fin np) ≠ ⟨(p.getVert 3).val, h3P⟩ := by
            intro h
            have hv := congrArg (fun z : Fin np => (z : ℕ)) h
            exact ne13 (Fin.ext (by simpa using hv))
          have hxl : (⟨(p.getVert 0).val - np,
              Nat.sub_lt_left_of_lt_add h0 (p.getVert 0).isLt⟩ : Fin nl) ≠
              ⟨(p.getVert 2).val - np,
              Nat.sub_lt_left_of_lt_add h2L (p.getVert 2).isLt⟩ := by
            intro h
            have hv := congrArg (fun z : Fin nl => (z : ℕ)) h
            have : (p.getVert 0).val = (p.getVert 2).val := by
              simp at hv
              omega
            exact ne02 (Fin.ext this)
          exact hC4 _ _ _ _ hap hxl
            ⟨adj_to_E (p.getVert 1) (p.getVert 0) h1P h0 e01.symm,
              adj_to_E (p.getVert 1) (p.getVert 2) h1P h2L e12,
              adj_to_E (p.getVert 3) (p.getVert 0) h3P h0 e30,
              adj_to_E (p.getVert 3) (p.getVert 2) h3P h2L e23.symm⟩
    have match_le : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (K : Finset (Fin n)),
        H.IsVertexCover (K : Set (Fin n)) →
        (∀ e ∈ MG, e ∈ H.edgeSet) → MG.card ≤ K.card := by
      intro H _ K hK hsubH
      have hexV : ∀ e ∈ MG, ∃ v ∈ K, v ∈ e := by
        intro e he
        induction e using Sym2.ind with
        | _ u w =>
          have hadj : H.Adj u w := Iff.mp (SimpleGraph.mem_edgeSet H) (hsubH _ he)
          rcases hK hadj with hu | hw
          · exact ⟨u, hu, (Sym2.mem_iff).mpr (Or.inl rfl)⟩
          · exact ⟨w, hw, (Sym2.mem_iff).mpr (Or.inr rfl)⟩
      let f : Sym2 (Fin n) → Fin n := fun e =>
        if h : e ∈ MG then Classical.choose (hexV e h) else default
      have hf : ∀ e (he : e ∈ MG), f e ∈ K ∧ f e ∈ e := by
        intro e he
        simpa [f, he] using Classical.choose_spec (hexV e he)
      have maps : Set.MapsTo f ↑MG ↑K := fun e he => (hf e he).1
      have inj : Set.InjOn f ↑MG := by
        intro e he e' he' hfe
        exact matchM e he e' he' (f e) (hf e he).2 (hfe ▸ (hf e' he').2)
      exact Finset.card_le_card_of_injOn f maps inj
    by_cases hJ : (junk G C').Nonempty
    · have hbound :=
        hJunkK n G C' MG hNo4 hGne hLeast' hTop hJ subM matchM
      have : E.card + M.card ≤ C.size + 1 + K * Nat.sqrt (n + 1) := by
        have h1 : E.card + M.card ≤ C'.size + 1 + K * Nat.sqrt (n + 1) := by
          rwa [ncardE, cardM] at hbound
        omega
      simpa [n] using this
    · have hJ0 : junk G C' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      have hU : Ustar G C' = ∅ := hUstar n G C' girth hGne hLeast' hTop hJ0
      obtain ⟨hineq, hcov⟩ := hCharge n G C' hNo4 hGne hLeast' hTop
      have hGdel : G.deleteEdges ↑(Ustar G C') = G := by
        rw [hU]
        simp
      have hexC : ∃ k, ∃ K : Finset (Fin n),
          G.IsVertexCover (K : Set (Fin n)) ∧ K.card = k :=
        ⟨_, Finset.univ, fun _ _ _ => Or.inl (Finset.mem_univ _), rfl⟩
      obtain ⟨Kcov, hKcov, hKcard⟩ := Nat.find_spec hexC
      have hMin : IsMinCover G Kcov := by
        refine ⟨hKcov, ?_⟩
        intro T hT
        rw [hKcard]
        exact Nat.find_min' hexC ⟨T, hT, rfl⟩
      have hMin' : IsMinCover (G.deleteEdges ↑(Ustar G C')) Kcov := by
        rwa [hGdel]
      have hgood := hcov Kcov hMin'
      have hMle : MG.card ≤ Kcov.card :=
        match_le G Kcov hKcov (fun e he => subM e he)
      have : E.card + M.card ≤ C'.size + 1 := by
        have h1 : G.edgeSet.ncard + MG.card ≤ C'.size + (Ustar G C').card + 1 := by
          have := hineq
          omega
        rw [hU, Finset.card_empty, add_zero] at h1
        rwa [← ncardE, ← cardM]
      have : E.card + M.card ≤ C.size + 1 + K * Nat.sqrt (n + 1) := by
        omega
      simpa [n] using this
  · have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEn
    have hM0 : M = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have hxE : x ∈ E := hsub hx
      rw [hE0] at hxE
      exact Finset.notMem_empty _ hxE
    simp [hE0, hM0]
