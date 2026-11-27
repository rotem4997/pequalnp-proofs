import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3527_927
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
        (junk G D).card = (junk G C).card ∧ TopForm G D)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      G.edgeFinset.card + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 ∧
      ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
        K.card ≤ (tops G C \ centreless G C).card)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.IsBipartite → NoFourCycle G → ¬ G.IsAcyclic → IsLeastAO G C → TopForm G C →
      let U := Ustar G C
      U.Nonempty → ∃ K X : Finset (Fin n), IsMinCover (G.deleteEdges ↑U) K ∧
        (∀ e ∈ U, ∃ v ∈ K ∪ X, v ∈ e) ∧
        (K ∪ X).card + U.card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (compileStars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (T : Finset (Fin (n + m))),
      (∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) →
      ∃ D : Circuit, IsAO2 (n + m) D ∧ D.size ≤ E.card + T.card - 1 ∧
        ∀ x : Fin (n + m) → Bool, circuitFun (n + m) D x =
          decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) :
∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → ∃ x15 ∈ x3, x15 ∉ x4 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), x16.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x16 ∧ ∀ (x17 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x16 x17 = Decidable.decide (∃ (x18 : Fin x1) (x19 : Fin x2), (x18, x19) ∈ x3.erase x15 ∧ x17 (Fin.castAdd x2 x18) = Bool.true ∧ x17 (Fin.natAdd x1 x19) = Bool.true) := by
  classical
  intro n m E M C G hG hcyc h4 hC hfun _hsub hleft hright
  let L : Fin n → Fin (n + m) := Fin.castAdd m
  let R : Fin m → Fin (n + m) := Fin.natAdd n
  have hcross (p : Fin n) (l : Fin m) : L p ≠ R l := by
    intro h
    have hh := congrArg Fin.val h
    change p.val = n + l.val at hh
    have := p.isLt
    omega
  have hL : Function.Injective L := by
    intro a b hab
    have hh := congrArg (fun z : Fin (n + m) => z.val) hab
    exact Fin.ext hh
  have hR : Function.Injective R := by
    intro a b hab
    have hh := congrArg Fin.val hab
    change n + a.val = n + b.val at hh
    exact Fin.ext (by omega)
  have side (v : Fin (n + m)) : (∃ p, v = L p) ∨ ∃ l, v = R l := by
    by_cases hv : v.val < n
    · exact Or.inl ⟨⟨v.val, hv⟩, Fin.ext rfl⟩
    · refine Or.inr ⟨⟨v.val - n, by have := v.isLt; omega⟩, ?_⟩
      apply Fin.ext
      change v.val = n + (v.val - n)
      omega
  have adjL (p : Fin n) (v : Fin (n + m)) :
      G.Adj (L p) v ↔ ∃ l, (p, l) ∈ E ∧ v = R l := by
    rw [hG]
    constructor
    · rintro ⟨e, he, ⟨hp, hv⟩ | ⟨_, hp⟩⟩
      · have hh := hL hp
        exact ⟨e.2, by simpa only [hh] using he, hv⟩
      · exact False.elim (hcross _ _ hp)
    · rintro ⟨l, he, rfl⟩
      exact ⟨(p, l), he, Or.inl ⟨rfl, rfl⟩⟩
  have adjR (l : Fin m) (v : Fin (n + m)) :
      G.Adj (R l) v ↔ ∃ p, (p, l) ∈ E ∧ v = L p := by
    rw [hG]
    constructor
    · rintro ⟨e, he, ⟨hl, _⟩ | ⟨hv, hl⟩⟩
      · exact False.elim (hcross _ _ hl.symm)
      · have hh := hR hl
        exact ⟨e.1, by simpa only [hh] using he, hv⟩
    · rintro ⟨p, he, rfl⟩
      exact ⟨(p, l), he, Or.inr ⟨rfl, rfl⟩⟩
  have incidence (p : Fin n) (l : Fin m) : G.Adj (L p) (R l) ↔ (p, l) ∈ E := by
    rw [adjL]
    constructor
    · rintro ⟨l', he, hl⟩
      rwa [← hR hl] at he
    · exact fun he => ⟨l, he, rfl⟩
  have eligible : ∃ e ∈ E, e ∉ M := by
    by_contra! hnone
    have single {u v w : Fin (n + m)} (huv : G.Adj u v) (huw : G.Adj u w) : v = w := by
      rcases side u with ⟨p, rfl⟩ | ⟨l, rfl⟩
      · obtain ⟨a, ha, rfl⟩ := (adjL p v).mp huv
        obtain ⟨b, hb, rfl⟩ := (adjL p w).mp huw
        have key := hleft (p, a) (hnone _ ha) (p, b) (hnone _ hb) rfl
        exact congrArg (fun e : Fin n × Fin m => R e.2) key
      · obtain ⟨a, ha, rfl⟩ := (adjR l v).mp huv
        obtain ⟨b, hb, rfl⟩ := (adjR l w).mp huw
        have key := hright (a, l) (hnone _ ha) (b, l) (hnone _ hb) rfl
        exact congrArg (fun e : Fin n × Fin m => L e.1) key
    apply hcyc
    intro u w hw
    have enough := hw.three_le_length
    have h₀ := w.adj_getVert_succ (i := 0) (by omega)
    have h₁ := w.adj_getVert_succ (i := 1) (by omega)
    have eq := single h₀.symm h₁
    have hn : (0 : ℕ) = 2 := hw.getVert_injOn' (by simp) (by change 2 ≤ w.length - 1; omega) eq
    omega
  obtain ⟨e, he, heM⟩ := eligible
  have hNo4 : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro c hc d hd
    obtain ⟨hac, hbc⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨had, hbd⟩ := (Finset.mem_filter.mp hd).2
    by_contra hcd
    rcases side a with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · obtain ⟨l, hpl, rfl⟩ := (adjL p c).mp hac
      obtain ⟨r, hpr, rfl⟩ := (adjL p d).mp had
      obtain ⟨q, hql, rfl⟩ := (adjR l b).mp hbc.symm
      exact h4 p q l r (fun h => hab (congrArg L h)) (fun h => hcd (congrArg R h))
        ⟨hpl, hpr, hql, (incidence q r).mp hbd⟩
    · obtain ⟨p, hpl, rfl⟩ := (adjR l c).mp hac
      obtain ⟨q, hql, rfl⟩ := (adjR l d).mp had
      obtain ⟨r, hpr, rfl⟩ := (adjL p b).mp hbc.symm
      exact h4 p q l r (fun h => hcd (congrArg L h)) (fun h => hab (congrArg R h))
        ⟨hpl, hpr, hql, (incidence q r).mp hbd.symm⟩
  have hBip : G.IsBipartite := by
    apply SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
    refine ⟨Set.range L, Set.range R, Set.disjoint_left.mpr ?_, ?_⟩
    · rintro _ ⟨p, rfl⟩ ⟨l, hl⟩
      exact hcross p l hl.symm
    · intro a b hab
      rcases (hG a b).mp hab with ⟨d, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨⟨d.1, rfl⟩, ⟨d.2, rfl⟩⟩
      · exact Or.inr ⟨⟨d.2, rfl⟩, ⟨d.1, rfl⟩⟩
  let edge : Fin n × Fin m → Sym2 (Fin (n + m)) := fun d => s(L d.1, R d.2)
  have edge_inj : Function.Injective edge := by
    intro a b h
    rcases Sym2.eq_iff.mp h with ⟨ha, hb⟩ | ⟨ha, _⟩
    · exact Prod.ext (hL ha) (hR hb)
    · exact False.elim (hcross _ _ ha)
  let _ : DecidableRel G.Adj := Classical.decRel _
  have edgeFinset_eq : G.edgeFinset = E.image edge := by
    ext z
    refine Sym2.ind ?_ z
    intro u v
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image, edge,
      Sym2.eq_iff, hG]
    constructor
    · rintro ⟨d, hd, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
      · exact ⟨d, hd, Or.inl ⟨hu.symm, hv.symm⟩⟩
      · exact ⟨d, hd, Or.inr ⟨hv.symm, hu.symm⟩⟩
    · rintro ⟨d, hd, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
      · exact ⟨d, hd, Or.inl ⟨hu.symm, hv.symm⟩⟩
      · exact ⟨d, hd, Or.inr ⟨hv.symm, hu.symm⟩⟩
  have hEdges : G.edgeFinset.Nonempty := by
    rw [edgeFinset_eq]
    exact ⟨edge e, Finset.mem_image_of_mem edge he⟩
  have hcard : G.edgeFinset.card = E.card := by
    rw [edgeFinset_eq, Finset.card_image_of_injective _ edge_inj]
  have computes : circuitFun (n + m) C = graphFun G ∅ := by
    funext x
    change circuitFun (n + m) C x =
      (decide (∃ a ∈ (∅ : Finset (Fin (n + m))), x a = true) ||
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    rw [hfun, Bool.eq_iff_iff]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_iff]
    constructor
    · rintro ⟨p, l, hp, hx, hy⟩
      exact ⟨L p, R l, (incidence p l).mpr hp, hx, hy⟩
    · rintro ⟨u, v, hu, hx, hy⟩
      rcases (hG u v).mp hu with ⟨d, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨d.1, d.2, hd, hx, hy⟩
      · exact ⟨d.1, d.2, hd, hy, hx⟩
  let conjecture (s : ℕ) := ∃ D : Circuit, IsAO2 (n + m) D ∧ circuitFun (n + m) D = graphFun G ∅ ∧ D.size = s
  have existsSize : ∃ s, conjecture s := ⟨C.size, C, hC, computes, rfl⟩
  obtain ⟨Cmin, hCmin, heval, hsz⟩ := Nat.find_spec existsSize
  have hLeast : IsLeastAO G Cmin := ⟨hCmin, heval, fun D hD hDval =>
    hsz ▸ Nat.find_min' existsSize (show conjecture D.size from ⟨D, hD, hDval, rfl⟩)⟩
  have hmin : Cmin.size ≤ C.size := hLeast.2.2 C hC computes
  obtain ⟨D, hDleast, hDsize, _, hDtop⟩ := normalize (n + m) G Cmin hEdges hLeast
  have hc := (charge (n + m) G D hNo4 hEdges hDleast hDtop).1

  have hExtension : ∃ K X : Finset (Fin (n + m)), IsMinCover (G.deleteEdges ↑(Ustar G D)) K ∧
      (∀ e ∈ Ustar G D, ∃ v ∈ K ∪ X, v ∈ e) ∧
      (K ∪ X).card + (Ustar G D).card ≤ (tops G D \ centreless G D).card +
        2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card := by
    by_cases hU : (Ustar G D).Nonempty
    · exact residual (n + m) G D hBip hNo4 hcyc hDleast hDtop hU
    · have hUempty : Ustar G D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      let H := G.deleteEdges ↑(Ustar G D)
      let coverSize (s : ℕ) := ∃ T : Finset (Fin (n + m)), H.IsVertexCover (↑T) ∧ T.card = s
      have univCover : H.IsVertexCover (↑(Finset.univ : Finset (Fin (n + m)))) := by
        intro a b _
        exact Or.inl (by simp)
      have existsCover : ∃ s, coverSize s := ⟨_, Finset.univ, univCover, rfl⟩
      obtain ⟨K, hKcovers, hKcard⟩ := Nat.find_spec existsCover
      have hK : IsMinCover H K := ⟨hKcovers, fun T hT =>
        hKcard ▸ Nat.find_min' existsCover (show coverSize T.card from ⟨T, hT, rfl⟩)⟩
      refine ⟨K, ∅, hK, ?_, ?_⟩
      · intro z hz
        rw [hUempty] at hz
        exact False.elim (Finset.notMem_empty z hz)
      · have hchargeK := (charge (n + m) G D hNo4 hEdges hDleast hDtop).2 K hK
        rw [Finset.union_empty, hUempty, Finset.card_empty, add_zero]
        omega
  obtain ⟨K, X, hK, hX, hb⟩ := hExtension
  have hcov (d : Fin n × Fin m) (hd : d ∈ E) : L d.1 ∈ K ∪ X ∨ R d.2 ∈ K ∪ X := by
    have hadj := (incidence d.1 d.2).mpr hd
    by_cases hmem : edge d ∈ Ustar G D
    · obtain ⟨v, hv, hve⟩ := hX (edge d) hmem
      rcases Sym2.mem_iff.mp hve with hh | hh
      · exact Or.inl (hh ▸ hv)
      · exact Or.inr (hh ▸ hv)
    · have hadj' : (G.deleteEdges ↑(Ustar G D)).Adj (L d.1) (R d.2) :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hmem⟩
      rcases hK.1 hadj' with hv | hv
      · exact Or.inl (Finset.mem_union_left _ hv)
      · exact Or.inr (Finset.mem_union_left _ hv)
  have hbudget : E.card + (K ∪ X).card ≤ C.size + 1 := by
    rw [hcard, hDsize] at hc
    omega
  obtain ⟨F, hF, hFsize, hFval⟩ := compileStars n m (E.erase e) (K ∪ X)
    (fun d hd => hcov d (Finset.mem_of_mem_erase hd))
  refine ⟨e, he, heM, F, ?_, hF, hFval⟩
  rw [Finset.card_erase_of_mem he] at hFsize
  have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨e, he⟩
  have hTpos : 0 < (K ∪ X).card := Finset.card_pos.mpr <|
    (hcov e he).elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  omega
