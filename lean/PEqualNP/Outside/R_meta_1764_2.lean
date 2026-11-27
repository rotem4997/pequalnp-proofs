import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1764_2
    (h_delete : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (walk : G.Walk v v), walk.IsCycle → 5 ≤ walk.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ (k : ℕ) (T : Finset (Sym2 (Fin n))), T ⊆ G.edgeFinset →
      (∀ e ∈ T, ∃ u v : Fin n, e = s(u,v) ∧ ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v ∧
        ∃ B : Finset (Fin n), B.card ≤ k ∧ u ∉ B ∧ v ∉ B ∧
          ∀ p ∉ B, ∀ q ∉ B, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q) →
      T.card ≤ 2^(k+2)*C.size)
    (h_pack : ∃ m c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (walk : G.Walk v v), walk.IsCycle → 5 ≤ walk.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ T ⊆ G.edgeFinset,
        (∀ e ∈ T, ∀ u v : Fin n, e = s(u,v) → ∀ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v →
          let onPair := fun p q : Fin n => PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true
          let outside := fun t : Fin n × Fin n => ({t.1,t.2} : Finset (Fin n)) \ {u,v}
          onPair u u ∨ onPair v v ∨ ∃ F : Finset (Fin n × Fin n), F.card = m+3 ∧
            (∀ t ∈ F, onPair t.1 t.2 ∧ ¬ G.Adj t.1 t.2) ∧
            ∀ t ∈ F, ∀ w ∈ F, t ≠ w → Disjoint (outside t) (outside w)) →
        T.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨m,c,hc⟩ := h_pack
  let k := 2*(m+2)
  refine ⟨2^(k+2)+c, ?_⟩
  intro n G inst degrees girth givenC givenMono givenFun
  -- Counting all edges in a least circuit gives a bound for every subset in the original circuit.
  let candidates (s : ℕ) := ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = s ∧ PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
  have existsSize : ∃ s, candidates s := ⟨givenC.size,givenC,rfl,givenMono,givenFun⟩
  obtain ⟨C,sizeEq,mono,computes⟩ := Nat.find_spec existsSize
  have least : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C := by
    refine ⟨mono, fun D dMono same => ?_⟩
    exact sizeEq.le.trans (Nat.find_min' existsSize ⟨D,rfl,dMono,same.trans computes⟩)
  have cost := least.2 givenC givenMono (givenFun.trans computes.symm)
  apply le_trans (Finset.card_filter_le _ _)
  apply le_trans _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right cost 1))
  let goalEdges := G.edgeFinset
  let shield := fun e : Sym2 (Fin n) => ∃ u v : Fin n, e = s(u,v) ∧
    ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v ∧ ∃ B : Finset (Fin n),
      B.card ≤ k ∧ u ∉ B ∧ v ∉ B ∧
        ∀ p ∉ B, ∀ q ∉ B, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q
  let A := goalEdges.filter shield
  let D := goalEdges \ A
  have graphmem {e} (he : e ∈ goalEdges) : e ∈ G.edgeFinset := he
  have ha := h_delete n G girth C mono k A
    (fun _ he => graphmem (Finset.mem_filter.mp he).1) (fun _ he => (Finset.mem_filter.mp he).2)
  have hd : D.card ≤ c*(C.size+1) := by
    apply hc n G degrees girth C least computes D (fun _ he => graphmem (Finset.mem_sdiff.mp he).1)
    intro e he u v eq j owns
    dsimp only
    by_cases atU : PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u u) = true
    · exact Or.inl atU
    by_cases atV : PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput v v) = true
    · exact Or.inr (Or.inl atV)
    right; right
    let allowed : Finset (Fin n) := Finset.univ \ {u,v}
    let outside (t : Fin n × Fin n) := ({t.1,t.2} : Finset (Fin n)) \ {u,v}
    let bad (t : Fin n × Fin n) := PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput t.1 t.2) = true ∧ ¬G.Adj t.1 t.2
    have edge : G.Adj u v := by
      have mem := graphmem (Finset.mem_sdiff.mp he).1
      simpa [eq] using mem
    have small (t) : (outside t).card ≤ 2 :=
      (Finset.card_le_card Finset.sdiff_subset).trans
        ((Finset.card_insert_le _ _).trans (by simp))
    have inside (t) : outside t ⊆ allowed := fun _ hx =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have nz (t) (ht : bad t) : (outside t).Nonempty := by
      by_contra! empty
      have endpoints (x) (hx : x ∈ ({t.1,t.2} : Finset (Fin n))) : x = u ∨ x = v := by
        by_contra! miss
        have hit : x ∈ outside t := Finset.mem_sdiff.mpr ⟨hx,by simp [miss.1,miss.2]⟩
        simp [empty] at hit
      rcases endpoints t.1 (by simp) with a|a <;> rcases endpoints t.2 (by simp) with b|b
      · exact atU (by simpa only [a,b] using ht.1)
      · exact ht.2 (a ▸ b ▸ edge)
      · exact ht.2 (a ▸ b ▸ edge.symm)
      · exact atV (by simpa only [a,b] using ht.1)
    -- Removing the outside vertices of earlier tests forces a new test disjoint from them.
    have more (B : Finset (Fin n)) (sub : B ⊆ allowed) (cap : B.card ≤ 2*(m+2)) :
        ∃ t, bad t ∧ Disjoint (outside t) B := by
      have avoidU : u ∉ B := fun h => (Finset.mem_sdiff.mp (sub h)).2 (by simp)
      have avoidV : v ∉ B := fun h => (Finset.mem_sdiff.mp (sub h)).2 (by simp)
      have leaks : ¬ ∀ p ∉ B, ∀ q ∉ B, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q := by
        intro clean
        exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp he).1, u,v,eq,j,owns,B,cap,avoidU,avoidV,clean⟩)
      push Not at leaks
      obtain ⟨p,hp,q,hq,on,nonedge⟩ := leaks
      refine ⟨(p,q),⟨on,nonedge⟩,Finset.disjoint_left.mpr ?_⟩
      intro x hx
      have h : x = p ∨ x = q := by simpa using (Finset.mem_sdiff.mp hx).1
      rcases h with rfl|rfl
      · exact hp
      · exact hq
    suffices aux : ∀ r ≤ (m+2)+1, ∃ F : Finset (Fin n × Fin n), F.card = r ∧ (∀ t∈F, bad t) ∧
        ∀ t∈F, ∀ w∈F, t ≠ w → Disjoint (outside t) (outside w) from aux _ le_rfl
    intro r
    induction r with
    | zero => intro _; exact ⟨∅,by simp,by simp,by simp⟩
    | succ r ih =>
      intro hr
      obtain ⟨F,hF,hok,dis⟩ := ih (by omega)
      let B := F.biUnion outside
      have incl : B ⊆ allowed := by
        intro x hx
        obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hx
        exact inside t ht
      have cap : B.card ≤ 2*(m+2) := calc
        B.card ≤ ∑ t∈F, (outside t).card := Finset.card_biUnion_le
        _ ≤ ∑ _t∈F, 2 := Finset.sum_le_sum (fun t _ => small t)
        _ ≤ 2*(m+2) := by simp [hF]; omega
      obtain ⟨a,ha,hnew⟩ := more B incl cap
      have cross (b) (hb : b ∈ F) : Disjoint (outside a) (outside b) :=
        hnew.mono_right (Finset.subset_biUnion_of_mem outside hb)
      have fresh : a ∉ F := by
        intro old
        obtain ⟨x,hx⟩ := nz a ha
        exact Finset.disjoint_left.mp (cross a old) hx hx
      refine ⟨insert a F, by simp [fresh,hF], ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl|ht
        · exact ha
        · exact hok t ht
      · intro t ht w hw ne
        by_cases eqt : t = a
        · subst t
          exact cross w ((Finset.mem_insert.mp hw).resolve_left ne.symm)
        · have oldt := (Finset.mem_insert.mp ht).resolve_left eqt
          by_cases eqw : w = a
          · subst w
            exact (cross t oldt).symm
          · exact dis t oldt w ((Finset.mem_insert.mp hw).resolve_left eqw) ne
  have total : goalEdges.card ≤ D.card+A.card := Finset.card_le_card_sdiff_add_card
  rw [Nat.add_mul]
  have hscale := Nat.mul_le_mul_left (2^(k+2)) (Nat.le_succ C.size)
  exact total.trans ((Nat.add_le_add hd (ha.trans hscale)).trans_eq (Nat.add_comm _ _))
