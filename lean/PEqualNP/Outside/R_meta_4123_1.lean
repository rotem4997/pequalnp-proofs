import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.EquivFin
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4123_1
    (normalForm : ∀ (n s : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (f : (Fin n → Bool) → Bool),
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      H = G.deleteEdges (G.incidenceSet z) →
      (∀ x, f x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
      ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
        (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        gates.length ≤ s ∧
        (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = true ↔
          ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) ∧
        (∀ (i : Fin gates.length) (x : Fin n → Bool),
          (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true →
          ∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true))
    (monotoneBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) :
    ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool), (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) → (x3.neighborSet x5).ncard = (3 : ℕ) → (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → x4 = x3.deleteEdges (x3.incidenceSet x5) → (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 → ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x15 : Fin (x2 + (1 : ℕ)) → Fin x1), ∀ (x16 x17 x18 x19 : Fin x1), x4.Adj x16 x17 → x18 = x19 ∨ x4.Adj x18 x19 → (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧ ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 → (x15 x22 = x16 ∨ x15 x22 = x17) ∧ ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19) := by
  classical
  intro n s G H z f hdeg hz hgirth hH hf hsize
  obtain ⟨gates, out, ops, hlen, heval, hclean⟩ := normalForm n s G H z f hdeg hz hgirth hH hf hsize
  have hle : ∀ a b, H.Adj a b → G.Adj a b := by
    intro a b h
    rw [hH] at h
    exact (SimpleGraph.deleteIncidenceSet_adj.mp h).1
  have tri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → False := by
    intro a b c hab hbc hca
    have hab' := hab.ne
    have hbc' := hbc.ne
    have hca' := hca.ne
    have h := hgirth a (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hca SimpleGraph.Walk.nil))) (by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.isPath_def, hbc', hca', hab'.symm]
      · simp [hab', hbc', hca', hab'.symm, hca'.symm])
    simp at h
  have sq : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d →
      False := by
    intro a b c d hab hbc hcd hda hac hbd
    have hab' := hab.ne
    have hbc' := hbc.ne
    have hcd' := hcd.ne
    have hda' := hda.ne
    have h := hgirth a (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))) (by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.isPath_def, hbc', hcd', hda', hbd, hac.symm, hab'.symm]
      · simp [hab', hbc', hac, hbd, hab'.symm, hda'.symm])
    simp at h
  have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2, h3, h4⟩
    exact sq a b c d (hle _ _ h1) (hle _ _ h2) (hle _ _ h3) (hle _ _ h4) hac hbd
  have heval' : ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩
      (List.ofFn x) = decide (∃ u v : Fin n, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    rw [Bool.eq_iff_iff, heval x, decide_eq_true_iff]
  obtain ⟨T, hT, hcard⟩ := monotoneBound n H h4 gates out ops heval' hclean
  -- two ends of a bad label pair would close a short cycle
  have notboth : ∀ a b v w : Fin n, H.Adj a b → (v = w ∨ H.Adj v w) →
      ((H.Adj v a ∨ H.Adj w a) ∧ a ≠ v ∧ a ≠ w) →
      ((H.Adj v b ∨ H.Adj w b) ∧ b ≠ v ∧ b ≠ w) → False := by
    rintro a b v w hab hvw ⟨ha1, hav, haw⟩ ⟨hb1, hbv, hbw⟩
    have gab := hle _ _ hab
    rcases hvw with rfl | hvw
    · have h1 : H.Adj v a := by rcases ha1 with h | h <;> exact h
      have h2 : H.Adj v b := by rcases hb1 with h | h <;> exact h
      exact tri _ _ _ gab (hle _ _ h2).symm (hle _ _ h1)
    · have gvw := hle _ _ hvw
      rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
      · exact tri _ _ _ gab (hle _ _ h2).symm (hle _ _ h1)
      · exact sq _ _ _ _ gab (hle _ _ h2).symm gvw.symm (hle _ _ h1) haw hbv
      · exact sq _ _ _ _ gab (hle _ _ h2).symm gvw (hle _ _ h1) hav hbw
      · exact tri _ _ _ gab (hle _ _ h2).symm (hle _ _ h1)
  -- owner and other end of each edge
  obtain ⟨ownE, othE, hown⟩ : ∃ ownE othE : Sym2 (Fin n) → Fin n, ∀ a b, H.Adj a b →
      ownE s(a, b) ∈ T ∧ ((ownE s(a, b) = a ∧ othE s(a, b) = b) ∨
        (ownE s(a, b) = b ∧ othE s(a, b) = a)) := by
    refine ⟨fun e => if h : ∃ v ∈ T, v ∈ e then Classical.choose h else z,
      fun e => if h : ∃ v ∈ T, v ∈ e then Sym2.Mem.other (Classical.choose_spec h).2 else z, ?_⟩
    intro a b hab
    have h : ∃ v ∈ T, v ∈ s(a, b) := by
      rcases hT a b hab with h | h
      · exact ⟨a, h, Sym2.mem_mk_left a b⟩
      · exact ⟨b, h, Sym2.mem_mk_right a b⟩
    simp only [dif_pos h]
    have hs := Sym2.other_spec (Classical.choose_spec h).2
    refine ⟨(Classical.choose_spec h).1, ?_⟩
    rw [Sym2.eq_iff] at hs
    exact hs
  let S : Finset (Sym2 (Fin n) ⊕ Fin n) :=
    H.edgeFinset.map Function.Embedding.inl ∪ T.map Function.Embedding.inr
  have hS : S.card ≤ s + 1 := by
    have : S.card = H.edgeFinset.card + T.card := by
      rw [Finset.card_union_of_disjoint]
      · simp
      · rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_map, Function.Embedding.inl_apply,
          Function.Embedding.inr_apply] at hx hx'
        obtain ⟨_, _, rfl⟩ := hx
        obtain ⟨_, _, h⟩ := hx'
        cases h
    omega
  obtain ⟨g⟩ : Nonempty ({u // u ∈ S} ↪ Fin (s + 1)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hS)
  let XX : (Sym2 (Fin n) ⊕ Fin n) → Fin n → Fin n → Prop := fun u a b =>
    Sum.elim (fun e => e = s(a, b)) (fun q => ownE s(a, b) = q) u
  let YY : (Sym2 (Fin n) ⊕ Fin n) → Fin n → Fin n → Prop := fun u v w =>
    Sum.elim (fun e => (H.Adj v (ownE e) ∨ H.Adj w (ownE e)) ∧ ownE e ≠ v ∧ ownE e ≠ w)
      (fun q => ¬ ((H.Adj v q ∨ H.Adj w q) ∧ q ≠ v ∧ q ≠ w)) u
  let LL : (Sym2 (Fin n) ⊕ Fin n) → Fin n := fun u => Sum.elim othE id u
  have key : ∀ a b v w : Fin n, H.Adj a b → (v = w ∨ H.Adj v w) →
      ∃ u0, u0 ∈ S ∧ XX u0 a b ∧ YY u0 v w ∧ (∀ u, XX u a b → YY u v w → u = u0) ∧
        (LL u0 = a ∨ LL u0 = b) ∧
        ¬ ((H.Adj v (LL u0) ∨ H.Adj w (LL u0)) ∧ LL u0 ≠ v ∧ LL u0 ≠ w) := by
    intro a b v w hab hvw
    obtain ⟨hoT, hends⟩ := hown a b hab
    by_cases hb : (H.Adj v (ownE s(a, b)) ∨ H.Adj w (ownE s(a, b))) ∧
        ownE s(a, b) ≠ v ∧ ownE s(a, b) ≠ w
    · refine ⟨Sum.inl s(a, b), ?_, rfl, hb, ?_, ?_, ?_⟩
      · simp [S, hab]
      · intro u hx hy
        cases u with
        | inl e => simp only [XX, Sum.elim_inl] at hx; rw [hx]
        | inr q =>
          simp only [XX, Sum.elim_inr] at hx
          simp only [YY, Sum.elim_inr] at hy
          exact absurd (hx ▸ hb) hy
      · simp only [LL, Sum.elim_inl]
        rcases hends with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
      · simp only [LL, Sum.elim_inl]
        intro hbad
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1] at hb; rw [h2] at hbad
          exact notboth a b v w hab hvw hb hbad
        · rw [h1] at hb; rw [h2] at hbad
          exact notboth a b v w hab hvw hbad hb
    · refine ⟨Sum.inr (ownE s(a, b)), ?_, rfl, hb, ?_, ?_, hb⟩
      · simp [S, hoT]
      · intro u hx hy
        cases u with
        | inl e =>
          simp only [XX, Sum.elim_inl] at hx
          simp only [YY, Sum.elim_inl] at hy
          rw [hx] at hy
          exact absurd hy hb
        | inr q => simp only [XX, Sum.elim_inr] at hx; rw [hx]
      · simp only [LL, Sum.elim_inr, id]
        rcases hends with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  refine ⟨fun i a b => ∃ u : {u // u ∈ S}, g u = i ∧ XX u.1 a b,
    fun i v w => ∃ u : {u // u ∈ S}, g u = i ∧ YY u.1 v w,
    fun i => if h : ∃ u : {u // u ∈ S}, g u = i then LL (Classical.choose h).1 else z, ?_⟩
  intro a b v w hab hvw
  obtain ⟨u0, hu0S, hX0, hY0, huniq, hlab, hgood⟩ := key a b v w hab hvw
  refine ⟨⟨g ⟨u0, hu0S⟩, ⟨⟨⟨u0, hu0S⟩, rfl, hX0⟩, ⟨⟨u0, hu0S⟩, rfl, hY0⟩⟩, ?_⟩, ?_⟩
  · rintro i ⟨⟨u1, hu1, hx⟩, ⟨u2, hu2, hy⟩⟩
    have h12 : u1 = u2 := g.injective (hu1.trans hu2.symm)
    subst h12
    have := huniq u1.1 hx hy
    rw [← hu1]
    congr 1
    exact Subtype.ext this
  · rintro i ⟨u1, hu1, hx⟩ ⟨u2, hu2, hy⟩
    have h12 : u1 = u2 := g.injective (hu1.trans hu2.symm)
    subst h12
    have h0 := huniq u1.1 hx hy
    have hex : ∃ u : {u // u ∈ S}, g u = i := ⟨u1, hu1⟩
    have hch : (Classical.choose hex) = u1 :=
      g.injective ((Classical.choose_spec hex).trans hu1.symm)
    simp only [hex, dite_true, hch, h0]
    exact ⟨hlab, hgood⟩
