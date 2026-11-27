import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- The missing structural input is a charge from star edges and the matching to the other gates.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_5066_2
    (normalize : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size = C.size)
    (account : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      G.edgeFinset.card + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj]
      (col : Fin (n + n) → Bool) (mate : Fin (n + n) → Fin (n + n)) (C : Circuit),
      NoFourCycle G →
      (∀ a b : Fin n, ¬ G.Adj (Fin.castAdd n a) (Fin.castAdd n b)) →
      (∀ a b : Fin n, ¬ G.Adj (Fin.natAdd n a) (Fin.natAdd n b)) →
      (∀ u v, G.Adj u v → col u ≠ col v) →
      Function.Involutive mate → (∀ u, G.Adj u (mate u)) →
      (∀ u, ∃ v, G.Adj u v ∧ v ≠ mate u) →
      (∀ v, ∃ u, G.Adj u v ∧ u ≠ mate v) →
      IsLeastAO G C → TopForm G C →
      (Ustar G C).card + n ≤ (tops G C \ centreless G C).card + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x12 ≠ x3 x11 ∧ (x11, x12) ∈ x2) ∧ ∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x3 x12 ≠ x11 ∧ (x12, x11) ∈ x2) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro n E p C hdense _ hfree hmatching hmodel heval extra
  rcases extra with ⟨extraRow, extraCol⟩
  classical
  let left : Fin n → Fin (n + n) := Fin.castAdd n
  let right : Fin n → Fin (n + n) := Fin.natAdd n
  have separated (a b : Fin n) : left a ≠ right b := by
    intro h
    have hval := congrArg Fin.val h
    change a.val = n + b.val at hval
    omega
  have left_injective : Function.Injective left := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin (n + n) => x.val) h
  have right_injective : Function.Injective right := by
    intro a b h
    have hval := congrArg Fin.val h
    change n + a.val = n + b.val at hval
    apply Fin.ext
    omega
  have split (x : Fin (n + n)) : (∃ a, x = left a) ∨ (∃ b, x = right b) :=
    Fin.addCases (fun a => Or.inl ⟨a, rfl⟩) (fun b => Or.inr ⟨b, rfl⟩) x
  let rel (x y : Fin (n + n)) : Prop :=
    (∃ a b, (a, b) ∈ E ∧ x = left a ∧ y = right b) ∨
    (∃ a b, (a, b) ∈ E ∧ x = right b ∧ y = left a)
  let G : SimpleGraph (Fin (n + n)) :=
    { Adj := rel
      symm := by
        constructor
        intro x y h
        rcases h with ⟨a, b, he, hx, hy⟩ | ⟨a, b, he, hx, hy⟩
        · exact Or.inr ⟨a, b, he, hy, hx⟩
        · exact Or.inl ⟨a, b, he, hy, hx⟩
      loopless := by
        constructor
        intro x h
        rcases h with ⟨a, b, _, hx, hy⟩ | ⟨a, b, _, hx, hy⟩
        · exact separated a b (hx.symm.trans hy)
        · exact separated a b (hy.symm.trans hx) }
  have lr (a b : Fin n) : G.Adj (left a) (right b) ↔ (a, b) ∈ E := by
    constructor
    · rintro (⟨u, v, he, hu, hv⟩ | ⟨u, v, _, hu, _⟩)
      · have ha := left_injective hu
        have hb := right_injective hv
        simpa [ha, hb] using he
      · exact (separated a v hu).elim
    · exact fun he => Or.inl ⟨a, b, he, rfl, rfl⟩
  have ll (a b : Fin n) : ¬ G.Adj (left a) (left b) := by
    rintro (⟨u, v, _, _, hv⟩ | ⟨u, v, _, hu, _⟩)
    · exact separated b v hv
    · exact separated a v hu
  have rr (a b : Fin n) : ¬ G.Adj (right a) (right b) := by
    rintro (⟨u, v, _, hu, _⟩ | ⟨u, v, _, _, hv⟩)
    · exact separated u a hu.symm
    · exact separated u b hv.symm
  have right_neighbor (a : Fin n) (v : Fin (n + n)) (h : G.Adj (left a) v) :
      ∃ b, v = right b := by
    rcases split v with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact (ll a b h).elim
    · exact ⟨b, rfl⟩
  have left_neighbor (a : Fin n) (v : Fin (n + n)) (h : G.Adj (right a) v) :
      ∃ b, v = left b := by
    rcases split v with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨b, rfl⟩
    · exact (rr a b h).elim
  have no4 : NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases split u with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · obtain ⟨b, rfl⟩ := right_neighbor a x hx'.1
      obtain ⟨c, rfl⟩ := right_neighbor a y hy'.1
      obtain ⟨d, rfl⟩ := left_neighbor b v hx'.2.symm
      by_contra hxy
      exact hfree a d b c (fun h => huv (congrArg left h)) (fun h => hxy (congrArg right h))
        ⟨(lr _ _).mp hx'.1, (lr _ _).mp hy'.1, (lr _ _).mp hx'.2, (lr _ _).mp hy'.2⟩
    · obtain ⟨b, rfl⟩ := left_neighbor a x hx'.1
      obtain ⟨c, rfl⟩ := left_neighbor a y hy'.1
      obtain ⟨d, rfl⟩ := right_neighbor b v hx'.2.symm
      by_contra hxy
      exact hfree b c a d (fun h => hxy (congrArg left h)) (fun h => huv (congrArg right h))
        ⟨(lr _ _).mp hx'.1.symm, (lr _ _).mp hx'.2.symm,
          (lr _ _).mp hy'.1.symm, (lr _ _).mp hy'.2.symm⟩
  let encode (e : Fin n × Fin n) : Sym2 (Fin (n + n)) := s(left e.1, right e.2)
  have encode_injective : Function.Injective encode := by
    intro a b h
    change s(left a.1, right a.2) = s(left b.1, right b.2) at h
    rcases Sym2.eq_iff.mp h with ⟨hleft, hright⟩ | ⟨hbad, _⟩
    · exact Prod.ext (left_injective hleft) (right_injective hright)
    · exact (separated _ _ hbad).elim
  have edges : G.edgeFinset = E.image encode := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      constructor
      · intro h
        have hadj : G.Adj u v := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
        rcases hadj with ⟨a, b, he, rfl, rfl⟩ | ⟨a, b, he, rfl, rfl⟩
        · exact Finset.mem_image.mpr ⟨(a, b), he, rfl⟩
        · exact Finset.mem_image.mpr ⟨(a, b), he, Sym2.eq_swap⟩
      · intro h
        obtain ⟨⟨a, b⟩, he, hsym⟩ := Finset.mem_image.mp h
        rw [← hsym]
        simpa only [encode, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (lr a b).mpr he
  have edge_card : G.edgeFinset.card = E.card := by
    rw [edges, Finset.card_image_of_injective _ encode_injective]
  have nonempty : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos, edge_card]
    omega
  have computes : circuitFun (n + n) C = graphFun G ∅ := by
    funext x
    have equivalence :
        (∃ a b, (a, b) ∈ E ∧ x (left a) = true ∧ x (right b) = true) ↔
        (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
      constructor
      · rintro ⟨a, b, he, ha, hb⟩
        exact ⟨left a, right b, (lr a b).mpr he, ha, hb⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        rcases huv with ⟨a, b, he, rfl, rfl⟩ | ⟨a, b, he, rfl, rfl⟩
        · exact ⟨a, b, he, hu, hv⟩
        · exact ⟨a, b, he, hv, hu⟩
    rw [heval x]
    change decide _ = (decide (∃ a ∈ (∅ : Finset (Fin (n + n))), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    simpa only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
      using decide_eq_decide.mpr equivalence
  have exists_size : ∃ k : ℕ, ∃ D : Circuit,
      IsAO2 (n + n) D ∧ circuitFun (n + n) D = graphFun G ∅ ∧ D.size = k :=
    ⟨C.size, C, hmodel, computes, rfl⟩
  obtain ⟨M, mmodel, mcomputes, msize⟩ := Nat.find_spec exists_size
  have least : IsLeastAO G M := by
    refine ⟨mmodel, mcomputes, ?_⟩
    intro D dmodel dcomputes
    rw [msize]
    exact Nat.find_min' exists_size ⟨D, dmodel, dcomputes, rfl⟩
  have ms_le : M.size ≤ C.size := least.2.2 C hmodel computes
  obtain ⟨D, dleast, dform, dsize⟩ := normalize (n + n) G M nonempty least
  have total := account (n + n) G D no4 nonempty dleast dform
  let col : Fin (n + n) → Bool := fun u => decide (n ≤ u.val)
  have hcolor : ∀ u v, G.Adj u v → col u ≠ col v := by
    intro u v huv
    rcases huv with ⟨a, b, _, rfl, rfl⟩ | ⟨a, b, _, rfl, rfl⟩ <;>
      simp [col, left, right, Nat.not_le_of_lt a.isLt]
  let mate : Fin (n + n) → Fin (n + n) :=
    Fin.addCases (fun a => right (p a)) (fun b => left (p.symm b))
  have mate_left (a : Fin n) : mate (left a) = right (p a) := Fin.addCases_left a
  have mate_right (b : Fin n) : mate (right b) = left (p.symm b) := Fin.addCases_right b
  have hMate : Function.Involutive mate := by
    intro u
    rcases split u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [mate_left, mate_right, p.symm_apply_apply]
    · rw [mate_right, mate_left, p.apply_symm_apply]
  have hMatched : ∀ u, G.Adj u (mate u) := by
    intro u
    rcases split u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [mate_left]
      exact (lr a (p a)).mpr (hmatching a)
    · rw [mate_right]
      have h := hmatching (p.symm b)
      rw [p.apply_symm_apply] at h
      exact ((lr (p.symm b) b).mpr h).symm
  have extraAll : ∀ u : Fin (n + n), ∃ v, G.Adj u v ∧ v ≠ mate u := by
    intro u
    rcases split u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · obtain ⟨c, hcne, hc⟩ := extraRow a
      refine ⟨right c, (lr a c).mpr hc, ?_⟩
      rw [mate_left]
      exact fun heq => hcne (right_injective heq)
    · obtain ⟨a, hane, ha⟩ := extraCol b
      refine ⟨left a, ((lr a b).mpr ha).symm, ?_⟩
      rw [mate_right]
      intro heq
      apply hane
      have ha' : a = p.symm b := left_injective heq
      rw [ha', p.apply_symm_apply]
  have extra := charge n G col mate D no4 ll rr hcolor hMate hMatched extraAll
    (fun v => by
      obtain ⟨u, hadj, hne⟩ := extraAll v
      exact ⟨u, hadj.symm, hne⟩)
    dleast dform
  omega
