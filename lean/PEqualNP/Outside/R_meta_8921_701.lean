import PEqualNP.Defs

open PEqualNP.AndCount

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8921_701
    (antiflag :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 20 →
        let R (v : Fin 42) := Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
        (∀ v, (R v).card ≤ 4) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l → (R p ∪ R l).card ≤ 6) →
        (∃ (t : Fin C.size × Bool) (p l : Fin 42), p.val < 21 ∧ 21 ≤ l.val ∧ ¬ G.Adj p l ∧
          (if t.2 = true then C.leftVars t.1 else C.rightVars t.1) = {p, l}) → False)
    (fourFlags :
      let G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G → C.outVars = ∅ →
        (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 20 →
        let R (v : Fin 42) := Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
        (∀ v, (R v).card ≤ 4) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l → (R p ∪ R l).card ≤ 6) →
        (∃ T : Finset (Fin C.size × Bool), 4 ≤ T.card ∧
          (∀ t ∈ T, ∃ p l : Fin 42, G.Adj p l ∧
            (if t.2 = true then C.leftVars t.1 else C.rightVars t.1) = {p, l}) ∧
          ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
            Disjoint (if t.2 = true then C.leftVars t.1 else C.rightVars t.1)
              (if t'.2 = true then C.leftVars t'.1 else C.rightVars t'.1)) → False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x2.WellFormed →     x2.Computes x1 →       x2.outVars = ∅ →         (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) →           (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) →             x2.size = (20 : ℕ) →               have x9 : Finset (Fin (42 : ℕ)) → ℕ := fun (x9 : Finset (Fin (42 : ℕ))) => {x10 : Fin x2.size | ((∃ x11 ∈ x2.leftVars x10, x11 ∈ x9) ∨ ∃ x11 ∈ x2.leftGates x10, x2.gateVal x9 x11 = Bool.true) ∨ (∃ x11 ∈ x2.rightVars x10, x11 ∈ x9) ∨ ∃ x11 ∈ x2.rightGates x10, x2.gateVal x9 x11 = Bool.true}.ncard;               (∀ (x10 : Fin (42 : ℕ)), x9 {x10} ≤ (4 : ℕ)) → (∀ (x11 x12 : Fin (42 : ℕ)), ↑x11 < (21 : ℕ) → (21 : ℕ) ≤ ↑x12 → ¬x1.Adj x11 x12 → x9 {x11, x12} ≤ (6 : ℕ)) → False := by
  dsimp only at antiflag fourFlags ⊢
  intro C wf comp noOut noSingle disj size capRaw pairsRaw
  classical
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin 42),
      G = SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) =>
        ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] := ⟨_, rfl⟩
  rw [← hG] at comp pairsRaw
  let R (v : Fin 42) : Finset (Fin C.size) :=
    Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
  have capF : ∀ v : Fin 42, (R v).card ≤ 4 := by
    intro v
    have hsub : (↑(R v) : Set (Fin C.size)) ⊆
        {x10 : Fin C.size |
          ((∃ x11 ∈ C.leftVars x10, x11 ∈ ({v} : Finset (Fin 42))) ∨
            ∃ x11 ∈ C.leftGates x10, C.gateVal {v} x11 = Bool.true) ∨
          (∃ x11 ∈ C.rightVars x10, x11 ∈ ({v} : Finset (Fin 42))) ∨
            ∃ x11 ∈ C.rightGates x10, C.gateVal {v} x11 = Bool.true} := by
      intro i hi
      simp only [R, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with hL | hR
      · exact Or.inl (Or.inl ⟨v, hL, Finset.mem_singleton_self v⟩)
      · exact Or.inr (Or.inl ⟨v, hR, Finset.mem_singleton_self v⟩)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hle
    exact hle.trans (capRaw v)
  have pairsF : ∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l → (R p ∪ R l).card ≤ 6 := by
    intro p l hp hl hna
    have hsub : (↑(R p ∪ R l) : Set (Fin C.size)) ⊆
        {x10 : Fin C.size |
          ((∃ x11 ∈ C.leftVars x10, x11 ∈ ({p, l} : Finset (Fin 42))) ∨
            ∃ x11 ∈ C.leftGates x10, C.gateVal {p, l} x11 = Bool.true) ∨
          (∃ x11 ∈ C.rightVars x10, x11 ∈ ({p, l} : Finset (Fin 42))) ∨
            ∃ x11 ∈ C.rightGates x10, C.gateVal {p, l} x11 = Bool.true} := by
      intro i hi
      simp only [R, Finset.mem_coe, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with (hL | hR) | (hL | hR)
      · exact Or.inl (Or.inl ⟨p, hL, Finset.mem_insert_self p {l}⟩)
      · exact Or.inr (Or.inl ⟨p, hR, Finset.mem_insert_self p {l}⟩)
      · exact Or.inl (Or.inl ⟨l, hL, Finset.mem_insert_of_mem (Finset.mem_singleton_self l)⟩)
      · exact Or.inr (Or.inl ⟨l, hR, Finset.mem_insert_of_mem (Finset.mem_singleton_self l)⟩)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hle
    exact hle.trans (pairsRaw p l hp hl hna)
  have antiflag' := antiflag C wf (hG ▸ comp) noOut disj size capF (hG ▸ pairsF)
  have fourFlags' := fourFlags C wf (hG ▸ comp) noOut disj size capF (hG ▸ pairsF)
  rw [← hG] at antiflag' fourFlags'
  clear antiflag fourFlags capRaw pairsRaw
  have hadj : ∀ a b : Fin 42, G.Adj a b ↔
      ((a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ [0, 5, 7, 17, 20]) ∨
        (b.val < 21 ∧ 21 ≤ a.val ∧ (a.val + 21 - b.val) % 21 ∈ [0, 5, 7, 17, 20])) := by
    intro a b
    rw [hG, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega
  have hcol : ∀ a b : Fin 42, G.Adj a b → ¬ (a.val < 21 ↔ b.val < 21) := by
    intro a b h
    rcases (hadj a b).mp h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega
  obtain ⟨nb, hnb, hnbU⟩ : ∃ nb : Fin 42 → Fin 5 → Fin 42,
      (∀ (v : Fin 42) (k : Fin 5),
        ((v.val < 21 ∧ 21 ≤ (nb v k).val ∧ ((nb v k).val + 21 - v.val) % 21 ∈ [0, 5, 7, 17, 20]) ∨
          ((nb v k).val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - (nb v k).val) % 21 ∈ [0, 5, 7, 17, 20]))) ∧
      (∀ (v x : Fin 42), (x.val < 21 ↔ v.val < 21) → ∀ (k k' : Fin 5), k ≠ k' →
        ((x.val < 21 ∧ 21 ≤ (nb v k).val ∧ ((nb v k).val + 21 - x.val) % 21 ∈ [0, 5, 7, 17, 20]) ∨
          ((nb v k).val < 21 ∧ 21 ≤ x.val ∧ (x.val + 21 - (nb v k).val) % 21 ∈ [0, 5, 7, 17, 20])) →
        ((x.val < 21 ∧ 21 ≤ (nb v k').val ∧ ((nb v k').val + 21 - x.val) % 21 ∈ [0, 5, 7, 17, 20]) ∨
          ((nb v k').val < 21 ∧ 21 ≤ x.val ∧ (x.val + 21 - (nb v k').val) % 21 ∈ [0, 5, 7, 17, 20])) →
        x = v) := by
    refine ⟨fun v k => if v.val < 21
        then Fin.ofNat 42 (21 + (v.val + (![0, 5, 7, 17, 20] : Fin 5 → ℕ) k) % 21)
        else Fin.ofNat 42 ((v.val - (![0, 5, 7, 17, 20] : Fin 5 → ℕ) k) % 21), ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  have hnbAdj : ∀ v k, G.Adj v (nb v k) := fun v k => (hadj v (nb v k)).mpr (hnb v k)
  obtain ⟨bare, hbare⟩ : ∃ bare : Fin C.size × Bool → Finset (Fin 42),
      ∀ t, bare t = if t.2 = true then C.leftVars t.1 else C.rightVars t.1 := ⟨_, fun _ => rfl⟩
  have bareL : ∀ i, bare (i, true) = C.leftVars i := fun i => by rw [hbare]; simp
  have bareR : ∀ i, bare (i, false) = C.rightVars i := fun i => by rw [hbare]; simp
  have evalEq : ∀ U V : Finset (Fin 42),
      (∀ t, (∃ x ∈ bare t, x ∈ U) ↔ (∃ x ∈ bare t, x ∈ V)) → C.eval U = C.eval V := by
    intro U V h
    have fuel : ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = C.gateValFuel V d i := by
      intro d
      induction d with
      | zero => intro i; rfl
      | succ d ih =>
        intro i
        have hfun : C.gateValFuel U d = C.gateValFuel V d := funext ih
        have hl := h (i, true)
        have hr := h (i, false)
        rw [bareL] at hl
        rw [bareR] at hr
        show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i
              (C.gateValFuel U d) &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i
              (C.gateValFuel U d)) =
          (PEqualNP.AndCount.AndCountCircuit.sideTrue V (C.leftVars i) (C.leftGates i) i
              (C.gateValFuel V d) &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue V (C.rightVars i) (C.rightGates i) i
              (C.gateValFuel V d))
        delta PEqualNP.AndCount.AndCountCircuit.sideTrue
        simp only [hfun, hl, hr]
    have gv : ∀ i, C.gateVal U i = C.gateVal V i := fun i => fuel C.size i
    delta PEqualNP.AndCount.AndCountCircuit.eval
    simp only [noOut, Finset.notMem_empty, false_and, exists_false, false_or, gv]
  have sep : ∀ (U : Finset (Fin 42)) (v w : Fin 42), (∀ a ∈ U, ∀ b ∈ U, ¬ G.Adj a b) → w ∈ U →
      G.Adj v w → ∃ t, v ∈ bare t ∧ ∀ x ∈ bare t, x ∉ U := by
    intro U v w hind hw hvw
    by_contra hne
    push Not at hne
    have he := evalEq U (insert v U) (fun t => by
      constructor
      · rintro ⟨x, hx, hxU⟩
        exact ⟨x, hx, Finset.mem_insert_of_mem hxU⟩
      · rintro ⟨x, hx, hxU⟩
        rcases Finset.mem_insert.mp hxU with rfl | hxU
        · exact hne t hx
        · exact ⟨x, hx, hxU⟩)
    have h0 : C.eval U ≠ true := by
      intro h
      obtain ⟨a, ha, c, hc, hac⟩ := (comp U).mp h
      exact hind a ha c hc hac
    have h1 : C.eval (insert v U) = true :=
      (comp _).mpr ⟨v, Finset.mem_insert_self v U, w, Finset.mem_insert_of_mem hw, hvw⟩
    exact h0 (he.trans h1)
  have sameSide : ∀ (v : Fin 42) (s t : Fin C.size × Bool), v ∈ bare s → v ∈ bare t →
      s.1 = t.1 → s = t := by
    rintro v ⟨i, b⟩ ⟨j, c⟩ hs ht (rfl : i = j)
    cases b <;> cases c
    · rfl
    · rw [bareR] at hs
      rw [bareL] at ht
      exact (Finset.disjoint_left.mp (disj i) ht hs).elim
    · rw [bareL] at hs
      rw [bareR] at ht
      exact (Finset.disjoint_left.mp (disj i) hs ht).elim
    · rfl
  have priv : ∀ v : Fin 42, ∃ t, v ∈ bare t ∧
      ∀ u ∈ bare t, (u.val < 21 ↔ v.val < 21) → u = v := by
    intro v
    have step : ∀ k : Fin 5, ∃ t, v ∈ bare t ∧ ∀ x ∈ bare t,
        x ∉ insert (nb v k) (Finset.univ.filter
          (fun x : Fin 42 => (x.val < 21 ↔ v.val < 21) ∧ ¬ G.Adj x (nb v k))) := by
      intro k
      apply sep _ v (nb v k) _ (Finset.mem_insert_self _ _) (hnbAdj v k)
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hcol _ _ hab Iff.rfl
        · exact (Finset.mem_filter.mp hb).2.2 hab.symm
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (Finset.mem_filter.mp ha).2.2 hab
        · exact hcol _ _ hab ((Finset.mem_filter.mp ha).2.1.trans (Finset.mem_filter.mp hb).2.1.symm)
    choose t ht1 ht2 using step
    have maps : ∀ k ∈ (Finset.univ : Finset (Fin 5)), (t k).1 ∈ R v := by
      intro k _
      have h := ht1 k
      rw [hbare] at h
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hb : (t k).2 = true
      · simp only [hb, ite_true] at h
        exact Or.inl h
      · simp only [hb] at h
        exact Or.inr h
    have lt : (R v).card < (Finset.univ : Finset (Fin 5)).card := by
      have := capF v
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨k, _, k', _, hkk, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to lt maps
    have hside : t k = t k' := sameSide v _ _ (ht1 k) (ht1 k') heq
    refine ⟨t k, ht1 k, ?_⟩
    intro u hu hc
    have a1 : G.Adj u (nb v k) := by
      by_contra hn
      exact ht2 k u hu (Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hn⟩))
    have a2 : G.Adj u (nb v k') := by
      by_contra hn
      exact ht2 k' u (hside ▸ hu) (Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hn⟩))
    exact hnbU v u hc k k' hkk ((hadj _ _).mp a1) ((hadj _ _).mp a2)
  have pure : ∀ v : Fin 42, ∃ t, v ∈ bare t ∧ ∀ u ∈ bare t, (u.val < 21 ↔ v.val < 21) := by
    intro v
    obtain ⟨t, h1, h2⟩ := sep (Finset.univ.filter (fun x : Fin 42 => ¬ (x.val < 21 ↔ v.val < 21)))
      v (nb v 0)
      (by
        intro a ha b hb hab
        have ca := (Finset.mem_filter.mp ha).2
        have cb := (Finset.mem_filter.mp hb).2
        apply hcol _ _ hab
        omega)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hcol _ _ (hnbAdj v 0) h.symm⟩)
      (hnbAdj v 0)
    refine ⟨t, h1, fun u hu => ?_⟩
    by_contra hn
    exact h2 u hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  choose π πmem πpriv using priv
  choose ρ ρmem ρpure using pure
  have πinj : ∀ v w : Fin 42, (w.val < 21 ↔ v.val < 21) → π v = π w → v = w := by
    intro v w hc h
    have hw : w ∈ bare (π v) := h ▸ πmem w
    exact (πpriv v w hw hc).symm
  have cardP : (Finset.univ.filter (fun v : Fin 42 => v.val < 21)).card = 21 := by decide
  have cardL : (Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).card = 21 := by decide
  have cardA : ((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π).card = 21 := by
    rw [Finset.card_image_of_injOn, cardP]
    intro v hv w hw h
    have hv' := (Finset.mem_filter.mp hv).2
    have hw' := (Finset.mem_filter.mp hw).2
    exact πinj v w (iff_of_true hw' hv') h
  have cardB : ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π).card = 21 := by
    rw [Finset.card_image_of_injOn, cardL]
    intro v hv w hw h
    have hv' := (Finset.mem_filter.mp hv).2
    have hw' := (Finset.mem_filter.mp hw).2
    exact πinj v w (iff_of_false hw' hv') h
  have cardS : Fintype.card (Fin C.size × Bool) = 40 := by
    simp [Fintype.card_prod, size]
  have tally := Finset.card_union_add_card_inter
    ((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π)
    ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π)
  have memT : ∀ t, t ∈ ((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π) ∩
      ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π) →
      ∃ p l : Fin 42, p.val < 21 ∧ ¬ l.val < 21 ∧ π p = t ∧ π l = t ∧ bare t = {p, l} := by
    intro t ht
    obtain ⟨hA, hB⟩ := Finset.mem_inter.mp ht
    obtain ⟨p, hpm, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨l, hlm, hlp⟩ := Finset.mem_image.mp hB
    have hp' := (Finset.mem_filter.mp hpm).2
    have hl' := (Finset.mem_filter.mp hlm).2
    refine ⟨p, l, hp', hl', rfl, hlp, ?_⟩
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hu
      by_cases hc : u.val < 21
      · exact Or.inl (πpriv p u hu (iff_of_true hc hp'))
      · exact Or.inr (πpriv l u (hlp ▸ hu) (iff_of_false hc hl'))
    · rintro (rfl | rfl)
      · exact πmem _
      · exact hlp ▸ πmem _
  have two0 : 2 ≤ (((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π) ∩
      ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π)).card := by
    have h := Finset.card_le_univ (((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π) ∪
      ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π))
    omega
  obtain ⟨a, ha⟩ : ∃ a, a ∈ ((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π) ∩
      ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π) :=
    Finset.card_pos.mp (by omega)
  obtain ⟨p, l, hp, hl, πp, πl, _⟩ := memT a ha
  have notπ : ∀ q q' : Fin 42, π q = π q' → ¬ (q'.val < 21 ↔ q.val < 21) → ∀ v, π v ≠ ρ q := by
    intro q q' hqq hc v hv
    have h1 : (v.val < 21 ↔ q.val < 21) := ρpure q v (hv ▸ πmem v)
    have h2 : q = v := πpriv v q (hv ▸ ρmem q) h1.symm
    subst h2
    have h3 : q' ∈ bare (ρ q) := by
      rw [← hv, hqq]
      exact πmem q'
    exact hc (ρpure q q' h3)
  have np : ∀ v, π v ≠ ρ p := notπ p l (πp.trans πl.symm) (fun h => hl (h.mpr hp))
  have nl : ∀ v, π v ≠ ρ l := notπ l p (πl.trans πp.symm) (fun h => hl (h.mp hp))
  have ne : ρ p ≠ ρ l := by
    intro h
    have hpl := ρpure l p (h ▸ ρmem p)
    exact hl (hpl.mp hp)
  have sub : ((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π) ∪
      ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π) ⊆
      (Finset.univ.erase (ρ p)).erase (ρ l) := by
    intro s hs
    have : ∃ v, π v = s := by
      rcases Finset.mem_union.mp hs with h | h
      · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h
        exact ⟨v, rfl⟩
      · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h
        exact ⟨v, rfl⟩
    obtain ⟨v, rfl⟩ := this
    exact Finset.mem_erase.mpr ⟨nl v, Finset.mem_erase.mpr ⟨np v, Finset.mem_univ _⟩⟩
  have c38 : ((Finset.univ.erase (ρ p)).erase (ρ l)).card = 38 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, cardS]
  have four : 4 ≤ (((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π) ∩
      ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π)).card := by
    have h := Finset.card_le_card sub
    omega
  by_cases hanti : ∃ t ∈ ((Finset.univ.filter (fun v : Fin 42 => v.val < 21)).image π) ∩
      ((Finset.univ.filter (fun v : Fin 42 => ¬ v.val < 21)).image π),
      ∃ p l : Fin 42, p.val < 21 ∧ 21 ≤ l.val ∧ ¬ G.Adj p l ∧ bare t = {p, l}
  · obtain ⟨t, _, p, l, h1, h2, h3, h4⟩ := hanti
    exact antiflag' ⟨t, p, l, h1, h2, h3, (hbare t) ▸ h4⟩
  · apply fourFlags'
    refine ⟨_, four, ?_, ?_⟩
    · intro t ht
      obtain ⟨p, l, hp, hl, _, _, hb⟩ := memT t ht
      refine ⟨p, l, ?_, (hbare t) ▸ hb⟩
      by_contra hn
      exact hanti ⟨t, ht, p, l, hp, by omega, hn, hb⟩
    · intro t ht t' ht' htt
      obtain ⟨p, l, hp, hl, πp, πl, hb⟩ := memT t ht
      obtain ⟨p', l', hp', hl', πp', πl', hb'⟩ := memT t' ht'
      rw [← hbare t, ← hbare t', hb, hb']
      have e1 : p ≠ p' := fun h => htt (πp.symm.trans ((congrArg π h).trans πp'))
      have e2 : l ≠ l' := fun h => htt (πl.symm.trans ((congrArg π h).trans πl'))
      have e3 : p ≠ l' := fun h => hl' (h ▸ hp)
      have e4 : l ≠ p' := fun h => hl (h ▸ hp')
      rw [Finset.disjoint_left]
      intro u hu hu'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
      rcases hu with rfl | rfl <;> rcases hu' with h | h
      · exact e1 h
      · exact e3 h
      · exact e4 h
      · exact e2 h
