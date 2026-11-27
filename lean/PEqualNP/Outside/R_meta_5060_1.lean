import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5060_1
    (h1 : (have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun (a b : Fin 42) => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ c : PEqualNP.AndCount.AndCountCircuit 42, c.WellFormed → c.Computes G → c.outVars = ∅ →
        (∀ (i : Fin c.size) (v : Fin 42), c.gateVal {v} i = false) →
        (∀ i : Fin c.size, Disjoint (c.leftVars i) (c.rightVars i)) → c.size = 19 →
        (∀ v : Fin 42, {i : Fin c.size | v ∈ c.leftVars i ∨ v ∈ c.rightVars i}.ncard ≤ 3) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
          {i : Fin c.size | p ∈ c.leftVars i ∨ p ∈ c.rightVars i ∨ l ∈ c.leftVars i ∨ l ∈ c.rightVars i}.ncard ≤ 5) →
        (∃ i : Fin c.size, (∃ a ∈ c.leftVars i, ∃ b ∈ c.rightVars i, ¬ G.Adj a b) ∧ ∀ j : Fin c.size, (∃ a ∈ c.leftVars j, ∃ b ∈ c.rightVars j, ¬ G.Adj a b) → j = i) → False))
    (h2 : (have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun (a b : Fin 42) => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ c : PEqualNP.AndCount.AndCountCircuit 42, c.WellFormed → c.Computes G → c.outVars = ∅ →
        (∀ (i : Fin c.size) (v : Fin 42), c.gateVal {v} i = false) →
        (∀ i : Fin c.size, Disjoint (c.leftVars i) (c.rightVars i)) → c.size = 19 →
        (∀ v : Fin 42, {i : Fin c.size | v ∈ c.leftVars i ∨ v ∈ c.rightVars i}.ncard ≤ 3) →
        (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬ G.Adj p l →
          {i : Fin c.size | p ∈ c.leftVars i ∨ p ∈ c.rightVars i ∨ l ∈ c.leftVars i ∨ l ∈ c.rightVars i}.ncard ≤ 5) →
        (∃ i j : Fin c.size, i ≠ j ∧ (∃ a ∈ c.leftVars i, ∃ b ∈ c.rightVars i, ¬ G.Adj a b) ∧ (∃ a ∈ c.leftVars j, ∃ b ∈ c.rightVars j, ¬ G.Adj a b)) → False)) : have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (19 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (3 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (5 : ℕ)) → False := by
  classical
  intro G c hW hC hOut hSing hDisj hSize hOcc hPair
  have hG : G = (SimpleGraph.fromRel fun (a b : Fin 42) => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) := rfl
  have hAdj : ∀ a b : Fin 42, G.Adj a b ↔ a ≠ b ∧ (((a).val < 21 ∧ 21 ≤ (b).val ∧ ((b).val + 21 - (a).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨ ((b).val < 21 ∧ 21 ≤ (a).val ∧ ((a).val + 21 - (b).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))) := by
    intro a b
    rw [hG]
    exact SimpleGraph.fromRel_adj _ a b
  by_cases hJ : ∃ i : Fin c.size, ∃ a ∈ c.leftVars i, ∃ b ∈ c.rightVars i, ¬ G.Adj a b
  · obtain ⟨i, hi⟩ := hJ
    by_cases hJ2 : ∃ j : Fin c.size, j ≠ i ∧ ∃ a ∈ c.leftVars j, ∃ b ∈ c.rightVars j, ¬ G.Adj a b
    · obtain ⟨j, hji, hj⟩ := hJ2
      exact h2 c hW hC hOut hSing hDisj hSize hOcc hPair ⟨j, i, hji, hj, hi⟩
    · refine h1 c hW hC hOut hSing hDisj hSize hOcc hPair ⟨i, hi, ?_⟩
      intro j hj
      by_contra hne
      exact hJ2 ⟨j, hne, hj⟩
  · have hclean : ∀ i : Fin c.size, ∀ a ∈ c.leftVars i, ∀ b ∈ c.rightVars i, G.Adj a b := by
      intro i a ha b hb
      by_contra hn
      exact hJ ⟨i, a, ha, b, hb, hn⟩
    have F1 : (Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))).card = 105 := by decide +kernel
    have F2 : ∀ v : Fin 42, ((Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))).filter (fun e => e.1 = v ∨ e.2 = v)).card ≤ 5 := by decide +kernel
    have F3 : ∀ a a' : Fin 42, a ≠ a' → (Finset.univ.filter (fun b : Fin 42 => (((a).val < 21 ∧ 21 ≤ (b).val ∧ ((b).val + 21 - (a).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨ ((b).val < 21 ∧ 21 ≤ (a).val ∧ ((a).val + 21 - (b).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))) ∧ (((a').val < 21 ∧ 21 ≤ (b).val ∧ ((b).val + 21 - (a').val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨ ((b).val < 21 ∧ 21 ≤ (a').val ∧ ((a').val + 21 - (b).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))))).card ≤ 1 := by decide +kernel
    have key : ∀ (U : Finset (Fin 42)) (d : ℕ) (i : Fin c.size), c.gateValFuel U d i = true →
        ∃ k : Fin c.size, ∃ a ∈ c.leftVars k, ∃ b ∈ c.rightVars k, a ∈ U ∧ b ∈ U := by
      intro U d
      induction d with
      | zero =>
        intro i h
        have h0 : c.gateValFuel U 0 i = false := rfl
        rw [h0] at h
        exact absurd h (by simp)
      | succ d ih =>
        intro i h
        have h0 : c.gateValFuel U (d + 1) i =
          (PEqualNP.AndCount.AndCountCircuit.sideTrue U (c.leftVars i) (c.leftGates i) i (c.gateValFuel U d) &&
           PEqualNP.AndCount.AndCountCircuit.sideTrue U (c.rightVars i) (c.rightGates i) i (c.gateValFuel U d)) := rfl
        rw [h0, Bool.and_eq_true] at h
        obtain ⟨hl, hr⟩ := h
        have hside : ∀ (B : Finset (Fin 42)) (F : Finset (Fin c.size)),
            PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i (c.gateValFuel U d) =
              decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ c.gateValFuel U d j = true) := fun _ _ => rfl
        rw [hside, decide_eq_true_eq] at hl hr
        rcases hl with ⟨a, ha, haU⟩ | ⟨j, _, _, hj⟩
        · rcases hr with ⟨b, hb, hbU⟩ | ⟨j, _, _, hj⟩
          · exact ⟨i, a, ha, b, hb, haU, hbU⟩
          · exact ih j hj
        · exact ih j hj
    have cover : ∀ e ∈ (Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))), ∃ k : Fin c.size,
        (e.1 ∈ c.leftVars k ∧ e.2 ∈ c.rightVars k) ∨ (e.2 ∈ c.leftVars k ∧ e.1 ∈ c.rightVars k) := by
      intro e he
      have hr := (Finset.mem_filter.mp he).2
      have hne : e.1 ≠ e.2 := by
        intro h
        have h1' := hr.1
        have h2' := hr.2.1
        rw [h] at h1'
        omega
      have hadj : G.Adj e.1 e.2 := (hAdj e.1 e.2).mpr ⟨hne, Or.inl hr⟩
      have hev : c.eval {e.1, e.2} = true :=
        (hC {e.1, e.2}).mpr ⟨e.1, by simp, e.2, by simp, hadj⟩
      have hevd : c.eval {e.1, e.2} =
          decide ((∃ v ∈ c.outVars, v ∈ ({e.1, e.2} : Finset (Fin 42))) ∨ ∃ j ∈ c.outGates, c.gateVal {e.1, e.2} j = true) := rfl
      rw [hevd, decide_eq_true_eq, hOut] at hev
      rcases hev with ⟨v, hv, _⟩ | ⟨j, _, hj⟩
      · exact absurd hv (by simp)
      · obtain ⟨k, a, ha, b, hb, haU, hbU⟩ := key {e.1, e.2} c.size j hj
        have hab : a ≠ b := by
          intro h
          rw [h] at ha
          exact (Finset.disjoint_left.mp (hDisj k) ha) hb
        refine ⟨k, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at haU hbU
        rcases haU with h | h <;> rcases hbU with h' | h'
        · exact absurd (h.trans h'.symm) hab
        · left
          rw [← h, ← h']
          exact ⟨ha, hb⟩
        · right
          rw [← h, ← h']
          exact ⟨ha, hb⟩
        · exact absurd (h.trans h'.symm) hab
    have sub : ∀ S : Finset (Fin 42), (∀ x ∈ S, ∀ y ∈ S, x = y) →
        ∀ T : Finset (Fin 42 × Fin 42), T ⊆ (Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))) → (∀ e ∈ T, e.1 ∈ S ∨ e.2 ∈ S) → T.card ≤ 5 := by
      intro S hS T hT hTS
      by_cases hb : ∃ b, b ∈ S
      · obtain ⟨b, hb⟩ := hb
        refine le_trans (Finset.card_le_card ?_) (F2 b)
        intro e he
        refine Finset.mem_filter.mpr ⟨hT he, ?_⟩
        rcases hTS e he with h | h
        · exact Or.inl (hS _ h _ hb)
        · exact Or.inr (hS _ h _ hb)
      · have hem : T = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro e he
          rcases hTS e he with h | h
          · exact hb ⟨_, h⟩
          · exact hb ⟨_, h⟩
        rw [hem]
        simp
    have per : ∀ k : Fin c.size, ((Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))).filter (fun e =>
        (e.1 ∈ c.leftVars k ∧ e.2 ∈ c.rightVars k) ∨ (e.2 ∈ c.leftVars k ∧ e.1 ∈ c.rightVars k))).card ≤ 5 := by
      intro k
      by_cases hL : ∃ a ∈ c.leftVars k, ∃ a' ∈ c.leftVars k, a ≠ a'
      · obtain ⟨a, ha, a', ha', hne⟩ := hL
        have hR : ∀ x ∈ c.rightVars k, ∀ y ∈ c.rightVars k, x = y := by
          intro x hx y hy
          have m : ∀ z ∈ c.rightVars k, z ∈ Finset.univ.filter (fun b : Fin 42 => (((a).val < 21 ∧ 21 ≤ (b).val ∧ ((b).val + 21 - (a).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨ ((b).val < 21 ∧ 21 ≤ (a).val ∧ ((a).val + 21 - (b).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))) ∧ (((a').val < 21 ∧ 21 ≤ (b).val ∧ ((b).val + 21 - (a').val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) ∨ ((b).val < 21 ∧ 21 ≤ (a').val ∧ ((a').val + 21 - (b).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))) := by
            intro z hz
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hAdj a z).mp (hclean k a ha z hz)).2, ((hAdj a' z).mp (hclean k a' ha' z hz)).2⟩
          exact Finset.card_le_one.mp (F3 a a' hne) x (m x hx) y (m y hy)
        refine sub (c.rightVars k) hR _ (Finset.filter_subset _ _) ?_
        intro e he
        rcases (Finset.mem_filter.mp he).2 with h | h
        · exact Or.inr h.2
        · exact Or.inl h.2
      · have hL' : ∀ x ∈ c.leftVars k, ∀ y ∈ c.leftVars k, x = y := by
          intro x hx y hy
          by_contra h
          exact hL ⟨x, hx, y, hy, h⟩
        refine sub (c.leftVars k) hL' _ (Finset.filter_subset _ _) ?_
        intro e he
        rcases (Finset.mem_filter.mp he).2 with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
    have hsubset : (Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))) ⊆ (Finset.univ : Finset (Fin c.size)).biUnion (fun k => (Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))).filter (fun e =>
        (e.1 ∈ c.leftVars k ∧ e.2 ∈ c.rightVars k) ∨ (e.2 ∈ c.leftVars k ∧ e.1 ∈ c.rightVars k))) := by
      intro e he
      obtain ⟨k, hk⟩ := cover e he
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨he, hk⟩⟩
    have hcard := Finset.card_le_card hsubset
    have hmul := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin c.size)) (fun k => (Finset.univ.filter (fun e : Fin 42 × Fin 42 => ((e.1).val < 21 ∧ 21 ≤ (e.2).val ∧ ((e.2).val + 21 - (e.1).val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)))).filter (fun e =>
        (e.1 ∈ c.leftVars k ∧ e.2 ∈ c.rightVars k) ∨ (e.2 ∈ c.leftVars k ∧ e.1 ∈ c.rightVars k))) 5 (fun k _ => per k)
    rw [Finset.card_univ, Fintype.card_fin] at hmul
    rw [F1] at hcard
    omega
