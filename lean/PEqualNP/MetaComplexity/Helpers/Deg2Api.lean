import PEqualNP.MetaComplexity.Helpers.Deg2Defs

/-!
# Basic facts on the degree-two DAG (helper for L-meta-649, package P0)

Proved here: the `api_*` cards of `Deg2Skeleton` that need no foldl bridge, and D2-03a, D2-03b.
-/

namespace PEqualNP.MetaComplexity.Deg2.Api

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg2

variable {N : ℕ}

theorem gateAt_some {D : Dag N} {i : ℕ} {g : G} (h : D.gateAt i = some g) :
    N + N ≤ i ∧ D.gates[i - (N + N)]? = some g := by
  unfold Dag.gateAt at h
  split_ifs at h with hi
  exact ⟨hi, h⟩

/-- One step down does not raise the degree. -/
theorem deg_kid {D : Dag N} {i c : ℕ} (h : D.Kid i c) : D.deg c ≤ D.deg i := by
  obtain ⟨g, hg, hc, hci⟩ := h
  obtain ⟨hi, hg⟩ := gateAt_some hg
  conv_rhs => rw [Dag.deg]
  rw [if_neg (by omega), hg]
  cases g with
  | and a b =>
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · dsimp only; rw [dif_pos hci]; omega
    · dsimp only; rw [dif_pos hci]; omega
  | or a b =>
    simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · dsimp only; rw [dif_pos hci]; exact le_max_left _ _
    · dsimp only; rw [dif_pos hci]; exact le_max_right _ _
  | cst v => simp [G.kids] at hc

/-- Degree does not grow downward. -/
theorem api_reach_deg (D : Dag N) {i j : ℕ} (h : D.Reach i j) : D.deg j ≤ D.deg i := by
  induction h with
  | refl => exact le_rfl
  | tail _ hk ih => exact le_trans (deg_kid hk) ih

/-- A cone is closed downward over gate wires. -/
theorem api_coneOf_down (D : Dag N) (S : Finset ℕ) :
    ∀ i ∈ D.coneOf S, ∀ c, D.Kid i c → N + N ≤ c → c ∈ D.coneOf S := by
  intro i hi c hk hc
  classical
  unfold Dag.coneOf at hi ⊢
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  obtain ⟨hlt, -, r, hr, hreach⟩ := hi
  obtain ⟨_, _, _, hci⟩ := id hk
  refine ⟨by omega, hc, r, hr, ?_⟩
  exact Relation.ReflTransGen.tail hreach hk

theorem coneOf_sub (D : Dag N) (S : Finset ℕ) :
    D.coneOf S ⊆ Finset.Ico (N + N) (N + N + D.size) := by
  intro i hi
  classical
  unfold Dag.coneOf at hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  simp only [Finset.mem_Ico]
  omega

theorem coneOf_card (D : Dag N) (S : Finset ℕ) : (D.coneOf S).card ≤ D.size := by
  have := Finset.card_le_card (coneOf_sub D S)
  simpa using this

theorem card_filter_disj {s : Finset ℕ} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ i, p i → ¬ q i) :
    (s.filter p).card + (s.filter q).card ≤ (s.filter (fun i => p i ∨ q i)).card := by
  have hu := Finset.card_union_add_card_inter (s.filter p) (s.filter q)
  have hi : s.filter p ∩ s.filter q = ∅ := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨⟨_, hp⟩, ⟨_, hq⟩⟩
    exact h i hp hq
  have hsub : s.filter p ∪ s.filter q ⊆ s.filter (fun i => p i ∨ q i) := by
    intro i
    simp only [Finset.mem_union, Finset.mem_filter]
    rintro (⟨hs, hp⟩ | ⟨hs, hq⟩)
    · exact ⟨hs, Or.inl hp⟩
    · exact ⟨hs, Or.inr hq⟩
  rw [hi, Finset.card_empty] at hu
  have := Finset.card_le_card hsub
  omega

/-- The classes are disjoint sets of gates. -/
theorem api_classes_card (D : Dag N) : D.X.card + D.M.card + D.T.card ≤ D.size := by
  have h1 := card_filter_disj (s := D.cone) (p := fun i => D.deg i = 0)
    (q := fun i => D.deg i = 1) (by intro i h1 h2; omega)
  have h2 := card_filter_disj (s := D.cone) (p := fun i => D.deg i = 0 ∨ D.deg i = 1)
    (q := fun i => D.deg i = 2) (by intro i h1 h2; omega)
  have h3 := Finset.card_filter_le D.cone (fun i => (D.deg i = 0 ∨ D.deg i = 1) ∨ D.deg i = 2)
  have h4 := coneOf_card D {D.out}
  unfold Dag.X Dag.M Dag.T
  unfold Dag.cone at *
  omega

/-- AND and OR gates of M are disjoint. -/
theorem api_andor_card (D : Dag N) : D.AndM.card + D.OrM.card ≤ D.M.card := by
  classical
  have h := card_filter_disj (s := D.M) (p := D.IsAnd) (q := D.IsOr) (by
    rintro i ⟨a, b, ha⟩ ⟨a', b', hb⟩
    rw [ha] at hb
    cases hb)
  have h' := Finset.card_filter_le D.M (fun i => D.IsAnd i ∨ D.IsOr i)
  unfold Dag.AndM Dag.OrM
  convert le_trans h h' using 2


theorem band_mono : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c && d) := by decide
theorem bor_mono : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by decide

/-- Every wire is monotone in the input. -/
theorem api_val_mono (D : Dag N) (i : ℕ) {x y : Fin (N + N) → Bool} (h : x ≤ y) :
    D.val x i ≤ D.val y i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hd : ∀ a, (if _ : a < i then D.val x a else false) ≤
        (if _ : a < i then D.val y a else false) := by
      intro a
      split_ifs with ha
      · exact ih a ha
      · exact le_rfl
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    split_ifs with hi
    · exact h _
    · cases hg : D.gates[i - (N + N)]? with
      | none => exact le_rfl
      | some g =>
        cases g with
        | and a b => exact band_mono _ _ _ _ (hd a) (hd b)
        | or a b => exact bor_mono _ _ _ _ (hd a) (hd b)
        | cst v => exact le_rfl

/-- A wire of degree 0 reads the points only. -/
theorem api_val_xonly (D : Dag N) {i : ℕ} (hd : D.deg i = 0) {x y : Fin (N + N) → Bool}
    (h : ∀ p : Fin N, x (Fin.castAdd N p) = y (Fin.castAdd N p)) : D.val x i = D.val y i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have he : ∀ a, (if _ : a < i then D.deg a else 0) = 0 →
        (if _ : a < i then D.val x a else false) = (if _ : a < i then D.val y a else false) := by
      intro a ha
      split_ifs at ha ⊢ with hai
      · exact ih a hai ha
      · rfl
    rw [Dag.deg] at hd
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    by_cases hi : i < N + N
    · rw [dif_pos hi, dif_pos hi]
      rw [if_pos hi] at hd
      have hN : ¬ N ≤ i := by intro hN; rw [if_pos hN] at hd; exact absurd hd one_ne_zero
      have := h ⟨i, by omega⟩
      simpa [Fin.castAdd] using this
    · rw [dif_neg hi, dif_neg hi]
      rw [if_neg hi] at hd
      cases hg : D.gates[i - (N + N)]? with
      | none => rfl
        | some g =>
          rw [hg] at hd
          cases g with
          | and a b =>
            dsimp only at hd ⊢
            rw [he a (by omega), he b (by omega)]
          | or a b =>
            dsimp only at hd ⊢
            rw [he a (by omega), he b (by omega)]
          | cst v => rfl

/-- D2-03a. -/
theorem card03a_size (C : Circuit) : (ofCircuit N C).size = C.size := by
  simp [Dag.size, ofCircuit, Circuit.size]

theorem trGate_kids (i : ℕ) (g : Gate) : ∀ c ∈ (trGate i g).kids, c < i := by
  intro c hc
  unfold trGate at hc
  split at hc <;> (try split_ifs at hc) <;> simp_all [G.kids] <;> omega

/-- D2-03b. -/
theorem card03b_wf (C : Circuit) : (ofCircuit N C).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg⟩ := gateAt_some hg
  simp only [ofCircuit, List.getElem?_mapIdx] at hg
  cases h : C.gates[i - (N + N)]? with
  | none => rw [h] at hg; cases hg
  | some g0 =>
    rw [h] at hg
    simp only [Option.map_some, Option.some.injEq] at hg
    subst hg
    have := trGate_kids _ g0 c hc
    omega

/-- D2-03r (class). The converse translation is monotone of fan-in two. -/
theorem card03r_mono (D : Dag N) : Monotone2 D.toCircuit := by
  intro g hg
  simp only [Dag.toCircuit, List.mem_map] at hg
  obtain ⟨g0, -, rfl⟩ := hg
  cases g0 with
  | and a b => simp [G.toGate]
  | or a b => simp [G.toGate]
  | cst v => cases v <;> simp [G.toGate]

theorem labAnd_unique {D : Dag N} {g f v f' v' : ℕ} (h : D.LabAnd g f v) (h' : D.LabAnd g f' v') :
    f = f' ∧ v = v' := by
  obtain ⟨hg, hf, hv⟩ := h
  obtain ⟨hg', hf', hv'⟩ := h'
  rcases hg with hg | hg <;> rcases hg' with hg' | hg' <;> rw [hg] at hg' <;>
    simp only [Option.some.injEq, G.and.injEq] at hg' <;> obtain ⟨rfl, rfl⟩ := hg'
  · exact ⟨rfl, rfl⟩
  · omega
  · omega
  · exact ⟨rfl, rfl⟩

/-- D2-17 (count of Served). -/
theorem card17s_served (I : Fin N → Fin N → Prop) (D : Dag N) :
    (D.served I).card ≤ 2 * D.AndM.card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g => Finset.univ.filter (fun e => ∃ f v,
    D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧ e.1 ∈ D.alive f ∧ I e.1 e.2 ∧
      (D.alive f ∩ ptsOn I e.2).card ≤ 2)
  have hsub : D.served I ⊆ D.AndM.biUnion T := by
    intro e he
    unfold Dag.served at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, g, hg, f, v, h1, h2, h3, h4, h5⟩ := he
    rw [Finset.mem_biUnion]
    exact ⟨g, hg, Finset.mem_filter.2 ⟨Finset.mem_univ _, f, v, h1, h2, h3, h4, h5⟩⟩
  have hT : ∀ g ∈ D.AndM, (T g).card ≤ 2 := by
    intro g _
    by_cases hne : (T g).Nonempty
    · obtain ⟨e0, he0⟩ := hne
      obtain ⟨-, f0, v0, h1, h2, -, -, h5⟩ := Finset.mem_filter.1 he0
      have hsub' : T g ⊆ (D.alive f0 ∩ ptsOn I e0.2).image (fun p => (p, e0.2)) := by
        intro e he
        obtain ⟨-, f, v, k1, k2, k3, k4, -⟩ := Finset.mem_filter.1 he
        obtain ⟨rfl, rfl⟩ := labAnd_unique k1 h1
        have hw : e.2 = e0.2 := by
          rw [h2] at k2
          exact (Finset.singleton_inj.1 k2).symm
        rw [Finset.mem_image]
        refine ⟨e.1, Finset.mem_inter.2 ⟨k3, ?_⟩, ?_⟩
        · unfold ptsOn
          rw [Finset.mem_filter, ← hw]
          exact ⟨Finset.mem_univ _, k4⟩
        · ext <;> simp [hw]
      exact le_trans (Finset.card_le_card hsub') (le_trans Finset.card_image_le h5)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  calc (D.served I).card ≤ (D.AndM.biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ g ∈ D.AndM, (T g).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ D.AndM, 2 := Finset.sum_le_sum hT
    _ = 2 * D.AndM.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end PEqualNP.MetaComplexity.Deg2.Api
