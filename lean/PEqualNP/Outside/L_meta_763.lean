import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_763_aux

open PEqualNP.MetaComplexity

private def adj6 (u v : Fin 6) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
  (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨
  (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) ∨
  (u = 4 ∧ v = 5) ∨ (u = 5 ∧ v = 4)

private instance : DecidableRel adj6 := fun u v => by
  unfold adj6; infer_instance

private def G : SimpleGraph (Fin 6) where
  Adj := adj6
  symm := ⟨by intro u v h; fin_cases u <;> fin_cases v <;> simp [adj6] at h ⊢⟩
  loopless := ⟨by intro u h; fin_cases u <;> simp [adj6] at h⟩

private instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adj6)

private lemma cycle_two_neighbors {v w : Fin 6} {c : G.Walk v v} (hc : c.IsCycle)
    (hw : w ∈ c.support) :
    ∃ u1 u2 : Fin 6, G.Adj w u1 ∧ G.Adj w u2 ∧ u1 ≠ u2 ∧
      u1 ∈ c.support ∧ u2 ∈ c.support := by
  classical
  let c' := c.rotate w hw
  have hc' : c'.IsCycle := hc.rotate hw
  have hlen : 3 ≤ c'.length := hc'.three_le_length
  have hmem_rot : ∀ x : Fin 6, x ∈ c'.support → x ∈ c.support := by
    intro x hx
    exact (SimpleGraph.Walk.mem_support_rotate_iff c w hw).1 hx
  cases hc'eq : c' with
  | nil => rw [hc'eq] at hlen; simp at hlen
  | cons h1 p =>
    rename_i u1
    have hp_len : 2 ≤ p.length := by rw [hc'eq] at hlen; simp at hlen; omega
    have hnodup : (s(w, u1) :: p.edges).Nodup := by
      have := hc'.edges_nodup
      rw [hc'eq] at this
      exact this
    cases hrev : p.reverse with
    | nil =>
      have : p.reverse.length = p.length := SimpleGraph.Walk.length_reverse p
      rw [hrev] at this; simp at this; omega
    | cons h2 q =>
      rename_i u2
      have hmem_e : s(w, u2) ∈ p.edges := by
        have h1e : s(w, u2) ∈ p.reverse.edges := by rw [hrev]; simp
        rw [SimpleGraph.Walk.edges_reverse] at h1e
        exact List.mem_reverse.1 h1e
      have hne : u1 ≠ u2 := by
        intro heq
        subst heq
        exact (List.nodup_cons.1 hnodup).1 hmem_e
      have hu1 : u1 ∈ c.support := by
        apply hmem_rot
        rw [hc'eq]
        simp [SimpleGraph.Walk.start_mem_support]
      have hu2 : u2 ∈ c.support := by
        apply hmem_rot
        rw [hc'eq]
        have hu2p : u2 ∈ p.reverse.support := by
          rw [hrev]; simp [SimpleGraph.Walk.start_mem_support]
        rw [SimpleGraph.Walk.support_reverse] at hu2p
        exact List.mem_cons_of_mem w (List.mem_reverse.1 hu2p)
      exact ⟨u1, u2, h1, h2, hne, hu1, hu2⟩

private lemma G_acyclic : G.IsAcyclic := by
  intro v c hc
  have hne : c.support.toFinset.Nonempty := by
    refine ⟨v, List.mem_toFinset.2 (SimpleGraph.Walk.start_mem_support c)⟩
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image c.support.toFinset (fun x : Fin 6 => x.val) hne
  obtain ⟨u1, u2, h1, h2, hne12, hu1, hu2⟩ := cycle_two_neighbors hc (List.mem_toFinset.1 hm_mem)
  have hle1 : u1.val ≤ m.val := hm_max u1 (List.mem_toFinset.2 hu1)
  have hle2 : u2.val ≤ m.val := hm_max u2 (List.mem_toFinset.2 hu2)
  have hne1 : u1 ≠ m := G.ne_of_adj h1.symm
  have hne2 : u2 ≠ m := G.ne_of_adj h2.symm
  have hlt1 : u1.val < m.val := lt_of_le_of_ne hle1 (fun h => hne1 (Fin.ext h))
  have hlt2 : u2.val < m.val := lt_of_le_of_ne hle2 (fun h => hne2 (Fin.ext h))
  have huniq : ∀ a b d : Fin 6, G.Adj a b → G.Adj a d → b.val < a.val → d.val < a.val → b = d := by
    decide
  exact hne12 (huniq m u1 u2 h1 h2 hlt1 hlt2)

private lemma G_has_edge : ∃ i j : Fin 6, G.Adj i j :=
  ⟨0, 1, by decide⟩

private lemma G_edge_card : G.edgeFinset.card = 4 := by
  decide

private lemma G_cover_ge : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  intro T hT
  have h02 : (0 : Fin 6) ∈ T ∨ (2 : Fin 6) ∈ T := hT 0 2 (by decide)
  have h13 : (1 : Fin 6) ∈ T ∨ (3 : Fin 6) ∈ T := hT 1 3 (by decide)
  have h45 : (4 : Fin 6) ∈ T ∨ (5 : Fin 6) ∈ T := hT 4 5 (by decide)
  have hsub : ∀ a b c : Fin 6, a ∈ T → b ∈ T → c ∈ T → a ≠ b → a ≠ c → b ≠ c → 3 ≤ T.card := by
    intro a b c ha hb hc hab hac hbc
    have hle : ({a, b, c} : Finset (Fin 6)).card ≤ T.card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc3 : ({a, b, c} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hbc]
      · simp [hab, hac]
    omega
  rcases h02 with h0 | h2 <;> rcases h13 with h1 | h3 <;> rcases h45 with h4 | h5
  · exact hsub 0 1 4 h0 h1 h4 (by decide) (by decide) (by decide)
  · exact hsub 0 1 5 h0 h1 h5 (by decide) (by decide) (by decide)
  · exact hsub 0 3 4 h0 h3 h4 (by decide) (by decide) (by decide)
  · exact hsub 0 3 5 h0 h3 h5 (by decide) (by decide) (by decide)
  · exact hsub 2 1 4 h2 h1 h4 (by decide) (by decide) (by decide)
  · exact hsub 2 1 5 h2 h1 h5 (by decide) (by decide) (by decide)
  · exact hsub 2 3 4 h2 h3 h4 (by decide) (by decide) (by decide)
  · exact hsub 2 3 5 h2 h3 h5 (by decide) (by decide) (by decide)

private lemma target_eq_graph :
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) =
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    rcases h with ((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h1, h3⟩) | ⟨h4, h5⟩
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨1, 3, by decide, h1, h3⟩
    · exact ⟨4, 5, by decide, h4, h5⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; decide) | (dsimp at hi hj; simp [hi, hj])

theorem main (s : ℕ) :
    HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔
      6 ≤ s := by
  rw [target_eq_graph]
  constructor
  · intro hs
    have hb := PEqualNP.MetaComplexity.L104 6 3 s G G_acyclic G_has_edge G_cover_ge hs
    rw [G_edge_card] at hb
    omega
  · intro hs
    have hup := PEqualNP.MetaComplexity.L105 6 G ({0, 1, 4} : Finset (Fin 6)) G_has_edge (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; decide) | decide)
    rw [G_edge_card] at hup
    have hc : ({0, 1, 4} : Finset (Fin 6)).card = 3 := by decide
    rw [hc] at hup
    obtain ⟨C, hfan, hsize, heval⟩ := hup
    exact ⟨C, hfan, by omega, heval⟩

end PEqualNP.Outside.L_meta_763_aux

theorem PEqualNP.Outside.L_meta_763 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_763_aux.main
