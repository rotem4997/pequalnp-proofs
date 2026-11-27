import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1770_401
    (bottomDeep : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∃ E : Finset (Sym2 (Fin n)), E.card ≤ k * (C.size + 1) ∧
        ∀ e ∈ Ustar G C,
          (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ g ∈ junk G C,
            u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧ gateVal n C g (pairInput u v) = true) →
          (∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2),
            ∃ g ∈ junk G C, ∃ h ∈ junk G C,
            g ≠ h ∧ OrReaches n C (opnd C a b) g ∧ OrReaches n C (opnd C a (1 - b)) h ∧
            gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
            (∀ j ∈ junk G C, ¬InCone n C j g) ∧ (∃ j ∈ junk G C, InCone n C j h)) →
          e ∈ E)
    (deepDeep : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∃ E : Finset (Sym2 (Fin n)), E.card ≤ k * (C.size + 1) ∧
        ∀ e ∈ Ustar G C,
          (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ g ∈ junk G C,
            u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧ gateVal n C g (pairInput u v) = true) →
          (∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C,
            ∃ g ∈ junk G C, ∃ h ∈ junk G C,
            g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
            gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
            (∃ j ∈ junk G C, InCone n C j g) ∧ (∃ j ∈ junk G C, InCone n C j h)) →
          e ∈ E) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | (¬∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  have bottomBottom : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∃ EBB : Finset (Sym2 (Fin n)), EBB.card ≤ 204 * C.size ∧
        ∀ e ∈ Ustar G C,
          (∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C,
            ∃ g ∈ junk G C, ∃ h ∈ junk G C,
            g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
            gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
            (∀ j ∈ junk G C, ¬InCone n C j g) ∧ (∀ j ∈ junk G C, ¬InCone n C j h)) →
          e ∈ EBB := by
    intro n G _ C hG5 hL hT
    obtain ⟨⟨hAO, hRB, h2⟩, _, _⟩ := hL
    have hNo4 : NoFourCycle G := by
      intro a b hab
      by_contra hc
      rw [not_le] at hc
      obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hc
      rw [Finset.mem_filter] at hw1 hw2
      obtain ⟨-, ha1, hb1⟩ := hw1
      obtain ⟨-, ha2, hb2⟩ := hw2
      have e1 := G.ne_of_adj ha1
      have e2 := G.ne_of_adj hb1
      have e3 := G.ne_of_adj ha2
      have e4 := G.ne_of_adj hb2
      have hcyc : (SimpleGraph.Walk.cons ha1 (SimpleGraph.Walk.cons hb1.symm
          (SimpleGraph.Walk.cons hb2 (SimpleGraph.Walk.cons ha2.symm SimpleGraph.Walk.nil)))).IsCycle := by
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        refine ⟨?_, ?_⟩
        · simp [SimpleGraph.Walk.cons_isPath_iff, e4, hne, Ne.symm e1, Ne.symm e2,
            Ne.symm e3, Ne.symm hab]
        · simp [e1, e3, hab, hne, Ne.symm e1, Ne.symm e2]
      have h5 := hG5 a _ hcyc
      simp at h5
    let N : Fin n → Finset (Fin n) := fun u => Finset.univ.filter (fun v => G.Adj u v)
    have hMemN : ∀ u v : Fin n, v ∈ N u ↔ G.Adj u v := fun u v => by simp [N]
    have hInterN : ∀ a b : Fin n, a ≠ b → (N a ∩ N b).card ≤ 1 := by
      intro a b hab
      have heq : N a ∩ N b = Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
        ext w; simp [N]
      rw [heq]; exact hNo4 a b hab
    have hBiclique : ∀ (P Q : Finset (Fin n)), (∀ a ∈ P, ∀ b ∈ Q, G.Adj a b) → P.card ≤ 1 ∨ Q.card ≤ 1 := by
      intro P Q hab
      by_contra hcon
      simp only [not_or, not_le] at hcon
      obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
      obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
      have hsub : ({b, d} : Finset (Fin n)) ⊆ N a ∩ N c := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [Finset.mem_inter, hMemN, hMemN]
        rcases hw with rfl | rfl
        · exact ⟨hab a ha w hb, hab c hc w hb⟩
        · exact ⟨hab a ha w hd, hab c hc w hd⟩
      have hle := (Finset.card_le_card hsub).trans (hInterN a c hac)
      rw [Finset.card_pair hbd] at hle
      omega
    have hUniqueCenter : ∀ (S : Finset (Fin n)) (r : ℕ), 2 * r + 2 ≤ S.card →
        ∀ c1 c2 : Fin n, (S \ N c1).card ≤ r → (S \ N c2).card ≤ r → c1 = c2 := by
      intro S r hS c1 c2 h1 h2'
      by_contra hne
      have hsub : S ⊆ (S \ N c1) ∪ (S \ N c2) ∪ (N c1 ∩ N c2) := by
        intro w hw
        by_cases hc1 : w ∈ N c1
        · by_cases hc2 : w ∈ N c2
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hc1, hc2⟩)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hw, hc2⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw, hc1⟩))
      have hle := (Finset.card_le_card hsub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hi := hInterN c1 c2 hne
      omega
    have hSizeEq : C.size = C.gates.length := rfl
    have hgateAt_def : ∀ j : ℕ, gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ => rfl
    have hopnd_def : ∀ (k : ℕ) (b : Fin 2), opnd C k b = (gateAt C k).inputs.getD b 0 := fun _ _ => rfl
    letI : DecidableEq GateOp := gateOpDecEq
    have horStep_def : ∀ (cs : List (List ℕ)) (g : Gate), orStep n cs g =
        cs ++ [cs.length :: (if g.op = GateOp.or then
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => cs.getD (w - n) [])
          else [])] := fun _ _ => rfl
    have hconeStep_def : ∀ (cs : List (List ℕ)) (g : Gate), coneStep n cs g =
        cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) [])] := fun _ _ => rfl
    have hmem_filt : ∀ {α : Type} {s : Finset α} {p : α → Prop} {inst : DecidablePred p} {a : α},
        a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := by
      intro α s p inst a; exact @Finset.mem_filter α p inst s a
    have horIn_mem : ∀ (w : ℕ) (u : Fin n), u ∈ orIn n C w ↔
        (u : ℕ) = w ∨ ∃ k < C.gates.length,
          OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (u : ℕ) ∈ (gateAt C k).inputs := by
      intro w u
      change u ∈ @Finset.filter (Fin n) _ _ Finset.univ ↔ _
      rw [hmem_filt, and_iff_right (Finset.mem_univ _)]
    have hside_def : ∀ (a : ℕ) (b : Fin 2), side (n := n) C a b = orIn n C (opnd C a b) := fun _ _ => rfl
    have hgraphFun_def : ∀ x : Fin n → Bool, graphFun G ∅ x =
        (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
          decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
    have hpair_def : ∀ (u v w : Fin n), pairInput u v w = decide (w = u ∨ w = v) := fun _ _ _ => rfl
    have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
    have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
    obtain ⟨Tops, hTopsEq⟩ : ∃ S : Finset ℕ, S = tops G C := ⟨tops G C, rfl⟩
    obtain ⟨Junk, hJunkEq⟩ : ∃ S : Finset ℕ, S = junk G C := ⟨junk G C, rfl⟩
    have htops_mem : ∀ a : ℕ, a ∈ Tops ↔ a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
      intro a; rw [hTopsEq]
      change a ∈ @Finset.filter ℕ _ _ (Finset.range C.gates.length) ↔ _
      rw [hmem_filt, Finset.mem_range]
    have hjunk_mem : ∀ g : ℕ, g ∈ Junk ↔ g < C.gates.length ∧ IsDirtyAnd n G C g := by
      intro g; rw [hJunkEq]
      change g ∈ @Finset.filter ℕ _ _ (Finset.range C.gates.length) ↔ _
      rw [hmem_filt, Finset.mem_range]
    have gateAt_mem : ∀ {j : ℕ}, j < C.gates.length → gateAt C j ∈ C.gates := by
      intro j hj
      have heq : gateAt C j = C.gates[j]'hj := by rw [hgateAt_def]; simp [List.getD_eq_getElem?_getD, hj]
      rw [heq]; exact List.getElem_mem hj
    have opnd_pair : ∀ {k : ℕ}, k < C.gates.length → (gateAt C k).inputs = [opnd C k 0, opnd C k 1] := by
      intro k hk
      obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
      rw [hopnd_def, hopnd_def, hpq]; rfl
    have opnd_mem : ∀ {k : ℕ}, k < C.gates.length → ∀ b : Fin 2, opnd C k b ∈ (gateAt C k).inputs := by
      intro k hk b; rw [opnd_pair hk]; fin_cases b <;> simp
    have opnd_lt : ∀ {k : ℕ}, k < C.gates.length → ∀ b : Fin 2, opnd C k b < n + k :=
      fun hk b => hRB _ hk _ (opnd_mem hk b)
    have hORCore :
        (∀ (k g : ℕ), OrReaches n C (n + k) g ↔
          k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
            ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g))) ∧
        (∀ (i j : ℕ), InCone n C i j ↔
          j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone n C i k)) := by
      constructor
      · have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
            (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
          intro gs; induction gs with
          | nil => intro cs; simp
          | cons g gs ih => intro cs; rw [List.foldl_cons, ih, horStep_def]; simp; omega
        have orSets_char : ∀ (gs : List Gate) (i j : ℕ),
            i ∈ (gs.foldl (orStep n) []).getD j [] ↔
              j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
                ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
                  i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil => intro i j; simp
          | append_singleton gs g ih =>
            intro i j
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hlen : (gs.foldl (orStep n) []).length = gs.length := by rw [orSets_len]; simp
            have key : ∀ k, k < gs.length →
                (orStep n (gs.foldl (orStep n) []) g).getD k [] =
                  (gs.foldl (orStep n) []).getD k [] := by
              intro k hk
              rw [horStep_def]; simp only [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left (by omega)]
            rcases Nat.lt_trichotomy j gs.length with h | h | h
            · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
                simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]
              rw [key j h, ih i j, e1]
              constructor
              · rintro ⟨_, h3⟩
                refine ⟨by simp; omega, ?_⟩
                rcases h3 with h3 | ⟨hop, w, hw, h1, h2', h3⟩
                · exact Or.inl h3
                · refine Or.inr ⟨hop, w, hw, h1, h2', ?_⟩
                  rw [key (w - n) (by omega)]; exact h3
              · rintro ⟨_, h3⟩
                refine ⟨h, ?_⟩
                rcases h3 with h3 | ⟨hop, w, hw, h1, h2', h3⟩
                · exact Or.inl h3
                · rw [key (w - n) (by omega)] at h3; exact Or.inr ⟨hop, w, hw, h1, h2', h3⟩
            · subst h
              have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
                simp [List.getD_eq_getElem?_getD]
              rw [e1]
              by_cases hop : g.op = GateOp.or
              · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
                    gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                      (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
                  rw [horStep_def]; simp only [List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (by omega)]
                  simp [hlen, hop]
                rw [e2]
                simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
                constructor
                · rintro (h3 | ⟨w, ⟨hw, h1, h2'⟩, h3⟩)
                  · exact ⟨by simp, Or.inl h3⟩
                  · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2', ?_⟩⟩
                    rw [key (w - n) (by omega)]; exact h3
                · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2', h3⟩⟩
                  · exact Or.inl h3
                  · rw [key (w - n) (by omega)] at h3; exact Or.inr ⟨w, ⟨hw, h1, h2'⟩, h3⟩
              · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
                  rw [horStep_def]; simp only [List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (by omega)]
                  simp [hlen, hop]
                rw [e2]
                simp only [List.mem_singleton]
                constructor
                · intro h3; exact ⟨by simp, Or.inl h3⟩
                · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
                  · exact h3
                  · exact (hop hop2).elim
            · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
                rw [horStep_def]; simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_none (by simp; omega)]; rfl
              rw [e0]
              constructor
              · intro h0; simp at h0
              · rintro ⟨h0, _⟩; simp at h0; omega
        intro k g
        have h := orSets_char C.gates g k
        unfold OrReaches orSets
        rw [hgateAt_def, show n + k - n = k by omega, h]
        constructor
        · rintro ⟨_, hk, h3⟩
          refine ⟨hk, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2', h3⟩
          · exact Or.inl h3
          · exact Or.inr ⟨hop, w, hw, h2', h1, h3⟩
        · rintro ⟨hk, h3⟩
          refine ⟨by omega, hk, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h2', h1, h3⟩
          · exact Or.inl h3
          · exact Or.inr ⟨hop, w, hw, h1, h2', h3⟩
      · have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
            (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
          intro gs; induction gs with
          | nil => intro cs; simp
          | cons g gs ih => intro cs; rw [List.foldl_cons, ih, hconeStep_def]; simp; omega
        have cones_char : ∀ (gs : List Gate) (i j : ℕ),
            i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
              j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
                (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil => intro i j; simp
          | append_singleton gs g ih =>
            intro i j
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hlen : (gs.foldl (coneStep n) []).length = gs.length := by rw [cones_len]; simp
            have key : ∀ k, k < gs.length →
                (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
                  (gs.foldl (coneStep n) []).getD k [] := by
              intro k hk
              rw [hconeStep_def]; simp only [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left (by omega)]
            rcases Nat.lt_trichotomy j gs.length with h | h | h
            · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
                simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]
              rw [key j h, ih i j, e1]
              constructor
              · rintro ⟨_, w, hw, h1, h2', h3⟩
                refine ⟨by simp; omega, w, hw, h1, h2', ?_⟩
                rw [key (w - n) (by omega)]; exact h3
              · rintro ⟨_, w, hw, h1, h2', h3⟩
                refine ⟨h, w, hw, h1, h2', ?_⟩
                rw [key (w - n) (by omega)] at h3; exact h3
            · subst h
              have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
                simp [List.getD_eq_getElem?_getD]
              have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
                  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
                    (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
                rw [hconeStep_def]; simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (by omega)]
                simp [hlen]
              rw [e2, e1]
              simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
              constructor
              · rintro ⟨w, ⟨hw, h1, h2'⟩, h3⟩
                refine ⟨by simp, w, hw, h1, h2', ?_⟩
                rw [key (w - n) (by omega)]; exact h3
              · rintro ⟨_, w, hw, h1, h2', h3⟩
                rw [key (w - n) (by omega)] at h3
                exact ⟨w, ⟨hw, h1, h2'⟩, h3⟩
            · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
                rw [hconeStep_def]; simp only [List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_none (by simp; omega)]; rfl
              rw [e0]
              constructor
              · intro h0; simp at h0
              · rintro ⟨h0, _⟩; simp at h0; omega
        intro i j
        have h := cones_char C.gates i j
        unfold InCone cones
        rw [hgateAt_def, h]
        constructor
        · rintro ⟨h0, w, hw, h1, h2', h3⟩
          refine ⟨h0, w - n, by omega, ?_, h3⟩
          rw [show n + (w - n) = w by omega]; exact hw
        · rintro ⟨h0, k, hk, hw, h3⟩
          refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
          rw [show n + k - n = k by omega]; exact h3
    obtain ⟨orReaches_iff, inCone_iff⟩ := hORCore
    have orReaches_bounds : ∀ (w g : ℕ), OrReaches n C w g →
        n ≤ w ∧ w < n + C.gates.length ∧ g < C.gates.length ∧ n + g ≤ w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro g hr
        have hnw : n ≤ w := hr.1
        obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp hr
        rcases h3 with rfl | ⟨_, i, _, hlt, hri⟩
        · exact ⟨by omega, by omega, hk, by omega⟩
        · have hb := ih i hlt g hri
          exact ⟨by omega, by omega, hb.2.2.1, by omega⟩
    have orReaches_refl : ∀ {k : ℕ}, k < C.gates.length → OrReaches n C (n + k) k :=
      fun hk => (orReaches_iff _ _).mpr ⟨hk, Or.inl rfl⟩
    have orReaches_trans : ∀ (w k g : ℕ), OrReaches n C w k → OrReaches n C (n + k) g → OrReaches n C w g := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro k g h1 h2'
        have hnw : n ≤ w := h1.1
        obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        obtain ⟨hj, h3⟩ := (orReaches_iff j k).mp h1
        rcases h3 with rfl | ⟨hop, i, hi, hlt, hri⟩
        · exact h2'
        · exact (orReaches_iff j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, ih i hlt k g hri h2'⟩⟩
    have orIn_mono : ∀ {w k : ℕ}, OrReaches n C w k → orIn n C (n + k) ⊆ orIn n C w := by
      intro w k hr u hu
      rw [horIn_mem] at hu ⊢
      rcases hu with h | ⟨j, hj, hrj, hop, hin⟩
      · omega
      · exact Or.inr ⟨j, hj, orReaches_trans w k j hr hrj, hop, hin⟩
    have orIn_gate : ∀ (k : ℕ) (u : Fin n),
        u ∈ orIn n C (n + k) ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
          ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ u ∈ orIn n C i := by
      intro k u
      rw [horIn_mem]
      constructor
      · rintro (h | ⟨j, hj, hr, hop, hin⟩)
        · omega
        · obtain ⟨hk, h3⟩ := (orReaches_iff k j).mp hr
          rcases h3 with rfl | ⟨hopk, i, hi, hlt, hri⟩
          · exact ⟨hk, hop, u.val, hin, by omega, by rw [horIn_mem]; exact Or.inl rfl⟩
          · exact ⟨hk, hopk, i, hi, hlt, by rw [horIn_mem]; exact Or.inr ⟨j, hj, hri, hop, hin⟩⟩
      · rintro ⟨hk, hopk, i, hi, hlt, hu⟩
        rw [horIn_mem] at hu
        rcases hu with h | ⟨j, hj, hri, hop, hin⟩
        · exact Or.inr ⟨k, hk, orReaches_refl hk, hopk, by rw [h]; exact hi⟩
        · exact Or.inr ⟨j, hj, (orReaches_iff k j).mpr ⟨hk, Or.inr ⟨hopk, i, hi, hlt, hri⟩⟩, hop, hin⟩
    have orIn_input : ∀ {w : ℕ}, w < n → ∀ u : Fin n, u ∈ orIn n C w ↔ u.val = w := by
      intro w hw u
      rw [horIn_mem]
      constructor
      · rintro (h | ⟨k, _, hr, _⟩)
        · exact h
        · have := hr.1; omega
      · intro h; exact Or.inl h
    classical
    let IsBottom : ℕ → Prop := fun g => g ∈ Junk ∧ ∀ j ∈ Junk, ¬InCone n C j g
    have hBottomEval :
        (∀ {g : ℕ}, IsBottom g → ∀ x : Fin n → Bool,
          gateVal n C g x = true ↔ (∃ u ∈ side C g 0, x u = true) ∧ (∃ v ∈ side C g 1, x v = true)) ∧
        (∀ {a : ℕ} (b : Fin 2) {g h : ℕ},
          a ∈ Tops → IsBottom g → IsBottom h →
          OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
          ∀ x : Fin n → Bool,
            (∃ a1 ∈ side C g 0, x a1 = true) → (∃ b1 ∈ side C g 1, x b1 = true) →
            (∃ a2 ∈ side C h 0, x a2 = true) → (∃ b2 ∈ side C h 1, x b2 = true) →
            ∃ p q : Fin n, G.Adj p q ∧ x p = true ∧ x q = true) := by
      let stepW : List Bool → Gate → List Bool := fun w g =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have foldl_len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stepW w).length = w.length + gs.length := by
        intro gs; induction gs with
        | nil => intro w; simp
        | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [stepW]; omega
      have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
          (gs.foldl stepW w).getD i false = w.getD i false := by
        intro gs; induction gs with
        | nil => intro w i _; rfl
        | cons g gs ih =>
          intro w i hi
          simp only [List.foldl_cons]
          have hlt : i < (stepW w g).length := by simp [stepW]; omega
          rw [ih (stepW w g) i hlt]
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
          (gs.foldl stepW w).getD (w.length + j) false =
            (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i =>
              if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
        intro gs; induction gs with
        | nil => intro w j hj; simp at hj
        | cons g gs ih =>
          intro w j hj
          rw [List.foldl_cons]
          cases j with
          | zero =>
            have h1 : w.length < (stepW w g).length := by simp [stepW]
            rw [Nat.add_zero, foldl_getD_lt gs (stepW w g) w.length h1]
            simp only [List.getElem_cons_zero]
            have h2 : (stepW w g).getD w.length false =
                g.op.eval (g.inputs.map fun i => w.getD i false) := by
              simp [stepW, List.getD_eq_getElem?_getD]
            rw [h2]; congr 1
            apply List.map_congr_left; intro i _
            by_cases hi : i < w.length
            · rw [if_pos hi, foldl_getD_lt gs (stepW w g) i (by simp [stepW]; omega)]
              simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
            · have hge : w.length ≤ i := by omega
              rw [if_neg hi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
          | succ j =>
            have hj' : j < gs.length := by simpa using hj
            have key := ih (stepW w g) j hj'
            have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
            rw [hl] at key
            have e : w.length + (j + 1) = w.length + 1 + j := by omega
            simp only [List.getElem_cons_succ]; rw [e]; exact key
      have wireVal_input : ∀ (x : Fin n → Bool) (u : Fin n), wireVal n C u.val x = x u := by
        intro x u
        show (C.gates.foldl stepW (List.ofFn x)).getD u.val false = x u
        rw [foldl_getD_lt C.gates (List.ofFn x) u.val (by simp)]
        simp [List.getD_eq_getElem?_getD]
      have wireVal_ge : ∀ (x : Fin n → Bool) {w : ℕ}, n + C.gates.length ≤ w → wireVal n C w x = false := by
        intro x w hw
        show (C.gates.foldl stepW (List.ofFn x)).getD w false = false
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by rw [foldl_len, List.length_ofFn]; omega)]; rfl
      have wireVal_gate : ∀ (x : Fin n → Bool) {j : ℕ}, j < C.gates.length →
          wireVal n C (n + j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
            if i < n + j then wireVal n C i x else false) := by
        intro x j hj
        have h := foldl_getD_gate C.gates (List.ofFn x) j hj
        rw [List.length_ofFn] at h
        have heq : gateAt C j = C.gates[j]'hj := by rw [hgateAt_def]; simp [List.getD_eq_getElem?_getD, hj]
        rw [heq]; exact h
      have wireVal_or : ∀ (x : Fin n → Bool) {r : ℕ}, r < C.gates.length →
          (gateAt C r).op = GateOp.or →
          (wireVal n C (n + r) x = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ wireVal n C i x = true) := by
        intro x r hr hop
        rw [wireVal_gate x hr, hop, eval_or]
        simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
        constructor
        · rintro ⟨i, hi, h⟩
          by_cases hlt : i < n + r
          · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
          · rw [if_neg hlt] at h; cases h
        · rintro ⟨i, hi, hlt, h⟩; exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
      have wireVal_and : ∀ (x : Fin n → Bool) {r : ℕ}, r < C.gates.length →
          (gateAt C r).op = GateOp.and →
          (wireVal n C (n + r) x = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ wireVal n C i x = true) := by
        intro x r hr hop
        rw [wireVal_gate x hr, hop, eval_and]
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
        constructor
        · intro h i hi
          have h' := h i hi
          by_cases hlt : i < n + r
          · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
          · rw [if_neg hlt] at h'; cases h'
        · intro h i hi; rw [if_pos (h i hi).1]; exact (h i hi).2
      have orReaches_up : ∀ (w g : ℕ) (x : Fin n → Bool),
          OrReaches n C w g → gateVal n C g x = true → wireVal n C w x = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro g x hr hg
          have hnw : n ≤ w := hr.1
          obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp hr
          rcases h3 with rfl | ⟨hop, i, hi, hlt, hri⟩
          · exact hg
          · exact (wireVal_or x hk hop).mpr ⟨i, hi, hlt, ih i hlt g x hri hg⟩
      have orIn_up : ∀ (w : ℕ) (u : Fin n) (x : Fin n → Bool),
          u ∈ orIn n C w → x u = true → wireVal n C w x = true := by
        intro w u x hu hxu
        rw [horIn_mem] at hu
        rcases hu with h | ⟨k, hk, hr, hop, hin⟩
        · rw [← h, wireVal_input x u]; exact hxu
        · refine orReaches_up w k x hr ?_
          show wireVal n C (n + k) x = true
          rw [wireVal_or x hk hop]
          exact ⟨u.val, hin, by omega, by rw [wireVal_input]; exact hxu⟩
      have orReaches_inCone : ∀ (w g : ℕ), OrReaches n C w g →
          ∀ k, w = n + k → g = k ∨ InCone n C g k := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro g hr k hw; subst hw
          obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp hr
          rcases h3 with rfl | ⟨_, i, hi, hlt, hri⟩
          · exact Or.inl rfl
          · have hb := orReaches_bounds i g hri
            obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
            exact Or.inr ((inCone_iff g k).mpr ⟨hk, j, by omega, hi, ih (n + j) hlt g hri j rfl⟩)
      have wire_trace : ∀ (w : ℕ) (x : Fin n → Bool), wireVal n C w x = true →
          (∃ u ∈ orIn n C w, x u = true) ∨
          (∃ h < C.gates.length, (gateAt C h).op = GateOp.and ∧ OrReaches n C w h ∧ gateVal n C h x = true) := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro x hwx
          by_cases hlt : w < n
          · left
            refine ⟨⟨w, hlt⟩, (orIn_input hlt _).mpr rfl, ?_⟩
            have := wireVal_input x ⟨w, hlt⟩; rw [← this]; exact hwx
          · by_cases hlen : n + C.gates.length ≤ w
            · rw [wireVal_ge x hlen] at hwx; cases hwx
            · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
              have hk : k < C.gates.length := by omega
              rcases hAO _ (gateAt_mem hk) with hop | hop
              · right; exact ⟨k, hk, hop, orReaches_refl hk, hwx⟩
              · obtain ⟨i, hi, hilt, hix⟩ := (wireVal_or x hk hop).mp hwx
                rcases ih i hilt x hix with ⟨u, hu, hxu⟩ | ⟨h, hh, hhand, hrh, hvh⟩
                · left; exact ⟨u, (orIn_gate k u).mpr ⟨hk, hop, i, hi, hilt, hu⟩, hxu⟩
                · right; exact ⟨h, hh, hhand, (orReaches_iff k h).mpr ⟨hk, Or.inr ⟨hop, i, hi, hilt, hrh⟩⟩, hvh⟩
      have bottom_eval : ∀ {g : ℕ}, IsBottom g → ∀ x : Fin n → Bool,
          gateVal n C g x = true ↔ (∃ u ∈ side C g 0, x u = true) ∧ (∃ v ∈ side C g 1, x v = true) := by
        intro g hg x
        obtain ⟨hgj, hbot⟩ := hg
        have hgj' := (hjunk_mem g).mp hgj
        obtain ⟨hglen, hgand, _⟩ := hgj'
        constructor
        · intro hgx
          have hpq := (wireVal_and x hglen hgand).mp hgx
          have each_side : ∀ b : Fin 2, ∃ u ∈ side C g b, x u = true := by
            intro b
            have hmem := opnd_mem hglen b
            have hlt := opnd_lt hglen b
            rcases wire_trace _ x (hpq _ hmem).2 with ⟨u, hu, hxu⟩ | ⟨h, hh, hhand, hrh, _⟩
            · exact ⟨u, hu, hxu⟩
            · exfalso
              have hb := orReaches_bounds _ h hrh
              obtain ⟨j, hj⟩ : ∃ j, opnd C g b = n + j := ⟨opnd C g b - n, by omega⟩
              have hcone : InCone n C h g := (inCone_iff h g).mpr
                ⟨hglen, j, by omega, hj ▸ hmem, orReaches_inCone _ h hrh j hj⟩
              have hnb : ¬BelowF G C h := fun hb2 => hT h hh g hglen hhand hb2 hgand hcone
              have hdirty : IsDirtyAnd n G C h := by
                refine ⟨hhand, hh, ?_⟩
                by_contra hne
                apply hnb; intro y hy; by_contra hfy
                exact hne ⟨y, hy, Bool.eq_false_iff.mpr hfy⟩
              have hhj : h ∈ Junk := (hjunk_mem h).mpr ⟨hh, hdirty⟩
              exact hbot h hhj hcone
          exact ⟨each_side 0, each_side 1⟩
        · rintro ⟨⟨u, hu, hxu⟩, ⟨v, hv, hxv⟩⟩
          show wireVal n C (n + g) x = true
          rw [wireVal_and x hglen hgand, opnd_pair hglen]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨opnd_lt hglen 0, orIn_up _ u x hu hxu⟩
          · exact ⟨opnd_lt hglen 1, orIn_up _ v x hv hxv⟩
      refine ⟨bottom_eval, ?_⟩
      intro a b g h ha hg hh hrg hrh x ha1 hb1 ha2 hb2
      have ha' := (htops_mem a).mp ha
      obtain ⟨halen, haand, habel⟩ := ha'
      have hgx : gateVal n C g x = true := (bottom_eval hg x).mpr ⟨ha1, hb1⟩
      have hhx : gateVal n C h x = true := (bottom_eval hh x).mpr ⟨ha2, hb2⟩
      have hax : gateVal n C a x = true := by
        show wireVal n C (n + a) x = true
        rw [wireVal_and x halen haand, opnd_pair halen]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        fin_cases b
        · have hrg0 : OrReaches n C (opnd C a 0) g := hrg
          have hrh1 : OrReaches n C (opnd C a 1) h := by
            simpa [show (1 : Fin 2) - 0 = 1 by decide] using hrh
          rcases hi with rfl | rfl
          · exact ⟨opnd_lt halen 0, orReaches_up _ g x hrg0 hgx⟩
          · exact ⟨opnd_lt halen 1, orReaches_up _ h x hrh1 hhx⟩
        · have hrg1 : OrReaches n C (opnd C a 1) g := hrg
          have hrh0 : OrReaches n C (opnd C a 0) h := by
            simpa [show (1 : Fin 2) - 1 = 0 by decide] using hrh
          rcases hi with rfl | rfl
          · exact ⟨opnd_lt halen 0, orReaches_up _ h x hrh0 hhx⟩
          · exact ⟨opnd_lt halen 1, orReaches_up _ g x hrg1 hgx⟩
      have hgf := habel x hax
      rw [hgraphFun_def] at hgf
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hgf
      exact hgf
    obtain ⟨bottom_eval, top_pair_adj⟩ := hBottomEval
    have hTop2 : ∀ {a : ℕ} (b : Fin 2) {g h : ℕ},
        a ∈ Tops → IsBottom g → IsBottom h →
        OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
        ∀ u v : Fin n,
          (u ∈ side C g 0 ∨ v ∈ side C g 0) → (u ∈ side C g 1 ∨ v ∈ side C g 1) →
          (u ∈ side C h 0 ∨ v ∈ side C h 0) → (u ∈ side C h 1 ∨ v ∈ side C h 1) →
          G.Adj u v := by
      intro a b g h ha hg hh hrg hrh u v hg0 hg1 hh0 hh1
      let x : Fin n → Bool := fun z => decide (z = u ∨ z = v)
      have mk : ∀ {S : Finset (Fin n)}, (u ∈ S ∨ v ∈ S) → ∃ w ∈ S, x w = true := by
        intro S hS; rcases hS with hu | hv
        · exact ⟨u, hu, by simp [x]⟩
        · exact ⟨v, hv, by simp [x]⟩
      obtain ⟨p, q, hpq, hp, hq⟩ := top_pair_adj b ha hg hh hrg hrh x (mk hg0) (mk hg1) (mk hh0) (mk hh1)
      simp only [x, decide_eq_true_eq] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact (G.irrefl hpq).elim
      · exact hpq
      · exact hpq.symm
      · exact (G.irrefl hpq).elim
    have hTop3 : ∀ {a : ℕ} (b : Fin 2) {g h : ℕ},
        a ∈ Tops → IsBottom g → IsBottom h →
        OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
        ∀ u v w : Fin n,
          (u ∈ side C g 0 ∨ v ∈ side C g 0 ∨ w ∈ side C g 0) →
          (u ∈ side C g 1 ∨ v ∈ side C g 1 ∨ w ∈ side C g 1) →
          (u ∈ side C h 0 ∨ v ∈ side C h 0 ∨ w ∈ side C h 0) →
          (u ∈ side C h 1 ∨ v ∈ side C h 1 ∨ w ∈ side C h 1) →
          G.Adj u v ∨ G.Adj u w ∨ G.Adj v w := by
      intro a b g h ha hg hh hrg hrh u v w hg0 hg1 hh0 hh1
      let x : Fin n → Bool := fun z => decide (z = u ∨ z = v ∨ z = w)
      have mk : ∀ {S : Finset (Fin n)}, (u ∈ S ∨ v ∈ S ∨ w ∈ S) → ∃ t ∈ S, x t = true := by
        intro S hS; rcases hS with hu | hv | hw
        · exact ⟨u, hu, by simp [x]⟩
        · exact ⟨v, hv, by simp [x]⟩
        · exact ⟨w, hw, by simp [x]⟩
      obtain ⟨p, q, hpq, hp, hq⟩ := top_pair_adj b ha hg hh hrg hrh x (mk hg0) (mk hg1) (mk hh0) (mk hh1)
      simp only [x, decide_eq_true_eq] at hp hq
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
      · exact (G.irrefl hpq).elim
      · exact Or.inl hpq
      · exact Or.inr (Or.inl hpq)
      · exact Or.inl hpq.symm
      · exact (G.irrefl hpq).elim
      · exact Or.inr (Or.inr hpq)
      · exact Or.inr (Or.inl hpq.symm)
      · exact Or.inr (Or.inr hpq.symm)
      · exact (G.irrefl hpq).elim
    have hTop4 : ∀ {a : ℕ} (b : Fin 2) {g h : ℕ},
        a ∈ Tops → IsBottom g → IsBottom h →
        OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
        ∀ w1 w2 w3 w4 : Fin n,
          (w1 ∈ side C g 0 ∨ w2 ∈ side C g 0 ∨ w3 ∈ side C g 0 ∨ w4 ∈ side C g 0) →
          (w1 ∈ side C g 1 ∨ w2 ∈ side C g 1 ∨ w3 ∈ side C g 1 ∨ w4 ∈ side C g 1) →
          (w1 ∈ side C h 0 ∨ w2 ∈ side C h 0 ∨ w3 ∈ side C h 0 ∨ w4 ∈ side C h 0) →
          (w1 ∈ side C h 1 ∨ w2 ∈ side C h 1 ∨ w3 ∈ side C h 1 ∨ w4 ∈ side C h 1) →
          G.Adj w1 w2 ∨ G.Adj w1 w3 ∨ G.Adj w1 w4 ∨ G.Adj w2 w3 ∨ G.Adj w2 w4 ∨ G.Adj w3 w4 := by
      intro a b g h ha hg hh hrg hrh w1 w2 w3 w4 hg0 hg1 hh0 hh1
      let x : Fin n → Bool := fun z => decide (z = w1 ∨ z = w2 ∨ z = w3 ∨ z = w4)
      have mk : ∀ {S : Finset (Fin n)},
          (w1 ∈ S ∨ w2 ∈ S ∨ w3 ∈ S ∨ w4 ∈ S) → ∃ t ∈ S, x t = true := by
        intro S hS; rcases hS with h1 | h2' | h3 | h4
        · exact ⟨w1, h1, by simp [x]⟩
        · exact ⟨w2, h2', by simp [x]⟩
        · exact ⟨w3, h3, by simp [x]⟩
        · exact ⟨w4, h4, by simp [x]⟩
      obtain ⟨p, q, hpq, hp, hq⟩ := top_pair_adj b ha hg hh hrg hrh x (mk hg0) (mk hg1) (mk hh0) (mk hh1)
      simp only [x, decide_eq_true_eq] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
      · exact (G.irrefl hpq).elim
      · exact Or.inl hpq
      · exact Or.inr (Or.inl hpq)
      · exact Or.inr (Or.inr (Or.inl hpq))
      · exact Or.inl hpq.symm
      · exact (G.irrefl hpq).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl hpq)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpq))))
      · exact Or.inr (Or.inl hpq.symm)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hpq.symm)))
      · exact (G.irrefl hpq).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpq))))
      · exact Or.inr (Or.inr (Or.inl hpq.symm))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpq.symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpq.symm))))
      · exact (G.irrefl hpq).elim
    have hStarCounts :
        (∀ (k r : ℕ) (l : List (Finset (Fin n) × ℕ)),
          (∀ p ∈ l, p.1.card ≤ k ∧ (orIn n C p.2 \ p.1.biUnion N).card ≤ r) →
          (l.toFinset.biUnion (fun p =>
            p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))))).card
          ≤ k * (k + r) * (l.length + C.size)) ∧
        (∀ (ℓ r : ℕ) (L : ℕ → Finset (Fin n)) (badC : ℕ → Fin n → Option (Fin n))
          (l : List (Fin n × ℕ × Finset (Fin n))),
          (∀ g, (L g).card ≤ ℓ) →
          (∀ t ∈ l, t.2.2.card ≤ r ∧
            ∀ g < C.gates.length, (gateAt C g).op ≠ GateOp.or → OrReaches n C t.2.1 g →
              ∀ v ∈ L g, G.Adj t.1 v ∨ v ∈ t.2.2 ∨ badC g v = some t.1) →
          (l.toFinset.biUnion (fun t =>
            ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C t.2.1 g)).biUnion
              (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))))).card
          ≤ max ℓ (2 + 2 * r) * (l.length + 2 * C.size)) := by
      have or_stops : ∀ (S : Finset ℕ) (w : ℕ),
          ∃ (Znew stops : Finset ℕ),
            Disjoint Znew S ∧
            (∀ k ∈ Znew, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ OrReaches n C w k) ∧
            stops.card ≤ Znew.card + 1 ∧
            (∀ s ∈ stops,
              (s < n ∧ ∀ u ∈ orIn n C s, u ∈ orIn n C w) ∨
              (n ≤ s ∧ s - n < C.gates.length ∧ OrReaches n C w (s - n) ∧
                ((gateAt C (s - n)).op ≠ GateOp.or ∨ s - n ∈ S))) ∧
            (∀ u ∈ orIn n C w, ∃ s ∈ stops, u ∈ orIn n C s) ∧
            (∀ g < C.gates.length, (gateAt C g).op ≠ GateOp.or → OrReaches n C w g →
              ∃ s ∈ stops, OrReaches n C s g) := by
        intro S w
        induction w using Nat.strong_induction_on generalizing S with
        | _ w ih =>
          by_cases hlt : w < n
          · refine ⟨∅, {w}, Finset.disjoint_empty_left _, by simp, by simp, ?_, ?_, ?_⟩
            · intro s hs; rw [Finset.mem_singleton] at hs; subst hs; exact Or.inl ⟨hlt, fun _ h => h⟩
            · intro u hu; exact ⟨w, Finset.mem_singleton_self _, hu⟩
            · intro g _ _ hr; have := hr.1; omega
          · by_cases hlen : n + C.gates.length ≤ w
            · refine ⟨∅, ∅, Finset.disjoint_empty_left _, by simp, by simp, by simp, ?_, ?_⟩
              · intro u hu
                rw [horIn_mem] at hu
                rcases hu with h | ⟨k, _, hr, _⟩
                · omega
                · have := (orReaches_bounds w k hr).2.1; omega
              · intro g _ _ hr; have := (orReaches_bounds w g hr).2.1; omega
            · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
              have hk : k < C.gates.length := by omega
              by_cases hstop : (gateAt C k).op ≠ GateOp.or ∨ k ∈ S
              · refine ⟨∅, {n + k}, Finset.disjoint_empty_left _, by simp, by simp, ?_, ?_, ?_⟩
                · intro s hs; rw [Finset.mem_singleton] at hs; subst hs
                  exact Or.inr ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left]; exact orReaches_refl hk,
                    by rw [Nat.add_sub_cancel_left]; exact hstop⟩
                · intro u hu; exact ⟨n + k, Finset.mem_singleton_self _, hu⟩
                · intro g _ _ hr; exact ⟨n + k, Finset.mem_singleton_self _, hr⟩
              · push Not at hstop
                obtain ⟨hop, hkS⟩ := hstop
                let p := opnd C k 0
                let q := opnd C k 1
                have hp : p < n + k := opnd_lt hk 0
                have hq : q < n + k := opnd_lt hk 1
                have hpm : p ∈ (gateAt C k).inputs := opnd_mem hk 0
                have hqm : q ∈ (gateAt C k).inputs := opnd_mem hk 1
                obtain ⟨Z1, stops1, hd1, hZ1, hc1, hs1, hu1, hg1⟩ := ih p hp S
                obtain ⟨Z2, stops2, hd2, hZ2, hc2, hs2, hu2, hg2⟩ := ih q hq (S ∪ Z1)
                have hd2S : Disjoint Z2 S := Finset.disjoint_of_subset_right Finset.subset_union_left hd2
                have hd21 : Disjoint Z2 Z1 := Finset.disjoint_of_subset_right Finset.subset_union_right hd2
                have hkZ1 : k ∉ Z1 := fun h => by have := (orReaches_bounds p k (hZ1 k h).2.2).2.2.2; omega
                have hkZ2 : k ∉ Z2 := fun h => by have := (orReaches_bounds q k (hZ2 k h).2.2).2.2.2; omega
                let Znew := insert k (Z1 ∪ Z2)
                let stops2' := stops2.filter (fun s => ¬ (n ≤ s ∧ s - n ∈ Z1))
                let stops := stops1 ∪ stops2'
                have hZnew_card : Znew.card = Z1.card + Z2.card + 1 := by
                  have hnot : k ∉ Z1 ∪ Z2 := by simp [hkZ1, hkZ2]
                  rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hd21.symm]
                have hstops_card : stops.card ≤ Znew.card + 1 := by
                  have h1 := Finset.card_union_le stops1 stops2'
                  have h2' : stops2'.card ≤ stops2.card := Finset.card_le_card (Finset.filter_subset _ _)
                  change (stops1 ∪ stops2').card ≤ Znew.card + 1
                  omega
                refine ⟨Znew, stops, ?_, ?_, hstops_card, ?_, ?_, ?_⟩
                · rw [Finset.disjoint_insert_left]
                  exact ⟨hkS, Finset.disjoint_union_left.mpr ⟨hd1, hd2S⟩⟩
                · intro j hj
                  simp only [Znew, Finset.mem_insert, Finset.mem_union] at hj
                  rcases hj with rfl | hj | hj
                  · exact ⟨hk, hop, orReaches_refl hk⟩
                  · obtain ⟨hj1, hj2, hj3⟩ := hZ1 j hj
                    exact ⟨hj1, hj2, (orReaches_iff k j).mpr ⟨hk, Or.inr ⟨hop, p, hpm, hp, hj3⟩⟩⟩
                  · obtain ⟨hj1, hj2, hj3⟩ := hZ2 j hj
                    exact ⟨hj1, hj2, (orReaches_iff k j).mpr ⟨hk, Or.inr ⟨hop, q, hqm, hq, hj3⟩⟩⟩
                · intro s hs
                  simp only [stops, stops2', Finset.mem_union, Finset.mem_filter] at hs
                  rcases hs with hs | ⟨hs, hnot⟩
                  · rcases hs1 s hs with ⟨hsn, hsub⟩ | ⟨hns, hlen', hrr, hcond⟩
                    · exact Or.inl ⟨hsn, fun u hu => (orIn_gate k u).mpr ⟨hk, hop, p, hpm, hp, hsub u hu⟩⟩
                    · exact Or.inr ⟨hns, hlen', (orReaches_iff k _).mpr ⟨hk, Or.inr ⟨hop, p, hpm, hp, hrr⟩⟩, hcond⟩
                  · rcases hs2 s hs with ⟨hsn, hsub⟩ | ⟨hns, hlen', hrr, hcond⟩
                    · exact Or.inl ⟨hsn, fun u hu => (orIn_gate k u).mpr ⟨hk, hop, q, hqm, hq, hsub u hu⟩⟩
                    · refine Or.inr ⟨hns, hlen', (orReaches_iff k _).mpr ⟨hk, Or.inr ⟨hop, q, hqm, hq, hrr⟩⟩, ?_⟩
                      rcases hcond with hnor | hmem
                      · exact Or.inl hnor
                      · rcases Finset.mem_union.mp hmem with hm | hm
                        · exact Or.inr hm
                        · exact (hnot ⟨hns, hm⟩).elim
                · intro u hu
                  obtain ⟨_, _, i, hi, _, hui⟩ := (orIn_gate k u).mp hu
                  rw [opnd_pair hk] at hi
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · obtain ⟨s, hs, hus⟩ := hu1 u hui
                    exact ⟨s, Finset.mem_union_left _ hs, hus⟩
                  · obtain ⟨s, hs, hus⟩ := hu2 u hui
                    by_cases hZ : n ≤ s ∧ s - n ∈ Z1
                    · have hrr : OrReaches n C p (s - n) := (hZ1 _ hZ.2).2.2
                      have heq : n + (s - n) = s := Nat.add_sub_of_le hZ.1
                      have hup : u ∈ orIn n C p := orIn_mono hrr (heq.symm ▸ hus)
                      obtain ⟨s', hs', hus'⟩ := hu1 u hup
                      exact ⟨s', Finset.mem_union_left _ hs', hus'⟩
                    · exact ⟨s, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hZ⟩), hus⟩
                · intro g hg hgnor hrg
                  obtain ⟨_, h3⟩ := (orReaches_iff k g).mp hrg
                  rcases h3 with rfl | ⟨_, i, hi, _, hri⟩
                  · exact (hgnor hop).elim
                  · rw [opnd_pair hk] at hi
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl
                    · obtain ⟨s, hs, hrs⟩ := hg1 g hg hgnor hri
                      exact ⟨s, Finset.mem_union_left _ hs, hrs⟩
                    · obtain ⟨s, hs, hrs⟩ := hg2 g hg hgnor hri
                      by_cases hZ : n ≤ s ∧ s - n ∈ Z1
                      · have hrr : OrReaches n C p (s - n) := (hZ1 _ hZ.2).2.2
                        have heq : n + (s - n) = s := Nat.add_sub_of_le hZ.1
                        have hrp : OrReaches n C p g := orReaches_trans p (s - n) g hrr (heq.symm ▸ hrs)
                        obtain ⟨s', hs', hrs'⟩ := hg1 g hg hgnor hrp
                        exact ⟨s', Finset.mem_union_left _ hs', hrs'⟩
                      · exact ⟨s, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hZ⟩), hrs⟩
      constructor
      · intro k r l hl
        have step : ∀ (ls : List (Finset (Fin n) × ℕ)),
            (∀ p ∈ ls, p.1.card ≤ k ∧ (orIn n C p.2 \ p.1.biUnion N).card ≤ r) →
            ∃ Z : Finset ℕ,
              (∀ j ∈ Z, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ∃ p ∈ ls, OrReaches n C p.2 j) ∧
              (ls.toFinset.biUnion (fun p =>
                p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))))).card
              ≤ k * (k + r) * (ls.length + Z.card) := by
          intro ls
          induction ls with
          | nil => intro _; exact ⟨∅, by simp, by simp⟩
          | cons p ls ih =>
            intro hls
            obtain ⟨Z, hZ, hcard⟩ := ih (fun q hq => hls q (List.mem_cons_of_mem _ hq))
            have hp := hls p List.mem_cons_self
            set E0 := ls.toFinset.biUnion (fun q =>
              q.1.biUnion (fun c => (orIn n C q.2 ∩ N c).image (fun v => s(c, v)))) with hE0
            set Enew := p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))) with hEnew
            obtain ⟨Znew, stops, hdisj, hZnew, hscard, hstops, hcov, _⟩ := or_stops Z p.2
            refine ⟨Z ∪ Znew, ?_, ?_⟩
            · intro j hj
              rcases Finset.mem_union.mp hj with hj | hj
              · obtain ⟨h1, h2', q, hq, h3⟩ := hZ j hj
                exact ⟨h1, h2', q, List.mem_cons_of_mem _ hq, h3⟩
              · obtain ⟨h1, h2', h3⟩ := hZnew j hj
                exact ⟨h1, h2', p, List.mem_cons_self, h3⟩
            · have hsub : Enew \ E0 ⊆ (p.1 ×ˢ stops).biUnion (fun cs =>
                  ((orIn n C cs.2 ∩ N cs.1).image (fun v => s(cs.1, v))) \ E0) := by
                intro e he
                rw [Finset.mem_sdiff] at he
                obtain ⟨he1, he0⟩ := he
                simp only [hEnew, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter] at he1
                obtain ⟨c, hc, v, ⟨hv, hadj⟩, rfl⟩ := he1
                obtain ⟨s, hs, hvs⟩ := hcov v hv
                refine Finset.mem_biUnion.mpr ⟨(c, s), Finset.mem_product.mpr ⟨hc, hs⟩, ?_⟩
                rw [Finset.mem_sdiff]
                exact ⟨Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨hvs, hadj⟩, rfl⟩, he0⟩
              have heach : ∀ cs ∈ p.1 ×ˢ stops,
                  (((orIn n C cs.2 ∩ N cs.1).image (fun v => s(cs.1, v))) \ E0).card ≤ k + r := by
                intro cs hcs
                obtain ⟨hc, hs⟩ := Finset.mem_product.mp hcs
                rcases hstops cs.2 hs with ⟨hsn, _⟩ | ⟨hns, _, _, hcond⟩
                · have h1 : (orIn n C cs.2).card ≤ 1 := by
                    rw [Finset.card_le_one]
                    intro a ha b hb
                    rw [orIn_input hsn] at ha hb
                    exact Fin.ext (ha.trans hb.symm)
                  have h2' : (((orIn n C cs.2 ∩ N cs.1).image (fun v => s(cs.1, v))) \ E0).card ≤ 1 :=
                    (Finset.card_le_card Finset.sdiff_subset).trans
                      (Finset.card_image_le.trans ((Finset.card_le_card Finset.inter_subset_left).trans h1))
                  have hk1 : 1 ≤ k := by have := Finset.card_pos.mpr ⟨cs.1, hc⟩; omega
                  omega
                · rcases hcond with hnor | hmemZ
                  · have hem : orIn n C cs.2 = ∅ := by
                      ext v; simp only [Finset.notMem_empty, iff_false]
                      have heq : n + (cs.2 - n) = cs.2 := Nat.add_sub_of_le hns
                      rw [← heq, orIn_gate]; intro h; exact hnor h.2.1
                    rw [hem]; simp
                  · obtain ⟨_, _, q, hq, hrr⟩ := hZ (cs.2 - n) hmemZ
                    have heq : n + (cs.2 - n) = cs.2 := Nat.add_sub_of_le hns
                    have hqsub : orIn n C cs.2 ⊆ orIn n C q.2 := by rw [← heq]; exact orIn_mono hrr
                    by_cases hcq : cs.1 ∈ q.1
                    · have hem : ((orIn n C cs.2 ∩ N cs.1).image (fun v => s(cs.1, v))) \ E0 = ∅ := by
                        rw [Finset.sdiff_eq_empty_iff_subset]
                        intro e he
                        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
                        rw [Finset.mem_inter] at hv
                        rw [hE0]
                        refine Finset.mem_biUnion.mpr ⟨q, List.mem_toFinset.mpr hq, ?_⟩
                        refine Finset.mem_biUnion.mpr ⟨cs.1, hcq, ?_⟩
                        exact Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨hqsub hv.1, hv.2⟩, rfl⟩
                      rw [hem]; simp
                    · have hqprop := hls q (List.mem_cons_of_mem _ hq)
                      have hsub2 : orIn n C cs.2 ∩ N cs.1 ⊆
                          q.1.biUnion (fun c' => N cs.1 ∩ N c') ∪ (orIn n C q.2 \ q.1.biUnion N) := by
                        intro v hv
                        rw [Finset.mem_inter] at hv
                        by_cases hhit : v ∈ q.1.biUnion N
                        · rw [Finset.mem_biUnion] at hhit
                          obtain ⟨c', hc', hvc'⟩ := hhit
                          exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
                            ⟨c', hc', Finset.mem_inter.mpr ⟨hv.2, hvc'⟩⟩)
                        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hqsub hv.1, hhit⟩)
                      have hbu : (q.1.biUnion (fun c' => N cs.1 ∩ N c')).card ≤ q.1.card * 1 :=
                        Finset.card_biUnion_le_card_mul _ _ 1 (fun c' hc' => hInterN cs.1 c' (fun h => hcq (h ▸ hc')))
                      have hle1 : (((orIn n C cs.2 ∩ N cs.1).image (fun v => s(cs.1, v))) \ E0).card ≤
                          (q.1.biUnion (fun c' => N cs.1 ∩ N c')).card + (orIn n C q.2 \ q.1.biUnion N).card :=
                        (Finset.card_le_card Finset.sdiff_subset).trans
                          (Finset.card_image_le.trans ((Finset.card_le_card hsub2).trans (Finset.card_union_le _ _)))
                      omega
              have hnew_bound : (Enew \ E0).card ≤ k * (k + r) * (Znew.card + 1) := by
                have h1 := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul _ _ _ heach)
                rw [Finset.card_product] at h1
                have h2' : p.1.card * stops.card ≤ k * (Znew.card + 1) := Nat.mul_le_mul hp.1 hscard
                have h3 : p.1.card * stops.card * (k + r) ≤ k * (Znew.card + 1) * (k + r) :=
                  Nat.mul_le_mul_right _ h2'
                calc (Enew \ E0).card ≤ p.1.card * stops.card * (k + r) := h1
                  _ ≤ k * (Znew.card + 1) * (k + r) := h3
                  _ = k * (k + r) * (Znew.card + 1) := by ring
              rw [List.toFinset_cons, Finset.biUnion_insert, ← hE0, ← hEnew,
                Finset.card_union_of_disjoint hdisj.symm, List.length_cons]
              have hsplit : Enew ∪ E0 = (Enew \ E0) ∪ E0 := (Finset.sdiff_union_self_eq_union).symm
              have hu := Finset.card_union_le (Enew \ E0) E0
              rw [← hsplit] at hu
              calc (Enew ∪ E0).card ≤ (Enew \ E0).card + E0.card := hu
                _ ≤ k * (k + r) * (Znew.card + 1) + k * (k + r) * (ls.length + Z.card) :=
                  Nat.add_le_add hnew_bound hcard
                _ = k * (k + r) * (ls.length + 1 + (Z.card + Znew.card)) := by ring
        obtain ⟨Z, hZ, hcard⟩ := step l hl
        have hZle : Z.card ≤ C.size := by
          rw [hSizeEq]
          simpa using Finset.card_le_card (show Z ⊆ Finset.range C.gates.length from
            fun j hj => Finset.mem_range.mpr (hZ j hj).1)
        exact hcard.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hZle _))
      · intro ℓ r L badC l hLcard hl
        let B := max ℓ (2 + 2 * r)
        have step : ∀ (ls : List (Fin n × ℕ × Finset (Fin n))),
            (∀ t ∈ ls, t.2.2.card ≤ r ∧
              ∀ g < C.gates.length, (gateAt C g).op ≠ GateOp.or → OrReaches n C t.2.1 g →
                ∀ v ∈ L g, G.Adj t.1 v ∨ v ∈ t.2.2 ∨ badC g v = some t.1) →
            ∃ Z1 Z2 : Finset ℕ,
              Z2 ⊆ Z1 ∧
              (∀ k ∈ Z1, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ ∃ t ∈ ls, OrReaches n C t.2.1 k) ∧
              (∀ k ∈ Z2, ∃ t1 ∈ ls, ∃ t2 ∈ ls, t1.1 ≠ t2.1 ∧ OrReaches n C t1.2.1 k ∧ OrReaches n C t2.2.1 k) ∧
              (ls.toFinset.biUnion (fun t =>
                ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C t.2.1 g)).biUnion
                  (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))))).card
              ≤ B * (ls.length + Z1.card + Z2.card) := by
          intro ls
          induction ls with
          | nil => intro _; exact ⟨∅, ∅, Finset.Subset.refl _, by simp, by simp, by simp⟩
          | cons t ls ih =>
            intro hls
            obtain ⟨Z1, Z2, h21, hZ1, hZ2, hcard⟩ := ih (fun q hq => hls q (List.mem_cons_of_mem _ hq))
            set E0 := ls.toFinset.biUnion (fun q =>
              ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C q.2.1 g)).biUnion
                (fun g => ((L g).filter (fun v => G.Adj q.1 v)).image (fun v => s(q.1, v)))) with hE0
            set Enew := ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C t.2.1 g)).biUnion
              (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))) with hEnew
            let S := Z2 ∪ Z1.filter (fun k => ∃ q ∈ ls, q.1 = t.1 ∧ OrReaches n C q.2.1 k)
            obtain ⟨Znew, stops, hdisj, hZnew, hscard, hstops, _, hcovg⟩ := or_stops S t.2.1
            let Z1' := Z1 ∪ (Znew \ Z1)
            let Z2' := Z2 ∪ (Znew ∩ Z1)
            have hdisj1 : Disjoint Z1 (Znew \ Z1) := disjoint_sdiff_self_right
            have hdisj2 : Disjoint Z2 (Znew ∩ Z1) := by
              rw [Finset.disjoint_left]
              intro k hk2 hk
              exact (Finset.disjoint_left.mp hdisj (Finset.mem_inter.mp hk).1) (Finset.mem_union_left _ hk2)
            have hcards : Z1'.card + Z2'.card = Z1.card + Z2.card + Znew.card := by
              rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2]
              have hpart := Finset.card_sdiff_add_card_inter Znew Z1
              omega
            refine ⟨Z1', Z2', ?_, ?_, ?_, ?_⟩
            · intro k hk
              rcases Finset.mem_union.mp hk with hk | hk
              · exact Finset.mem_union_left _ (h21 hk)
              · exact Finset.mem_union_left _ (Finset.mem_inter.mp hk).2
            · intro k hk
              rcases Finset.mem_union.mp hk with hk | hk
              · obtain ⟨h1, h2', q, hq, h3⟩ := hZ1 k hk
                exact ⟨h1, h2', q, List.mem_cons_of_mem _ hq, h3⟩
              · obtain ⟨h1, h2', h3⟩ := hZnew k (Finset.mem_sdiff.mp hk).1
                exact ⟨h1, h2', t, List.mem_cons_self, h3⟩
            · intro k hk
              rcases Finset.mem_union.mp hk with hk | hk
              · obtain ⟨t1, ht1, t2, ht2, hne, hr1, hr2⟩ := hZ2 k hk
                exact ⟨t1, List.mem_cons_of_mem _ ht1, t2, List.mem_cons_of_mem _ ht2, hne, hr1, hr2⟩
              · obtain ⟨hkn, hk1⟩ := Finset.mem_inter.mp hk
                obtain ⟨_, _, q, hq, hrrq⟩ := hZ1 k hk1
                have hne : t.1 ≠ q.1 := fun heq =>
                  (Finset.disjoint_left.mp hdisj hkn)
                    (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk1, q, hq, heq.symm, hrrq⟩))
                exact ⟨t, List.mem_cons_self, q, List.mem_cons_of_mem _ hq, hne, (hZnew k hkn).2.2, hrrq⟩
            · have hsub : Enew \ E0 ⊆ stops.biUnion (fun s =>
                  (((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g)).biUnion
                    (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v)))) \ E0) := by
                intro e he
                rw [Finset.mem_sdiff] at he
                obtain ⟨he1, he0⟩ := he
                simp only [hEnew, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at he1
                obtain ⟨g, ⟨hg, hgnor, hrg⟩, v, ⟨hv, hadj⟩, rfl⟩ := he1
                obtain ⟨s, hs, hrs⟩ := hcovg g hg hgnor hrg
                refine Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_sdiff.mpr ⟨?_, he0⟩⟩
                refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, hgnor, hrs⟩, ?_⟩
                exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hadj⟩, rfl⟩
              have heach : ∀ s ∈ stops,
                  ((((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g)).biUnion
                    (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v)))) \ E0).card ≤ B := by
                intro s hs
                rcases hstops s hs with ⟨hsn, _⟩ | ⟨hns, _, _, hcond⟩
                · have hem : (Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g) = ∅ := by
                    ext g; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
                    intro h; have := h.2.2.1; omega
                  rw [hem]; simp
                · rcases hcond with hnor | hmemS
                  · have hsubg : ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g)).biUnion
                        (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))) ⊆
                        (L (s - n)).image (fun v => s(t.1, v)) := by
                      intro e he
                      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at he
                      obtain ⟨g, ⟨_, _, hrs⟩, v, ⟨hv, _⟩, rfl⟩ := he
                      have heq : n + (s - n) = s := Nat.add_sub_of_le hns
                      rw [← heq, orReaches_iff] at hrs
                      rcases hrs.2 with rfl | ⟨hop, _⟩
                      · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
                      · exact (hnor hop).elim
                    exact ((Finset.card_le_card Finset.sdiff_subset).trans
                      ((Finset.card_le_card hsubg).trans (Finset.card_image_le.trans (hLcard (s - n))))).trans (le_max_left _ _)
                  · rcases Finset.mem_union.mp hmemS with hk2 | hk1
                    · obtain ⟨t1, ht1, t2, ht2, hne12, hr1, hr2⟩ := hZ2 (s - n) hk2
                      have heq : n + (s - n) = s := Nat.add_sub_of_le hns
                      by_cases h1 : t.1 = t1.1
                      · have hem : (((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g)).biUnion
                            (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v)))) \ E0 = ∅ := by
                          rw [Finset.sdiff_eq_empty_iff_subset]
                          intro e he
                          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at he
                          obtain ⟨g, ⟨hg, hgnor, hrs⟩, v, ⟨hv, hadj⟩, rfl⟩ := he
                          rw [hE0]
                          refine Finset.mem_biUnion.mpr ⟨t1, List.mem_toFinset.mpr ht1, ?_⟩
                          refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr
                            ⟨Finset.mem_range.mpr hg, hgnor, orReaches_trans _ _ _ hr1 (heq.symm ▸ hrs)⟩, ?_⟩
                          rw [h1] at hadj ⊢
                          exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hadj⟩, rfl⟩
                        rw [hem]; simp
                      · by_cases h2' : t.1 = t2.1
                        · have hem : (((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g)).biUnion
                              (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v)))) \ E0 = ∅ := by
                            rw [Finset.sdiff_eq_empty_iff_subset]
                            intro e he
                            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at he
                            obtain ⟨g, ⟨hg, hgnor, hrs⟩, v, ⟨hv, hadj⟩, rfl⟩ := he
                            rw [hE0]
                            refine Finset.mem_biUnion.mpr ⟨t2, List.mem_toFinset.mpr ht2, ?_⟩
                            refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr
                              ⟨Finset.mem_range.mpr hg, hgnor, orReaches_trans _ _ _ hr2 (heq.symm ▸ hrs)⟩, ?_⟩
                            rw [h2'] at hadj ⊢
                            exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hadj⟩, rfl⟩
                          rw [hem]; simp
                        · let Cset := (N t.1 ∩ N t1.1) ∪ (N t.1 ∩ N t2.1) ∪ t1.2.2 ∪ t2.2.2
                          have hsubc : (((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g)).biUnion
                              (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v)))) \ E0 ⊆
                              Cset.image (fun v => s(t.1, v)) := by
                            intro e he
                            rw [Finset.mem_sdiff] at he
                            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at he
                            obtain ⟨⟨g, ⟨hg, hgnor, hrs⟩, v, ⟨hv, hadj⟩, rfl⟩, _⟩ := he
                            refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
                            have hp1 := (hls t1 (List.mem_cons_of_mem _ ht1)).2 g hg hgnor
                              (orReaches_trans _ _ _ hr1 (heq.symm ▸ hrs)) v hv
                            have hp2 := (hls t2 (List.mem_cons_of_mem _ ht2)).2 g hg hgnor
                              (orReaches_trans _ _ _ hr2 (heq.symm ▸ hrs)) v hv
                            simp only [Cset, Finset.mem_union, Finset.mem_inter, hMemN]
                            rcases hp1 with ha1 | hr1' | hb1
                            · exact Or.inl (Or.inl (Or.inl ⟨hadj, ha1⟩))
                            · exact Or.inl (Or.inr hr1')
                            · rcases hp2 with ha2 | hr2' | hb2
                              · exact Or.inl (Or.inl (Or.inr ⟨hadj, ha2⟩))
                              · exact Or.inr hr2'
                              · exact (hne12 (Option.some.inj (hb1.symm.trans hb2))).elim
                          have hCcard : Cset.card ≤ 2 + 2 * r := by
                            have u1 := Finset.card_union_le ((N t.1 ∩ N t1.1) ∪ (N t.1 ∩ N t2.1) ∪ t1.2.2) t2.2.2
                            have u2 := Finset.card_union_le ((N t.1 ∩ N t1.1) ∪ (N t.1 ∩ N t2.1)) t1.2.2
                            have u3 := Finset.card_union_le (N t.1 ∩ N t1.1) (N t.1 ∩ N t2.1)
                            have c1 := hInterN t.1 t1.1 h1
                            have c2 := hInterN t.1 t2.1 h2'
                            have r1 := (hls t1 (List.mem_cons_of_mem _ ht1)).1
                            have r2 := (hls t2 (List.mem_cons_of_mem _ ht2)).1
                            dsimp only [Cset]; omega
                          exact ((Finset.card_le_card hsubc).trans (Finset.card_image_le.trans hCcard)).trans
                            (le_max_right _ _)
                    · obtain ⟨_, q, hq, hqt, hrq⟩ := Finset.mem_filter.mp hk1
                      have heq : n + (s - n) = s := Nat.add_sub_of_le hns
                      have hem : (((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C s g)).biUnion
                          (fun g => ((L g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v)))) \ E0 = ∅ := by
                        rw [Finset.sdiff_eq_empty_iff_subset]
                        intro e he
                        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at he
                        obtain ⟨g, ⟨hg, hgnor, hrs⟩, v, ⟨hv, hadj⟩, rfl⟩ := he
                        rw [hE0]
                        refine Finset.mem_biUnion.mpr ⟨q, List.mem_toFinset.mpr hq, ?_⟩
                        refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr
                          ⟨Finset.mem_range.mpr hg, hgnor, orReaches_trans _ _ _ hrq (heq.symm ▸ hrs)⟩, ?_⟩
                        rw [← hqt] at hadj ⊢
                        exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hadj⟩, rfl⟩
                      rw [hem]; simp
              have hnew_bound : (Enew \ E0).card ≤ B * (Znew.card + 1) := by
                have h1 := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul _ _ _ heach)
                calc (Enew \ E0).card ≤ stops.card * B := h1
                  _ ≤ (Znew.card + 1) * B := Nat.mul_le_mul_right _ hscard
                  _ = B * (Znew.card + 1) := Nat.mul_comm _ _
              rw [List.toFinset_cons, Finset.biUnion_insert, ← hE0, ← hEnew, List.length_cons]
              have hsplit : Enew ∪ E0 = (Enew \ E0) ∪ E0 := (Finset.sdiff_union_self_eq_union).symm
              have hu := Finset.card_union_le (Enew \ E0) E0
              rw [← hsplit] at hu
              calc (Enew ∪ E0).card ≤ (Enew \ E0).card + E0.card := hu
                _ ≤ B * (Znew.card + 1) + B * (ls.length + Z1.card + Z2.card) := Nat.add_le_add hnew_bound hcard
                _ = B * (ls.length + 1 + Z1'.card + Z2'.card) := by
                  rw [← Nat.mul_add]; congr 1; omega
        obtain ⟨Z1, Z2, h21, hZ1, _, hcard⟩ := step l hl
        have hZ1le : Z1.card ≤ C.size := by
          rw [hSizeEq]
          simpa using Finset.card_le_card (show Z1 ⊆ Finset.range C.gates.length from
            fun k hk => Finset.mem_range.mpr (hZ1 k hk).1)
        have hZ2le : Z2.card ≤ C.size := (Finset.card_le_card h21).trans hZ1le
        exact hcard.trans (Nat.mul_le_mul_left _ (by omega))
    obtain ⟨or_star_count, two_visit_star_count⟩ := hStarCounts
    have hTopsCard : Tops.card ≤ C.size := by
      have hsub : Tops ⊆ Finset.range C.gates.length := fun a ha => Finset.mem_range.mpr ((htops_mem a).mp ha).1
      rw [hSizeEq]; simpa using Finset.card_le_card hsub
    have hJunkCard : Junk.card ≤ C.size := by
      have hsub : Junk ⊆ Finset.range C.gates.length := fun g hg => Finset.mem_range.mpr ((hjunk_mem g).mp hg).1
      rw [hSizeEq]; simpa using Finset.card_le_card hsub
    have hTops2 : (Tops ×ˢ (Finset.univ : Finset (Fin 2))).card ≤ 2 * C.size := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]; omega
    have hJunk2 : (Junk ×ˢ (Finset.univ : Finset (Fin 2))).card ≤ 2 * C.size := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]; omega
    have hgate_len : ∀ {g : ℕ}, g ∈ Junk → g < C.gates.length ∧ (gateAt C g).op ≠ GateOp.or := by
      intro g hg
      have hg' := (hjunk_mem g).mp hg
      refine ⟨hg'.1, fun hor => ?_⟩
      have := hg'.2.1; rw [hor] at this; cases this
    let S1 : ℕ → Finset (Fin n) := fun g => side C g 0 ∩ side C g 1
    let L : ℕ → Fin 2 → Finset (Fin n) := fun a b =>
      Finset.univ.filter (fun w => ∃ g, IsBottom g ∧ OrReaches n C (opnd C a b) g ∧ w ∈ S1 g)
    obtain ⟨E1, hE1, mE1⟩ : ∃ E1 : Finset (Sym2 (Fin n)), E1.card ≤ 12 * C.size ∧
        ∀ a ∈ Tops, ∀ b : Fin 2, ∀ g h : ℕ, ∀ c w : Fin n,
          G.Adj c w → IsBottom g → IsBottom h →
          OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
          c ∈ S1 g → w ∈ S1 h → (L a b).card = 1 → (S1 h).card ≤ 3 → s(c, w) ∈ E1 := by
      let L1 : ℕ → Finset (Fin n) := fun g => if IsBottom g ∧ (S1 g).card ≤ 3 then S1 g else ∅
      have hL1card : ∀ g, (L1 g).card ≤ 3 := by
        intro g; dsimp only [L1]; split_ifs with h
        · exact h.2
        · simp
      let T1 := ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (L p.1 p.2).card = 1)).biUnion
        (fun p => (L p.1 p.2).image (fun c => (c, opnd C p.1 (1 - p.2), (∅ : Finset (Fin n)))))
      have hT1card : T1.card ≤ 2 * C.size := by
        have h1 : T1.card ≤ ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (L p.1 p.2).card = 1)).card * 1 :=
          Finset.card_biUnion_le_card_mul _ _ 1 (fun p hp => by
            rw [Finset.mem_filter] at hp
            exact Finset.card_image_le.trans (le_of_eq hp.2))
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => (L p.1 p.2).card = 1) (Tops ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E1 := T1.toList.toFinset.biUnion (fun t =>
        ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C t.2.1 g)).biUnion
          (fun g => ((L1 g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))))
      refine ⟨E1, ?_, ?_⟩
      · have hcov := two_visit_star_count 3 0 L1 (fun _ _ => none) T1.toList hL1card (by
          intro t ht
          rw [Finset.mem_toList] at ht
          simp only [T1, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            and_true, Finset.mem_image] at ht
          obtain ⟨⟨a, b⟩, ⟨ha, _⟩, c, hc, rfl⟩ := ht
          refine ⟨by simp, ?_⟩
          intro h _ _ hrh v hv
          dsimp only [L1] at hv
          split_ifs at hv with hbot
          · left
            simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hc
            obtain ⟨g, hg, hrg, hcg⟩ := hc
            simp only [S1, Finset.mem_inter] at hcg hv
            exact hTop2 b ha hg hbot.1 hrg hrh c v (Or.inl hcg.1) (Or.inl hcg.2) (Or.inr hv.1) (Or.inr hv.2)
          · simp at hv)
        rw [Finset.length_toList] at hcov
        have : max 3 (2 + 2 * 0) = 3 := by decide
        rw [this] at hcov
        calc E1.card ≤ 3 * (T1.card + 2 * C.size) := hcov
          _ ≤ 3 * (2 * C.size + 2 * C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 12 * C.size := by ring
      · intro a ha b g h c w hcw hgb hhb hrg hrh hcg hwh hcard1 hs1
        dsimp only [E1]
        refine Finset.mem_biUnion.mpr ⟨(c, opnd C a (1 - b), ∅), ?_, ?_⟩
        · rw [List.mem_toFinset, Finset.mem_toList]
          refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, hcard1⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hgb, hrg, hcg⟩, rfl⟩
        · obtain ⟨hhlen, hhnor⟩ := hgate_len hhb.1
          refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hhlen, hhnor, hrh⟩, ?_⟩
          refine Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨?_, hcw⟩, rfl⟩
          dsimp only [L1]; rw [if_pos ⟨hhb, hs1⟩]; exact hwh
    obtain ⟨E2, hE2, mE2⟩ : ∃ E2 : Finset (Sym2 (Fin n)), E2.card ≤ 6 * C.size ∧
        ∀ g ∈ Junk, ∀ d : Fin 2, ∀ c w : Fin n,
          G.Adj c w → 4 ≤ (side (n := n) C g d).card → (side (n := n) C g d \ N c).card ≤ 1 → w ∈ side (n := n) C g d → s(c, w) ∈ E2 := by
      let T2 := ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => 4 ≤ (side (n := n) C p.1 p.2).card)).biUnion
        (fun p => (Finset.univ.filter (fun c => (side (n := n) C p.1 p.2 \ N c).card ≤ 1)).image (fun c => (({c} : Finset (Fin n)), opnd C p.1 p.2)))
      have hT2card : T2.card ≤ 2 * C.size := by
        have h1 : T2.card ≤ ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => 4 ≤ (side (n := n) C p.1 p.2).card)).card * 1 :=
          Finset.card_biUnion_le_card_mul _ _ 1 (fun p hp => by
            rw [Finset.mem_filter] at hp
            refine Finset.card_image_le.trans ?_
            rw [Finset.card_le_one]
            intro c1 hc1 c2 hc2
            rw [Finset.mem_filter] at hc1 hc2
            exact hUniqueCenter (side (n := n) C p.1 p.2) 1 (by omega) c1 c2 hc1.2 hc2.2)
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => 4 ≤ (side (n := n) C p.1 p.2).card) (Junk ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E2 := T2.toList.toFinset.biUnion (fun p =>
        p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))))
      refine ⟨E2, ?_, ?_⟩
      · have hcov := or_star_count 1 1 T2.toList (by
          intro q hq
          rw [Finset.mem_toList] at hq
          simp only [T2, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hq
          obtain ⟨⟨g, d⟩, _, c, hc, rfl⟩ := hq
          refine ⟨by simp, ?_⟩
          have hbu1 : ({c} : Finset (Fin n)).biUnion N = N c := by ext w; simp
          rw [hbu1, ← hside_def]; exact hc)
        rw [Finset.length_toList] at hcov
        calc E2.card ≤ 1 * (1 + 1) * (T2.card + C.size) := hcov
          _ ≤ 1 * (1 + 1) * (2 * C.size + C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 6 * C.size := by ring
      · intro g hg d c w hcw h4 hex hw
        dsimp only [E2]
        refine Finset.mem_biUnion.mpr ⟨({c}, opnd C g d), ?_, ?_⟩
        · rw [List.mem_toFinset, Finset.mem_toList]
          refine Finset.mem_biUnion.mpr ⟨(g, d), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, h4⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex⟩, rfl⟩
        · refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_singleton_self _, ?_⟩
          exact Finset.mem_image.mpr ⟨w, Finset.mem_inter.mpr ⟨hw, (hMemN c w).mpr hcw⟩, rfl⟩
    obtain ⟨E3, hE3, mE3⟩ : ∃ E3 : Finset (Sym2 (Fin n)), E3.card ≤ 3 * C.size ∧
        ∀ g ∈ Junk, ∀ d : Fin 2, ∀ c w : Fin n,
          G.Adj c w → 2 ≤ (side (n := n) C g d).card → side (n := n) C g d ⊆ N c → w ∈ side (n := n) C g d → s(c, w) ∈ E3 := by
      let T3 := ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => 2 ≤ (side (n := n) C p.1 p.2).card)).biUnion
        (fun p => (Finset.univ.filter (fun c => (side (n := n) C p.1 p.2 \ N c).card ≤ 0)).image (fun c => (({c} : Finset (Fin n)), opnd C p.1 p.2)))
      have hT3card : T3.card ≤ 2 * C.size := by
        have h1 : T3.card ≤ ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => 2 ≤ (side (n := n) C p.1 p.2).card)).card * 1 :=
          Finset.card_biUnion_le_card_mul _ _ 1 (fun p hp => by
            rw [Finset.mem_filter] at hp
            refine Finset.card_image_le.trans ?_
            rw [Finset.card_le_one]
            intro c1 hc1 c2 hc2
            rw [Finset.mem_filter] at hc1 hc2
            exact hUniqueCenter (side (n := n) C p.1 p.2) 0 (by omega) c1 c2 hc1.2 hc2.2)
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => 2 ≤ (side (n := n) C p.1 p.2).card) (Junk ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E3 := T3.toList.toFinset.biUnion (fun p =>
        p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))))
      refine ⟨E3, ?_, ?_⟩
      · have hcov := or_star_count 1 0 T3.toList (by
          intro q hq
          rw [Finset.mem_toList] at hq
          simp only [T3, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hq
          obtain ⟨⟨g, d⟩, _, c, hc, rfl⟩ := hq
          refine ⟨by simp, ?_⟩
          have hbu1 : ({c} : Finset (Fin n)).biUnion N = N c := by ext w; simp
          rw [hbu1, ← hside_def]; exact hc)
        rw [Finset.length_toList] at hcov
        calc E3.card ≤ 1 * (1 + 0) * (T3.card + C.size) := hcov
          _ ≤ 1 * (1 + 0) * (2 * C.size + C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 3 * C.size := by ring
      · intro g hg d c w hcw h2' hsub hw
        dsimp only [E3]
        refine Finset.mem_biUnion.mpr ⟨({c}, opnd C g d), ?_, ?_⟩
        · rw [List.mem_toFinset, Finset.mem_toList]
          refine Finset.mem_biUnion.mpr ⟨(g, d), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, h2'⟩, ?_⟩
          refine Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub]; simp
        · refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_singleton_self _, ?_⟩
          exact Finset.mem_image.mpr ⟨w, Finset.mem_inter.mpr ⟨hw, (hMemN c w).mpr hcw⟩, rfl⟩
    obtain ⟨E4, hE4, mE4⟩ : ∃ E4 : Finset (Sym2 (Fin n)), E4.card ≤ 6 * C.size ∧
        ∀ g ∈ Junk, ∀ d : Fin 2, ∀ c w : Fin n,
          G.Adj c w → (side (n := n) C g (1 - d)).card = 1 → c ∈ side (n := n) C g (1 - d) →
          (side (n := n) C g d \ N c).card ≤ 1 → w ∈ side (n := n) C g d → s(c, w) ∈ E4 := by
      let T4 := ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (side (n := n) C p.1 (1 - p.2)).card = 1)).biUnion
        (fun p => ((side (n := n) C p.1 (1 - p.2)).filter (fun c => (side (n := n) C p.1 p.2 \ N c).card ≤ 1)).image (fun c => (({c} : Finset (Fin n)), opnd C p.1 p.2)))
      have hT4card : T4.card ≤ 2 * C.size := by
        have h1 : T4.card ≤ ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (side (n := n) C p.1 (1 - p.2)).card = 1)).card * 1 :=
          Finset.card_biUnion_le_card_mul _ _ 1 (fun p hp => by
            rw [Finset.mem_filter] at hp
            exact Finset.card_image_le.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans (le_of_eq hp.2)))
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => (side (n := n) C p.1 (1 - p.2)).card = 1) (Junk ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E4 := T4.toList.toFinset.biUnion (fun p =>
        p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))))
      refine ⟨E4, ?_, ?_⟩
      · have hcov := or_star_count 1 1 T4.toList (by
          intro q hq
          rw [Finset.mem_toList] at hq
          simp only [T4, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hq
          obtain ⟨⟨g, d⟩, _, c, ⟨_, hc⟩, rfl⟩ := hq
          refine ⟨by simp, ?_⟩
          have hbu1 : ({c} : Finset (Fin n)).biUnion N = N c := by ext w; simp
          rw [hbu1, ← hside_def]; exact hc)
        rw [Finset.length_toList] at hcov
        calc E4.card ≤ 1 * (1 + 1) * (T4.card + C.size) := hcov
          _ ≤ 1 * (1 + 1) * (2 * C.size + C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 6 * C.size := by ring
      · intro g hg d c w hcw h1 hc hex hw
        dsimp only [E4]
        refine Finset.mem_biUnion.mpr ⟨({c}, opnd C g d), ?_, ?_⟩
        · rw [List.mem_toFinset, Finset.mem_toList]
          refine Finset.mem_biUnion.mpr ⟨(g, d), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, h1⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hex⟩, rfl⟩
        · refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_singleton_self _, ?_⟩
          exact Finset.mem_image.mpr ⟨w, Finset.mem_inter.mpr ⟨hw, (hMemN c w).mpr hcw⟩, rfl⟩
    obtain ⟨E5, hE5, mE5⟩ : ∃ E5 : Finset (Sym2 (Fin n)), E5.card ≤ 32 * C.size ∧
        ∀ a ∈ Tops, ∀ b : Fin 2, ∀ g h : ℕ, ∀ d : Fin 2, ∀ x y : Fin n,
          G.Adj x y → IsBottom g → IsBottom h →
          OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
          x ∈ S1 g → (L a b).card ≤ 3 → (side (n := n) C h (1 - d)).card = 1 →
          y ∈ side (n := n) C h (1 - d) → 2 ≤ (side (n := n) C h d \ N y).card → s(x, y) ∈ E5 := by
      let L5 : Fin 2 → ℕ → Finset (Fin n) := fun d h =>
        if IsBottom h ∧ (side (n := n) C h (1 - d)).card = 1 ∧ (∀ v ∈ side (n := n) C h (1 - d), 2 ≤ (side (n := n) C h d \ N v).card)
        then side (n := n) C h (1 - d) else ∅
      let B5 : Fin 2 → ℕ → Fin n → Finset (Fin n) := fun d h v =>
        Finset.univ.filter (fun w => ¬ G.Adj w v ∧ ∀ z ∈ side C h d \ N v, G.Adj w z)
      let bad5 : Fin 2 → ℕ → Fin n → Option (Fin n) := fun d h v =>
        if hb : (B5 d h v).Nonempty then some hb.choose else none
      let T5 := ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (L p.1 p.2).card ≤ 3)).biUnion
        (fun p => (L p.1 p.2).image (fun w => (w, opnd C p.1 (1 - p.2), (∅ : Finset (Fin n)))))
      have hT5card : T5.card ≤ 6 * C.size := by
        have h1 : T5.card ≤ ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (L p.1 p.2).card ≤ 3)).card * 3 :=
          Finset.card_biUnion_le_card_mul _ _ 3 (fun p hp => by
            rw [Finset.mem_filter] at hp
            exact Finset.card_image_le.trans hp.2)
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => (L p.1 p.2).card ≤ 3) (Tops ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E5d : Fin 2 → Finset (Sym2 (Fin n)) := fun d =>
        T5.toList.toFinset.biUnion (fun t =>
          ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C t.2.1 g)).biUnion
            (fun g => ((L5 d g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))))
      have hE5d : ∀ d : Fin 2, (E5d d).card ≤ 16 * C.size := by
        intro d
        have hL5 : ∀ g, (L5 d g).card ≤ 1 := by
          intro g; dsimp only [L5]; split_ifs with h
          · omega
          · simp
        have hcov := two_visit_star_count 1 0 (L5 d) (bad5 d) T5.toList hL5 (by
          intro t ht
          rw [Finset.mem_toList] at ht
          simp only [T5, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            and_true, Finset.mem_image] at ht
          obtain ⟨⟨a, b⟩, ⟨ha, _⟩, w, hw, rfl⟩ := ht
          refine ⟨by simp, ?_⟩
          intro h _ _ hrh v hv
          dsimp only [L5] at hv
          split_ifs at hv with hcond
          · by_cases hadj : G.Adj w v
            · exact Or.inl hadj
            · right; right
              obtain ⟨hh, _, h2'⟩ := hcond
              simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hw
              obtain ⟨g, hg, hrg, hwg⟩ := hw
              simp only [S1, Finset.mem_inter] at hwg
              have hwB : w ∈ B5 d h v := by
                simp only [B5, Finset.mem_filter, Finset.mem_univ, true_and]
                refine ⟨hadj, fun z hz => ?_⟩
                rw [Finset.mem_sdiff, hMemN] at hz
                have ht3 : G.Adj w z ∨ G.Adj w v ∨ G.Adj z v := by
                  fin_cases d
                  · exact hTop3 b ha hg hh hrg hrh w z v
                      (Or.inl hwg.1) (Or.inl hwg.2) (Or.inr (Or.inl hz.1))
                      (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hv)))
                  · exact hTop3 b ha hg hh hrg hrh w z v
                      (Or.inl hwg.1) (Or.inl hwg.2)
                      (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hv)))
                      (Or.inr (Or.inl hz.1))
                rcases ht3 with h1 | h2'' | h3
                · exact h1
                · exact (hadj h2'').elim
                · exact (hz.2 h3.symm).elim
              have hBcard : (B5 d h v).card ≤ 1 := by
                have hv2 := h2' v hv
                obtain ⟨z1, hz1, z2, hz2, hzne⟩ := Finset.one_lt_card.mp (by omega : 1 < (side (n := n) C h d \ N v).card)
                have hsub : B5 d h v ⊆ N z1 ∩ N z2 := by
                  intro u hu
                  simp only [B5, Finset.mem_filter, Finset.mem_univ, true_and] at hu
                  rw [Finset.mem_inter, hMemN, hMemN]
                  exact ⟨(hu.2 z1 hz1).symm, (hu.2 z2 hz2).symm⟩
                exact (Finset.card_le_card hsub).trans (hInterN z1 z2 hzne)
              have hne : (B5 d h v).Nonempty := ⟨w, hwB⟩
              dsimp only [bad5]; rw [dif_pos hne]; congr 1
              exact Finset.card_le_one.mp hBcard _ hne.choose_spec _ hwB
          · simp at hv)
        rw [Finset.length_toList] at hcov
        have : max 1 (2 + 2 * 0) = 2 := by decide
        rw [this] at hcov
        calc (E5d d).card ≤ 2 * (T5.card + 2 * C.size) := hcov
          _ ≤ 2 * (6 * C.size + 2 * C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 16 * C.size := by ring
      refine ⟨E5d 0 ∪ E5d 1, ?_, ?_⟩
      · have hu := Finset.card_union_le (E5d 0) (E5d 1)
        have c0 := hE5d 0; have c1 := hE5d 1; omega
      · intro a ha b g h d x y hxy hgb hhb hrg hrh hxg hL3 hQ1 hyd hP2
        have hmem5d : s(x, y) ∈ E5d d := by
          dsimp only [E5d]
          refine Finset.mem_biUnion.mpr ⟨(x, opnd C a (1 - b), ∅), ?_, ?_⟩
          · rw [List.mem_toFinset, Finset.mem_toList]
            refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, hL3⟩, ?_⟩
            exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hgb, hrg, hxg⟩, rfl⟩
          · obtain ⟨hhlen, hhnor⟩ := hgate_len hhb.1
            refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr hhlen, hhnor, hrh⟩, ?_⟩
            refine Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨?_, hxy⟩, rfl⟩
            dsimp only [L5]
            rw [if_pos ⟨hhb, hQ1, fun v' hv' => by
              have heq := Finset.card_le_one.mp (le_of_eq hQ1) v' hv' y hyd
              rw [heq]; exact hP2⟩]
            exact hyd
        fin_cases d
        · exact Finset.mem_union_left _ hmem5d
        · exact Finset.mem_union_right _ hmem5d
    obtain ⟨E6, hE6, mE6⟩ : ∃ E6 : Finset (Sym2 (Fin n)), E6.card ≤ 16 * C.size ∧
        ∀ a ∈ Tops, ∀ b : Fin 2, ∀ g : ℕ, ∀ x y : Fin n,
          G.Adj y x → IsBottom g → OrReaches n C (opnd C a b) g →
          x ∈ S1 g → (S1 g).card ≤ 3 → 4 ≤ (L a b).card → (L a b \ N y).card ≤ 1 → s(y, x) ∈ E6 := by
      let L1 : ℕ → Finset (Fin n) := fun g => if IsBottom g ∧ (S1 g).card ≤ 3 then S1 g else ∅
      have hL1card : ∀ g, (L1 g).card ≤ 3 := by
        intro g; dsimp only [L1]; split_ifs with h
        · exact h.2
        · simp
      let T6 := ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => 4 ≤ (L p.1 p.2).card)).biUnion
        (fun p => (Finset.univ.filter (fun v => (L p.1 p.2 \ N v).card ≤ 1)).image
          (fun v => (v, opnd C p.1 p.2, L p.1 p.2 \ N v)))
      have hT6card : T6.card ≤ 2 * C.size := by
        have h1 : T6.card ≤ ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => 4 ≤ (L p.1 p.2).card)).card * 1 :=
          Finset.card_biUnion_le_card_mul _ _ 1 (fun p hp => by
            rw [Finset.mem_filter] at hp
            refine Finset.card_image_le.trans ?_
            rw [Finset.card_le_one]
            intro v1 hv1 v2 hv2
            rw [Finset.mem_filter] at hv1 hv2
            exact hUniqueCenter (L p.1 p.2) 1 (by omega) v1 v2 hv1.2 hv2.2)
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => 4 ≤ (L p.1 p.2).card) (Tops ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E6 := T6.toList.toFinset.biUnion (fun t =>
        ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C t.2.1 g)).biUnion
          (fun g => ((L1 g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))))
      refine ⟨E6, ?_, ?_⟩
      · have hcov := two_visit_star_count 3 1 L1 (fun _ _ => none) T6.toList hL1card (by
          intro t ht
          rw [Finset.mem_toList] at ht
          simp only [T6, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            and_true, Finset.mem_image] at ht
          obtain ⟨⟨a, b⟩, _, v, hv, rfl⟩ := ht
          refine ⟨hv.2, ?_⟩
          intro g _ _ hrg w hw
          dsimp only [L1] at hw
          split_ifs at hw with hbot
          · have hwL : w ∈ L a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hbot.1, hrg, hw⟩
            by_cases hadj : G.Adj v w
            · exact Or.inl hadj
            · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hwL, by rw [hMemN]; exact hadj⟩))
          · simp at hw)
        rw [Finset.length_toList] at hcov
        have : max 3 (2 + 2 * 1) = 4 := by decide
        rw [this] at hcov
        calc E6.card ≤ 4 * (T6.card + 2 * C.size) := hcov
          _ ≤ 4 * (2 * C.size + 2 * C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 16 * C.size := by ring
      · intro a ha b g x y hyx hgb hrg hxg hS1g hL4 hLexc
        dsimp only [E6]
        refine Finset.mem_biUnion.mpr ⟨(y, opnd C a b, L a b \ N y), ?_, ?_⟩
        · rw [List.mem_toFinset, Finset.mem_toList]
          refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, hL4⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLexc⟩, rfl⟩
        · obtain ⟨hglen, hgnor⟩ := hgate_len hgb.1
          refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hglen, hgnor, hrg⟩, ?_⟩
          refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨?_, hyx⟩, rfl⟩
          dsimp only [L1]; rw [if_pos ⟨hgb, hS1g⟩]; exact hxg
    obtain ⟨E7, hE7, mE7⟩ : ∃ E7 : Finset (Sym2 (Fin n)), E7.card ≤ 12 * C.size ∧
        ∀ g ∈ Junk, ∀ x y : Fin n,
          G.Adj y x → x ∈ S1 g → 4 ≤ (S1 g).card → (S1 g \ N y).card ≤ 1 →
          (∃ (d' : Fin 2) (z : Fin n), (side (n := n) C g d' \ (N y ∪ N z)).card ≤ 1) → s(y, x) ∈ E7 := by
      let P7 : ℕ → Fin n → Prop := fun g v =>
        (S1 g \ N v).card ≤ 1 ∧ ∃ (d' : Fin 2) (z : Fin n), (side (n := n) C g d' \ (N v ∪ N z)).card ≤ 1
      let T7 := ((Junk).filter (fun g => 4 ≤ (S1 g).card)).biUnion (fun g =>
        (Finset.univ.filter (fun v => P7 g v)).image (fun v =>
          if h : ∃ (d' : Fin 2) (z : Fin n), (side (n := n) C g d' \ (N v ∪ N z)).card ≤ 1
          then (({v, h.choose_spec.choose} : Finset (Fin n)), opnd C g h.choose)
          else (({v} : Finset (Fin n)), opnd C g 0)))
      have hT7card : T7.card ≤ C.size := by
        have h1 : T7.card ≤ ((Junk).filter (fun g => 4 ≤ (S1 g).card)).card * 1 :=
          Finset.card_biUnion_le_card_mul _ _ 1 (fun g hg => by
            rw [Finset.mem_filter] at hg
            refine Finset.card_image_le.trans ?_
            rw [Finset.card_le_one]
            intro v1 hv1 v2 hv2
            rw [Finset.mem_filter] at hv1 hv2
            exact hUniqueCenter (S1 g) 1 (by omega) v1 v2 hv1.2.1 hv2.2.1)
        have h2' := Finset.card_le_card (Finset.filter_subset (fun g : ℕ => 4 ≤ (S1 g).card) (Junk))
        omega
      let E7 := T7.toList.toFinset.biUnion (fun p =>
        p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))))
      refine ⟨E7, ?_, ?_⟩
      · have hcov := or_star_count 2 1 T7.toList (by
          intro q hq
          rw [Finset.mem_toList] at hq
          simp only [T7, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hq
          obtain ⟨g, _, v, hv, rfl⟩ := hq
          have hex : ∃ (d' : Fin 2) (z : Fin n), (side C g d' \ (N v ∪ N z)).card ≤ 1 := hv.2
          rw [dif_pos hex]
          refine ⟨Finset.card_le_two, ?_⟩
          have hbu : ({v, hex.choose_spec.choose} : Finset (Fin n)).biUnion N = N v ∪ N hex.choose_spec.choose := by
            ext w; simp
          rw [hbu]; exact hex.choose_spec.choose_spec)
        rw [Finset.length_toList] at hcov
        calc E7.card ≤ 2 * (2 + 1) * (T7.card + C.size) := hcov
          _ ≤ 2 * (2 + 1) * (C.size + C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 12 * C.size := by ring
      · intro g hg x y hyx hxg hS1g4 hS1exc hex7
        dsimp only [E7]
        refine Finset.mem_biUnion.mpr ⟨({y, hex7.choose_spec.choose}, opnd C g hex7.choose), ?_, ?_⟩
        · rw [List.mem_toFinset, Finset.mem_toList]
          refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hS1g4⟩, ?_⟩
          refine Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS1exc, hex7⟩, ?_⟩
          rw [dif_pos hex7]
        · refine Finset.mem_biUnion.mpr ⟨y, Finset.mem_insert_self _ _, ?_⟩
          have hxd' : x ∈ side C g hex7.choose := by
            have hall : ∀ d : Fin 2, x ∈ side C g d := fun d => by
              fin_cases d
              · exact (Finset.mem_inter.mp hxg).1
              · exact (Finset.mem_inter.mp hxg).2
            exact hall hex7.choose
          exact Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr ⟨hxd', (hMemN y x).mpr hyx⟩, rfl⟩
    obtain ⟨E8, hE8, mE8⟩ : ∃ E8 : Finset (Sym2 (Fin n)), E8.card ≤ 9 * C.size ∧
        ∀ g ∈ Junk, ∀ d : Fin 2, ∀ x y : Fin n,
          (side (n := n) C g d).card ≤ 3 → (side (n := n) C g (1 - d)).card ≤ 3 →
          x ∈ side (n := n) C g d → y ∈ side (n := n) C g (1 - d) → s(x, y) ∈ E8 := by
      let E8 := ((Junk).filter (fun g => (side (n := n) C g 0).card ≤ 3 ∧ (side (n := n) C g 1).card ≤ 3)).biUnion
        (fun g => (side (n := n) C g 0 ×ˢ side (n := n) C g 1).image (fun pq => s(pq.1, pq.2)))
      refine ⟨E8, ?_, ?_⟩
      · have h1 : E8.card ≤ ((Junk).filter (fun g => (side (n := n) C g 0).card ≤ 3 ∧ (side (n := n) C g 1).card ≤ 3)).card * 9 :=
          Finset.card_biUnion_le_card_mul _ _ 9 (fun g hg => by
            rw [Finset.mem_filter] at hg
            refine Finset.card_image_le.trans ?_
            rw [Finset.card_product]
            exact Nat.mul_le_mul hg.2.1 hg.2.2)
        have h2' := Finset.card_le_card (Finset.filter_subset (fun g : ℕ => (side (n := n) C g 0).card ≤ 3 ∧ (side (n := n) C g 1).card ≤ 3) (Junk))
        omega
      · intro g hg d x y hc1 hc2 hx hy
        dsimp only [E8]
        fin_cases d
        · have hc2' : (side (n := n) C g 1).card ≤ 3 := by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hc2
          have hy' : y ∈ side C g 1 := by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hy
          refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hc1, hc2'⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy'⟩, rfl⟩
        · have hc2' : (side (n := n) C g 0).card ≤ 3 := by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hc2
          have hy' : y ∈ side C g 0 := by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hy
          refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hc2', hc1⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨(y, x), Finset.mem_product.mpr ⟨hy', hx⟩, Sym2.eq_swap⟩
    obtain ⟨E9, hE9, mE9⟩ : ∃ E9 : Finset (Sym2 (Fin n)), E9.card ≤ 28 * C.size ∧
        ∀ g ∈ Junk, ∀ d : Fin 2, ∀ c w : Fin n,
          G.Adj c w → (side (n := n) C g d).card ≤ 3 → c ∈ side (n := n) C g d →
          (side (n := n) C g (1 - d) \ N c).card ≤ 3 → w ∈ side (n := n) C g (1 - d) → s(c, w) ∈ E9 := by
      let T9 := ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (side (n := n) C p.1 p.2).card ≤ 3)).biUnion
        (fun p => ((side (n := n) C p.1 p.2).filter (fun c => (side (n := n) C p.1 (1 - p.2) \ N c).card ≤ 3)).image
          (fun c => (({c} : Finset (Fin n)), opnd C p.1 (1 - p.2))))
      have hT9card : T9.card ≤ 6 * C.size := by
        have h1 : T9.card ≤ ((Junk ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (side (n := n) C p.1 p.2).card ≤ 3)).card * 3 :=
          Finset.card_biUnion_le_card_mul _ _ 3 (fun p hp => by
            rw [Finset.mem_filter] at hp
            exact Finset.card_image_le.trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans hp.2))
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => (side (n := n) C p.1 p.2).card ≤ 3) (Junk ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E9 := T9.toList.toFinset.biUnion (fun p =>
        p.1.biUnion (fun c => (orIn n C p.2 ∩ N c).image (fun v => s(c, v))))
      refine ⟨E9, ?_, ?_⟩
      · have hcov := or_star_count 1 3 T9.toList (by
          intro q hq
          rw [Finset.mem_toList] at hq
          simp only [T9, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hq
          obtain ⟨⟨g, d⟩, _, c, ⟨_, hc⟩, rfl⟩ := hq
          refine ⟨by simp, ?_⟩
          have hbu1 : ({c} : Finset (Fin n)).biUnion N = N c := by ext w; simp
          rw [hbu1, ← hside_def]; exact hc)
        rw [Finset.length_toList] at hcov
        calc E9.card ≤ 1 * (1 + 3) * (T9.card + C.size) := hcov
          _ ≤ 1 * (1 + 3) * (6 * C.size + C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 28 * C.size := by ring
      · intro g hg d c w hcw h3 hc hex hw
        dsimp only [E9]
        refine Finset.mem_biUnion.mpr ⟨({c}, opnd C g (1 - d)), ?_, ?_⟩
        · rw [List.mem_toFinset, Finset.mem_toList]
          refine Finset.mem_biUnion.mpr ⟨(g, d), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, h3⟩, ?_⟩
          exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hex⟩, rfl⟩
        · refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_singleton_self _, ?_⟩
          exact Finset.mem_image.mpr ⟨w, Finset.mem_inter.mpr ⟨hw, (hMemN c w).mpr hcw⟩, rfl⟩
    obtain ⟨E10, hE10, mE10⟩ : ∃ E10 : Finset (Sym2 (Fin n)), E10.card ≤ 80 * C.size ∧
        ∀ a ∈ Tops, ∀ b : Fin 2, ∀ g h : ℕ, ∀ da db : Fin 2, ∀ x y : Fin n,
          G.Adj x y → IsBottom g → IsBottom h →
          OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
          (side (n := n) C g da).card ≤ 3 → (side (n := n) C h db).card ≤ 3 →
          x ∈ side (n := n) C g da → y ∈ side (n := n) C h db →
          4 ≤ (side (n := n) C g (1 - da) \ N x).card → 4 ≤ (side (n := n) C h (1 - db) \ N y).card → s(x, y) ∈ E10 := by
      have h5x5 : ∀ (U V : Finset (Fin n)) (y x : Fin n → Option (Fin n)),
          (∀ u ∈ U, ∀ v ∈ V, G.Adj u v ∨ y u = some v ∨ x v = some u) →
          U.card ≤ 4 ∨ V.card ≤ 4 := by
        intro U V y x hUV
        by_contra hcon
        simp only [not_or, not_le] at hcon
        obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ U.card)
        obtain ⟨T, hTV, hTcard⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ V.card)
        let E := (S ×ˢ T).filter (fun p => G.Adj p.1 p.2)
        have hEcard : 15 ≤ E.card := by
          let BadY := S.biUnion (fun u => (T.filter (fun v => y u = some v)).image (fun v => (u, v)))
          let BadX := T.biUnion (fun v => (S.filter (fun u => x v = some u)).image (fun u => (u, v)))
          have hsub : (S ×ˢ T) \ E ⊆ BadY ∪ BadX := by
            intro p hp
            rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_product] at hp
            obtain ⟨⟨hpS, hpT⟩, hnot⟩ := hp
            have hna : ¬ G.Adj p.1 p.2 := fun ha => hnot ⟨⟨hpS, hpT⟩, ha⟩
            rcases hUV p.1 (hSU hpS) p.2 (hTV hpT) with ha | hy | hx
            · exact (hna ha).elim
            · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p.1, hpS,
                Finset.mem_image.mpr ⟨p.2, Finset.mem_filter.mpr ⟨hpT, hy⟩, rfl⟩⟩)
            · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p.2, hpT,
                Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨hpS, hx⟩, rfl⟩⟩)
          have hBY : BadY.card ≤ 5 := by
            have h1 : BadY.card ≤ S.card * 1 := Finset.card_biUnion_le_card_mul _ _ 1 (fun u _ => by
              refine Finset.card_image_le.trans ?_
              rw [Finset.card_le_one]
              intro v1 hv1 v2 hv2
              rw [Finset.mem_filter] at hv1 hv2
              exact Option.some.inj (hv1.2.symm.trans hv2.2))
            omega
          have hBX : BadX.card ≤ 5 := by
            have h1 : BadX.card ≤ T.card * 1 := Finset.card_biUnion_le_card_mul _ _ 1 (fun v _ => by
              refine Finset.card_image_le.trans ?_
              rw [Finset.card_le_one]
              intro u1 hu1 u2 hu2
              rw [Finset.mem_filter] at hu1 hu2
              exact Option.some.inj (hu1.2.symm.trans hu2.2))
            omega
          have hpart := Finset.card_sdiff_add_card_eq_card (show E ⊆ S ×ˢ T from Finset.filter_subset _ _)
          have hST : (S ×ˢ T).card = 25 := by rw [Finset.card_product, hScard, hTcard]
          have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
          omega
        let Ch := (S ×ˢ (T ×ˢ T)).filter (fun q => q.2.1 ≠ q.2.2 ∧ G.Adj q.1 q.2.1 ∧ G.Adj q.1 q.2.2)
        have hCh_up : Ch.card ≤ 20 := by
          let Pairs := (T ×ˢ T).filter (fun pp => pp.1 ≠ pp.2)
          have hPairsCard : Pairs.card ≤ 20 := by
            let Diag := T.image (fun v => (v, v))
            have hDiagSub : Diag ⊆ T ×ˢ T := by
              intro pp hpp; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hpp
              exact Finset.mem_product.mpr ⟨hv, hv⟩
            have hDiagCard : Diag.card = 5 := by
              rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), hTcard]
            have hPairsSub : Pairs ⊆ (T ×ˢ T) \ Diag := by
              intro pp hpp; rw [Finset.mem_filter] at hpp
              refine Finset.mem_sdiff.mpr ⟨hpp.1, fun hd => ?_⟩
              obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hd
              have := Prod.mk.inj hv; exact hpp.2 (this.1.symm.trans this.2)
            have hpart := Finset.card_sdiff_add_card_eq_card hDiagSub
            have hTT : (T ×ˢ T).card = 25 := by rw [Finset.card_product, hTcard]
            have hle := Finset.card_le_card hPairsSub
            omega
          have hsub : Ch ⊆ Pairs.biUnion (fun pp =>
              (S.filter (fun u => G.Adj u pp.1 ∧ G.Adj u pp.2)).image (fun u => (u, pp))) := by
            intro q hq; rw [Finset.mem_filter, Finset.mem_product] at hq
            refine Finset.mem_biUnion.mpr ⟨q.2, Finset.mem_filter.mpr ⟨hq.1.2, hq.2.1⟩, ?_⟩
            exact Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr ⟨hq.1.1, hq.2.2⟩, rfl⟩
          have hfib : ∀ pp ∈ Pairs,
              ((S.filter (fun u => G.Adj u pp.1 ∧ G.Adj u pp.2)).image (fun u => (u, pp))).card ≤ 1 := by
            intro pp hpp; rw [Finset.mem_filter] at hpp
            refine Finset.card_image_le.trans ?_
            have hss : S.filter (fun u => G.Adj u pp.1 ∧ G.Adj u pp.2) ⊆ N pp.1 ∩ N pp.2 := by
              intro u hu; rw [Finset.mem_filter] at hu
              rw [Finset.mem_inter, hMemN, hMemN]; exact ⟨hu.2.1.symm, hu.2.2.symm⟩
            exact (Finset.card_le_card hss).trans (hInterN pp.1 pp.2 hpp.2)
          have h1 := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul _ _ 1 hfib)
          omega
        have hCh_lo : 30 ≤ Ch.card := by
          let d : Fin n → ℕ := fun u => (T.filter (fun v => G.Adj u v)).card
          have hSumE : E.card = ∑ u ∈ S, d u := by
            have hEq : E = S.biUnion (fun u => (T.filter (fun v => G.Adj u v)).image (fun v => (u, v))) := by
              ext p; simp only [E, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
              constructor
              · rintro ⟨⟨h1, h2'⟩, ha⟩; exact ⟨p.1, h1, p.2, ⟨h2', ha⟩, rfl⟩
              · rintro ⟨u, hu, v, ⟨hv, ha⟩, rfl⟩; exact ⟨⟨hu, hv⟩, ha⟩
            rw [hEq, Finset.card_biUnion]
            · apply Finset.sum_congr rfl; intro u _
              rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
            · intro u1 _ u2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro p hp1 hp2
              obtain ⟨_, _, hp1⟩ := Finset.mem_image.mp hp1
              obtain ⟨_, _, hp2⟩ := Finset.mem_image.mp hp2
              exact hne ((Prod.mk.inj (hp1.trans hp2.symm)).1)
          have hSumCh : Ch.card = ∑ u ∈ S, (d u * d u - d u) := by
            have hEq : Ch = S.biUnion (fun u =>
                (((T.filter (fun v => G.Adj u v)) ×ˢ (T.filter (fun v => G.Adj u v))).filter
                  (fun pp => pp.1 ≠ pp.2)).image (fun pp => (u, pp))) := by
              ext q; simp only [Ch, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
              constructor
              · rintro ⟨⟨h1, h2', h3⟩, hne, ha1, ha2⟩
                exact ⟨q.1, h1, q.2, ⟨⟨⟨h2', ha1⟩, ⟨h3, ha2⟩⟩, hne⟩, rfl⟩
              · rintro ⟨u, hu, pp, ⟨⟨⟨hp1, ha1⟩, ⟨hp2, ha2⟩⟩, hne⟩, rfl⟩
                exact ⟨⟨hu, hp1, hp2⟩, hne, ha1, ha2⟩
            rw [hEq, Finset.card_biUnion]
            · apply Finset.sum_congr rfl; intro u _
              rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
              let Nu := T.filter (fun v => G.Adj u v)
              let Dg := Nu.image (fun v => (v, v))
              have hDgSub : Dg ⊆ Nu ×ˢ Nu := by
                intro pp hpp; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hpp
                exact Finset.mem_product.mpr ⟨hv, hv⟩
              have hDgCard : Dg.card = d u := by
                rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
              have hF : (Nu ×ˢ Nu).filter (fun pp => pp.1 ≠ pp.2) = (Nu ×ˢ Nu) \ Dg := by
                ext pp; simp only [Finset.mem_filter, Finset.mem_sdiff, Dg, Finset.mem_image]
                constructor
                · rintro ⟨h1, hne⟩; refine ⟨h1, fun h => ?_⟩
                  obtain ⟨v, _, hv⟩ := h
                  have := Prod.mk.inj hv; exact hne (this.1.symm.trans this.2)
                · rintro ⟨h1, hnd⟩
                  refine ⟨h1, fun heq => hnd ⟨pp.1, (Finset.mem_product.mp h1).1, Prod.ext rfl heq⟩⟩
              rw [hF]
              have hpart := Finset.card_sdiff_add_card_eq_card hDgSub
              have hNN : (Nu ×ˢ Nu).card = d u * d u := Finset.card_product _ _
              omega
            · intro u1 _ u2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro q hq1 hq2
              obtain ⟨_, _, hq1⟩ := Finset.mem_image.mp hq1
              obtain ⟨_, _, hq2⟩ := Finset.mem_image.mp hq2
              exact hne ((Prod.mk.inj (hq1.trans hq2.symm)).1)
          have hineq : ∀ m : ℕ, 5 * m ≤ (m * m - m) + 9 := by
            intro m
            have hle : m ≤ m * m := Nat.le_mul_self m
            have hsq : 6 * m ≤ m * m + 9 := by zify; nlinarith [sq_nonneg ((m : ℤ) - 3)]
            omega
          have hsum := Finset.sum_le_sum (s := S) (fun u _ => hineq (d u))
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, hScard, smul_eq_mul,
            ← hSumE, ← hSumCh] at hsum
          omega
        omega
      let Spec : ℕ → Fin 2 → Fin n → Finset (Fin n) := fun g d w =>
        Finset.univ.filter (fun y => (side (n := n) C g (1 - d) \ (N w ∪ N y)).card ≤ 1)
      have hSpecCard : ∀ g d w, 4 ≤ (side (n := n) C g (1 - d) \ N w).card → (Spec g d w).card ≤ 1 := by
        intro g d w hcard
        rw [Finset.card_le_one]
        intro y1 hy1 y2 hy2
        simp only [Spec, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
        have hsub1 : ((side (n := n) C g (1 - d) \ N w) \ N y1).card ≤ 1 := by
          have heq1 : (side (n := n) C g (1 - d) \ N w) \ N y1 = side (n := n) C g (1 - d) \ (N w ∪ N y1) := by
            ext z; simp [not_or, and_assoc]
          rw [heq1]; exact hy1
        have hsub2 : ((side (n := n) C g (1 - d) \ N w) \ N y2).card ≤ 1 := by
          have heq2 : (side (n := n) C g (1 - d) \ N w) \ N y2 = side (n := n) C g (1 - d) \ (N w ∪ N y2) := by
            ext z; simp [not_or, and_assoc]
          rw [heq2]; exact hy2
        exact hUniqueCenter (side (n := n) C g (1 - d) \ N w) 1 (by omega) y1 y2 hsub1 hsub2
      let specOpt : ℕ → Fin 2 → Fin n → Option (Fin n) := fun g d w =>
        if hs : (Spec g d w).Nonempty then some hs.choose else none
      let Good : ℕ → Fin 2 → ℕ → Fin 2 → Fin n → Prop := fun a b g d w =>
        IsBottom g ∧ OrReaches n C (opnd C a b) g ∧ (side (n := n) C g d).card ≤ 3 ∧
          w ∈ side (n := n) C g d ∧ 4 ≤ (side (n := n) C g (1 - d) \ N w).card
      let Uset : ℕ → Fin 2 → Finset (Fin n) := fun a b =>
        Finset.univ.filter (fun w => ∃ g d, Good a b g d w)
      have hGoodDich : ∀ {a : ℕ} (b : Fin 2) {g h : ℕ} {d1 d2 : Fin 2} {w1 w2 : Fin n},
          a ∈ Tops → Good a b g d1 w1 → Good a (1 - b) h d2 w2 →
          G.Adj w1 w2 ∨ w2 ∈ Spec g d1 w1 ∨ specOpt h d2 w2 = some w1 := by
        intro a b g h d1 d2 w1 w2 ha hg1 hh2
        by_cases hadj : G.Adj w1 w2
        · exact Or.inl hadj
        · let X := side C g (1 - d1) \ (N w1 ∪ N w2)
          let Y := side C h (1 - d2) \ (N w1 ∪ N w2)
          have hXY : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y := by
            intro x hx y hy
            simp only [X, Y, Finset.mem_sdiff, Finset.mem_union, hMemN, not_or] at hx hy
            have h4 := hTop4 b ha hg1.1 hh2.1 hg1.2.1 hh2.2.1 w1 x w2 y
              (by fin_cases d1
                  · exact Or.inl hg1.2.2.2.1
                  · exact Or.inr (Or.inl (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hx.1)))
              (by fin_cases d1
                  · exact Or.inr (Or.inl (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hx.1))
                  · exact Or.inl hg1.2.2.2.1)
              (by fin_cases d2
                  · exact Or.inr (Or.inr (Or.inl hh2.2.2.2.1))
                  · exact Or.inr (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hy.1))))
              (by fin_cases d2
                  · exact Or.inr (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hy.1)))
                  · exact Or.inr (Or.inr (Or.inl hh2.2.2.2.1)))
            rcases h4 with h1 | h2' | h3 | h4' | h5 | h6
            · exact (hx.2.1 h1).elim
            · exact (hadj h2').elim
            · exact (hy.2.1 h3).elim
            · exact (hx.2.2 h4'.symm).elim
            · exact h5
            · exact (hy.2.2 h6).elim
          rcases hBiclique X Y hXY with hX | hY
          · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩))
          · right; right
            have hw1Y : w1 ∈ Spec h d2 w2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              simpa [Y, Finset.union_comm] using hY⟩
            have hne : (Spec h d2 w2).Nonempty := ⟨w1, hw1Y⟩
            dsimp only [specOpt]; rw [dif_pos hne]; congr 1
            exact Finset.card_le_one.mp (hSpecCard h d2 w2 hh2.2.2.2.2) _ hne.choose_spec _ hw1Y
      have hUsmall : ∀ a ∈ Tops, (Uset a 0).card ≤ 4 ∨ (Uset a 1).card ≤ 4 := by
        intro a ha
        let y : Fin n → Option (Fin n) := fun u =>
          if hu : ∃ g d, Good a 0 g d u then specOpt hu.choose hu.choose_spec.choose u else none
        let x : Fin n → Option (Fin n) := fun v =>
          if hv : ∃ h d, Good a 1 h d v then specOpt hv.choose hv.choose_spec.choose v else none
        refine h5x5 (Uset a 0) (Uset a 1) y x ?_
        intro u hu v hv
        simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        have hd := hGoodDich 0 (h := hv.choose) (d2 := hv.choose_spec.choose) ha hu.choose_spec.choose_spec
          (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hv.choose_spec.choose_spec)
        rcases hd with ha' | hspec | hopt
        · exact Or.inl ha'
        · right; left
          dsimp only [y]; rw [dif_pos hu]
          have hne : (Spec hu.choose hu.choose_spec.choose u).Nonempty := ⟨v, hspec⟩
          dsimp only [specOpt]; rw [dif_pos hne]; congr 1
          exact Finset.card_le_one.mp
            (hSpecCard _ _ _ hu.choose_spec.choose_spec.2.2.2.2) _ hne.choose_spec _ hspec
        · right; right; dsimp only [x]; rw [dif_pos hv]; exact hopt
      let L10 : Fin 2 → ℕ → Finset (Fin n) := fun d0 h =>
        if IsBottom h ∧ (side (n := n) C h d0).card ≤ 3
        then (side (n := n) C h d0).filter (fun w => 4 ≤ (side (n := n) C h (1 - d0) \ N w).card)
        else ∅
      let T10 := ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (Uset p.1 p.2).card ≤ 4)).biUnion
        (fun p => (Uset p.1 p.2).image (fun u =>
          if hu : ∃ g d, Good p.1 p.2 g d u
          then (u, opnd C p.1 (1 - p.2), Spec hu.choose hu.choose_spec.choose u)
          else (u, opnd C p.1 (1 - p.2), ∅)))
      have hT10card : T10.card ≤ 8 * C.size := by
        have h1 : T10.card ≤ ((Tops ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun p => (Uset p.1 p.2).card ≤ 4)).card * 4 :=
          Finset.card_biUnion_le_card_mul _ _ 4 (fun p hp => by
            rw [Finset.mem_filter] at hp
            exact Finset.card_image_le.trans hp.2)
        have h2' := Finset.card_le_card (Finset.filter_subset (fun p : ℕ × Fin 2 => (Uset p.1 p.2).card ≤ 4) (Tops ×ˢ (Finset.univ : Finset (Fin 2))))
        omega
      let E10d : Fin 2 → Finset (Sym2 (Fin n)) := fun d0 =>
        T10.toList.toFinset.biUnion (fun t =>
          ((Finset.range C.gates.length).filter (fun g => (gateAt C g).op ≠ GateOp.or ∧ OrReaches n C t.2.1 g)).biUnion
            (fun g => ((L10 d0 g).filter (fun v => G.Adj t.1 v)).image (fun v => s(t.1, v))))
      have hE10d : ∀ d0 : Fin 2, (E10d d0).card ≤ 40 * C.size := by
        intro d0
        have hL10 : ∀ g, (L10 d0 g).card ≤ 3 := by
          intro g; dsimp only [L10]; split_ifs with h
          · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans h.2
          · simp
        have hcov := two_visit_star_count 3 1 (L10 d0) (fun h w => specOpt h d0 w) T10.toList hL10 (by
          intro t ht
          rw [Finset.mem_toList] at ht
          simp only [T10, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            and_true, Finset.mem_image] at ht
          obtain ⟨⟨a, b⟩, ⟨ha, _⟩, u, hu, rfl⟩ := ht
          have hu' : ∃ g d, Good a b g d u := by
            simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and] at hu; exact hu
          rw [dif_pos hu']
          refine ⟨hSpecCard _ _ _ hu'.choose_spec.choose_spec.2.2.2.2, ?_⟩
          intro h _ _ hrh v hv
          dsimp only [L10] at hv
          split_ifs at hv with hbot
          · rw [Finset.mem_filter] at hv
            exact hGoodDich b ha hu'.choose_spec.choose_spec ⟨hbot.1, hrh, hbot.2, hv.1, hv.2⟩
          · simp at hv)
        rw [Finset.length_toList] at hcov
        have : max 3 (2 + 2 * 1) = 4 := by decide
        rw [this] at hcov
        calc (E10d d0).card ≤ 4 * (T10.card + 2 * C.size) := hcov
          _ ≤ 4 * (8 * C.size + 2 * C.size) := Nat.mul_le_mul_left _ (by omega)
          _ = 40 * C.size := by ring
      refine ⟨E10d 0 ∪ E10d 1, ?_, ?_⟩
      · have hu := Finset.card_union_le (E10d 0) (E10d 1)
        have c0 := hE10d 0; have c1 := hE10d 1; omega
      · intro a ha b g h da db x y hxy hgb hhb hrg hrh hda hdb hx1 hy2 hgx hhy
        have hGoodG : Good a b g da x := ⟨hgb, hrg, hda, hx1, hgx⟩
        have hGoodH : Good a (1 - b) h db y := ⟨hhb, hrh, hdb, hy2, hhy⟩
        have hU_or : (Uset a b).card ≤ 4 ∨ (Uset a (1 - b)).card ≤ 4 := by
          rcases hUsmall a ha with h0 | h1
          · fin_cases b
            · exact Or.inl h0
            · exact Or.inr (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using h0)
          · fin_cases b
            · exact Or.inr (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using h1)
            · exact Or.inl h1
        have hE10_of : ∀ (b' : Fin 2) (h' : ℕ) (d0 : Fin 2) (c w : Fin n),
            G.Adj c w → (Uset a b').card ≤ 4 →
            (∃ g' d', Good a b' g' d' c) → Good a (1 - b') h' d0 w → s(c, w) ∈ E10d 0 ∪ E10d 1 := by
          intro b' h' d0 c w hcw hU4 hcG hwG
          have hmem10d : s(c, w) ∈ E10d d0 := by
            dsimp only [E10d]
            refine Finset.mem_biUnion.mpr
              ⟨(c, opnd C a (1 - b'), Spec hcG.choose hcG.choose_spec.choose c), ?_, ?_⟩
            · rw [List.mem_toFinset, Finset.mem_toList]
              refine Finset.mem_biUnion.mpr ⟨(a, b'), Finset.mem_filter.mpr
                ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, hU4⟩, ?_⟩
              refine Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcG⟩, ?_⟩
              rw [dif_pos hcG]
            · obtain ⟨hhlen, hhnor⟩ := hgate_len hwG.1.1
              refine Finset.mem_biUnion.mpr ⟨h', Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hhlen, hhnor, hwG.2.1⟩, ?_⟩
              refine Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨?_, hcw⟩, rfl⟩
              dsimp only [L10]; rw [if_pos ⟨hwG.1, hwG.2.2.1⟩]
              exact Finset.mem_filter.mpr ⟨hwG.2.2.2.1, hwG.2.2.2.2⟩
          fin_cases d0
          · exact Finset.mem_union_left _ hmem10d
          · exact Finset.mem_union_right _ hmem10d
        rcases hU_or with hUb | hU1b
        · exact hE10_of b h db x y hxy hUb ⟨g, da, hGoodG⟩ hGoodH
        · have hsubb : (1 : Fin 2) - (1 - b) = b := by fin_cases b <;> decide
          rw [Sym2.eq_swap]
          exact hE10_of (1 - b) g da y x hxy.symm hU1b ⟨h, db, hGoodH⟩ (hsubb.symm ▸ hGoodG)
    let Eall := E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ E6 ∪ E7 ∪ E8 ∪ E9 ∪ E10
    have hEall : Eall.card ≤ 204 * C.size := by
      have u9 := Finset.card_union_le (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ E6 ∪ E7 ∪ E8 ∪ E9) E10
      have u8 := Finset.card_union_le (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ E6 ∪ E7 ∪ E8) E9
      have u7 := Finset.card_union_le (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ E6 ∪ E7) E8
      have u6 := Finset.card_union_le (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ E6) E7
      have u5 := Finset.card_union_le (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5) E6
      have u4 := Finset.card_union_le (E1 ∪ E2 ∪ E3 ∪ E4) E5
      have u3 := Finset.card_union_le (E1 ∪ E2 ∪ E3) E4
      have u2 := Finset.card_union_le (E1 ∪ E2) E3
      have u1 := Finset.card_union_le E1 E2
      dsimp only [Eall]; omega
    refine ⟨Eall, hEall, ?_⟩
    · intro e heU he
      obtain ⟨u, v, rfl, a, ha, g1, hg1j, g2, hg2j, _, hrg1, hrg2, hvg1, hvg2, hbot1, hbot2⟩ := he
      rw [← hTopsEq] at ha
      rw [← hJunkEq] at hg1j hg2j hbot1 hbot2
      have hadj : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeFinset] using (Finset.mem_sdiff.mp heU).1
      have hgb1 : IsBottom g1 := ⟨hg1j, hbot1⟩
      have hgb2 : IsBottom g2 := ⟨hg2j, hbot2⟩
      have in1 : ∀ {x}, x ∈ E1 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))))))))
      have in2 : ∀ {x}, x ∈ E2 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))))))))
      have in3 : ∀ {x}, x ∈ E3 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ h)))))))
      have in4 : ∀ {x}, x ∈ E4 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ h))))))
      have in5 : ∀ {x}, x ∈ E5 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))))
      have in6 : ∀ {x}, x ∈ E6 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
      have in7 : ∀ {x}, x ∈ E7 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ h)))
      have in8 : ∀ {x}, x ∈ E8 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have in9 : ∀ {x}, x ∈ E9 → x ∈ Eall := fun h =>
        Finset.mem_union_left _ (Finset.mem_union_right _ h)
      have in10 : ∀ {x}, x ∈ E10 → x ∈ Eall := fun h => Finset.mem_union_right _ h
      have hcaseI : ∀ (b : Fin 2) (g h : ℕ) (x y : Fin n),
          s(u, v) = s(x, y) → G.Adj x y → IsBottom g → IsBottom h →
          OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
          x ∈ S1 g → y ∈ S1 h → s(u, v) ∈ Eall := by
        intro b g h x y hs hxy hgb hhb hrg hrh hx hy
        have hLadj : ∀ w1 ∈ L a b, ∀ w2 ∈ L a (1 - b), G.Adj w1 w2 := by
          intro w1 hw1 w2 hw2
          simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
          obtain ⟨g', hg', hrg', hw1'⟩ := hw1
          obtain ⟨h', hh', hrh', hw2'⟩ := hw2
          simp only [S1, Finset.mem_inter] at hw1' hw2'
          exact hTop2 b ha hg' hh' hrg' hrh' w1 w2 (Or.inl hw1'.1) (Or.inl hw1'.2) (Or.inr hw2'.1) (Or.inr hw2'.2)
        have hI_dir : ∀ (b' : Fin 2) (g' h' : ℕ) (c w : Fin n),
            s(u, v) = s(c, w) → G.Adj c w → IsBottom g' → IsBottom h' →
            OrReaches n C (opnd C a b') g' → OrReaches n C (opnd C a (1 - b')) h' →
            c ∈ S1 g' → w ∈ S1 h' → (L a b').card = 1 → s(u, v) ∈ Eall := by
          intro b' g' h' c w hs' hcw hgb' hhb' hrg' hrh' hc' hw' hcard1
          by_cases hs1 : (S1 h').card ≤ 3
          · rw [hs']; exact in1 (mE1 a ha b' g' h' c w hcw hgb' hhb' hrg' hrh' hc' hw' hcard1 hs1)
          · have hbig : 4 ≤ (S1 h').card := by omega
            have hAB : ∀ p ∈ side C h' 0 \ N c, ∀ q ∈ side C h' 1 \ N c, G.Adj p q := by
              intro p hp q hq
              rw [Finset.mem_sdiff, hMemN] at hp hq
              simp only [S1, Finset.mem_inter] at hc'
              rcases hTop3 b' ha hgb' hhb' hrg' hrh' c p q
                (Or.inl hc'.1) (Or.inl hc'.2) (Or.inr (Or.inl hp.1)) (Or.inr (Or.inr hq.1)) with h1 | h2' | h3
              · exact (hp.2 h1).elim
              · exact (hq.2 h2').elim
              · exact h3
            obtain ⟨d, hd⟩ : ∃ d : Fin 2, (side C h' d \ N c).card ≤ 1 := by
              rcases hBiclique _ _ hAB with h0 | h1
              · exact ⟨0, h0⟩
              · exact ⟨1, h1⟩
            have hbigd : 4 ≤ (side (n := n) C h' d).card := hbig.trans (Finset.card_le_card (by
              fin_cases d; exact Finset.inter_subset_left; exact Finset.inter_subset_right))
            have hwd : w ∈ side C h' d := by
              fin_cases d; exact (Finset.mem_inter.mp hw').1; exact (Finset.mem_inter.mp hw').2
            rw [hs']; exact in2 (mE2 h' hhb'.1 d c w hcw hbigd hd hwd)
        have hxL : x ∈ L a b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hgb, hrg, hx⟩
        have hyL : y ∈ L a (1 - b) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hhb, hrh, hy⟩
        rcases hBiclique (L a b) (L a (1 - b)) hLadj with h0 | h1
        · have := Finset.card_pos.mpr ⟨x, hxL⟩
          exact hI_dir b g h x y hs hxy hgb hhb hrg hrh hx hy (by omega)
        · have := Finset.card_pos.mpr ⟨y, hyL⟩
          have hsubb : (1 : Fin 2) - (1 - b) = b := by fin_cases b <;> decide
          exact hI_dir (1 - b) h g y x (hs.trans Sym2.eq_swap) hxy.symm hhb hgb hrh (hsubb.symm ▸ hrg) hy hx (by omega)
      have hcaseII : ∀ (b : Fin 2) (g h : ℕ) (d : Fin 2) (x y : Fin n),
          s(u, v) = s(x, y) → G.Adj x y → IsBottom g → IsBottom h →
          OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
          x ∈ S1 g → x ∈ side C h d → y ∈ side C h (1 - d) → s(u, v) ∈ Eall := by
        intro b g h d x y hs hxy hgb hhb hrg hrh hxg hxd hyd
        have hQsub : side C h (1 - d) ⊆ N x := by
          intro w hw; rw [hMemN]
          simp only [S1, Finset.mem_inter] at hxg
          fin_cases d
          · exact hTop2 b ha hgb hhb hrg hrh x w (Or.inl hxg.1) (Or.inl hxg.2) (Or.inl hxd)
              (Or.inr (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hw))
          · exact hTop2 b ha hgb hhb hrg hrh x w (Or.inl hxg.1) (Or.inl hxg.2)
              (Or.inr (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hw)) (Or.inl hxd)
        by_cases hQ2 : 2 ≤ (side (n := n) C h (1 - d)).card
        · rw [hs]; exact in3 (mE3 h hhb.1 (1 - d) x y hxy hQ2 hQsub hyd)
        · have hQ1 : (side (n := n) C h (1 - d)).card = 1 := by have := Finset.card_pos.mpr ⟨y, hyd⟩; omega
          by_cases hP1 : (side C h d \ N y).card ≤ 1
          · rw [hs, Sym2.eq_swap]; exact in4 (mE4 h hhb.1 d y x hxy.symm hQ1 hyd hP1 hxd)
          · have hP2 : 2 ≤ (side C h d \ N y).card := by omega
            by_cases hL3 : (L a b).card ≤ 3
            · rw [hs]; exact in5 (mE5 a ha b g h d x y hxy hgb hhb hrg hrh hxg hL3 hQ1 hyd hP2)
            · have hL4 : 4 ≤ (L a b).card := by omega
              obtain ⟨z1, hz1, z2, hz2, hzne⟩ := Finset.one_lt_card.mp (by omega : 1 < (side C h d \ N y).card)
              have hLexc : (L a b \ N y).card ≤ 1 := by
                have hsub : L a b \ N y ⊆ N z1 ∩ N z2 := by
                  intro w hw
                  rw [Finset.mem_sdiff, hMemN] at hw
                  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hw
                  obtain ⟨g', hg', hrg', hwg'⟩ := hw.1
                  simp only [S1, Finset.mem_inter] at hwg'
                  have eachz : ∀ z ∈ side C h d \ N y, G.Adj z w := by
                    intro z hz; rw [Finset.mem_sdiff, hMemN] at hz
                    have ht3 : G.Adj w z ∨ G.Adj w y ∨ G.Adj z y := by
                      fin_cases d
                      · exact hTop3 b ha hg' hhb hrg' hrh w z y (Or.inl hwg'.1) (Or.inl hwg'.2)
                          (Or.inr (Or.inl hz.1)) (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hyd)))
                      · exact hTop3 b ha hg' hhb hrg' hrh w z y (Or.inl hwg'.1) (Or.inl hwg'.2)
                          (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hyd))) (Or.inr (Or.inl hz.1))
                    rcases ht3 with h1 | h2'' | h3
                    · exact h1.symm
                    · exact (hw.2 h2''.symm).elim
                    · exact (hz.2 h3.symm).elim
                  rw [Finset.mem_inter, hMemN, hMemN]
                  exact ⟨eachz z1 hz1, eachz z2 hz2⟩
                exact (Finset.card_le_card hsub).trans (hInterN z1 z2 hzne)
              by_cases hS1g : (S1 g).card ≤ 3
              · rw [hs, Sym2.eq_swap]; exact in6 (mE6 a ha b g x y hxy.symm hgb hrg hxg hS1g hL4 hLexc)
              · have hS1g4 : 4 ≤ (S1 g).card := by omega
                have hS1exc : (S1 g \ N y).card ≤ 1 :=
                  (Finset.card_le_card (Finset.sdiff_subset_sdiff
                    (fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hgb, hrg, hw⟩)
                    (Finset.Subset.refl _))).trans hLexc
                have hz1' := hz1; rw [Finset.mem_sdiff, hMemN] at hz1'
                have hAB : ∀ p ∈ side C g 0 \ (N y ∪ N z1), ∀ q ∈ side C g 1 \ (N y ∪ N z1), G.Adj p q := by
                  intro p hp q hq
                  simp only [Finset.mem_sdiff, Finset.mem_union, hMemN, not_or] at hp hq
                  have h4 := hTop4 b ha hgb hhb hrg hrh p q z1 y
                    (Or.inl hp.1) (Or.inr (Or.inl hq.1))
                    (by fin_cases d
                        · exact Or.inr (Or.inr (Or.inl hz1'.1))
                        · exact Or.inr (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hyd))))
                    (by fin_cases d
                        · exact Or.inr (Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hyd)))
                        · exact Or.inr (Or.inr (Or.inl hz1'.1)))
                  rcases h4 with h1 | h2'' | h3 | h4' | h5 | h6
                  · exact h1
                  · exact (hp.2.2 h2''.symm).elim
                  · exact (hp.2.1 h3.symm).elim
                  · exact (hq.2.2 h4'.symm).elim
                  · exact (hq.2.1 h5.symm).elim
                  · exact (hz1'.2 h6.symm).elim
                have hex7 : ∃ (d' : Fin 2) (z : Fin n), (side C g d' \ (N y ∪ N z)).card ≤ 1 := by
                  rcases hBiclique _ _ hAB with h0 | h1
                  · exact ⟨0, z1, h0⟩
                  · exact ⟨1, z1, h1⟩
                rw [hs, Sym2.eq_swap]; exact in7 (mE7 g hgb.1 x y hxy.symm hxg hS1g4 hS1exc hex7)
      have hcaseIII : ∀ (d1 d2 : Fin 2),
          u ∈ side C g1 d1 → v ∈ side C g1 (1 - d1) →
          u ∈ side C g2 d2 → v ∈ side C g2 (1 - d2) → s(u, v) ∈ Eall := by
        intro d1 d2 hu1 hv1 hu2 hv2
        have hB12 : (side C g1 (1 - d1) \ N u).card ≤ 1 ∨ (side C g2 (1 - d2) \ N u).card ≤ 1 := by
          refine hBiclique _ _ (fun b1 hb1 b2 hb2 => ?_)
          rw [Finset.mem_sdiff, hMemN] at hb1 hb2
          have ht3 := hTop3 0 ha hgb1 hgb2 hrg1
            (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hrg2) u b1 b2
            (by fin_cases d1
                · exact Or.inl hu1
                · exact Or.inr (Or.inl (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hb1.1)))
            (by fin_cases d1
                · exact Or.inr (Or.inl (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hb1.1))
                · exact Or.inl hu1)
            (by fin_cases d2
                · exact Or.inl hu2
                · exact Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hb2.1)))
            (by fin_cases d2
                · exact Or.inr (Or.inr (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hb2.1))
                · exact Or.inl hu2)
          rcases ht3 with h1 | h2' | h3
          · exact (hb1.2 h1).elim
          · exact (hb2.2 h2').elim
          · exact h3
        have hA12 : (side C g1 d1 \ N v).card ≤ 1 ∨ (side C g2 d2 \ N v).card ≤ 1 := by
          refine hBiclique _ _ (fun a1 ha1 a2 ha2 => ?_)
          rw [Finset.mem_sdiff, hMemN] at ha1 ha2
          have ht3 := hTop3 0 ha hgb1 hgb2 hrg1
            (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hrg2) v a1 a2
            (by fin_cases d1
                · exact Or.inr (Or.inl ha1.1)
                · exact Or.inl (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hv1))
            (by fin_cases d1
                · exact Or.inl (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hv1)
                · exact Or.inr (Or.inl ha1.1))
            (by fin_cases d2
                · exact Or.inr (Or.inr ha2.1)
                · exact Or.inl (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hv2))
            (by fin_cases d2
                · exact Or.inl (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hv2)
                · exact Or.inr (Or.inr ha2.1))
          rcases ht3 with h1 | h2' | h3
          · exact (ha1.2 h1).elim
          · exact (ha2.2 h2').elim
          · exact h3
        have hIII3 : ∀ (b : Fin 2) (g h : ℕ) (da db : Fin 2) (x y : Fin n),
            s(u, v) = s(x, y) → G.Adj x y → IsBottom g → IsBottom h →
            OrReaches n C (opnd C a b) g → OrReaches n C (opnd C a (1 - b)) h →
            (side (n := n) C g da).card ≤ 3 → (side (n := n) C h db).card ≤ 3 →
            x ∈ side C g da → y ∈ side C g (1 - da) →
            y ∈ side C h db → x ∈ side C h (1 - db) → s(u, v) ∈ Eall := by
          intro b g h da db x y hs hxy hgb hhb hrg hrh hda hdb hx1 hy1 hy2 hx2
          by_cases hgx : (side C g (1 - da) \ N x).card ≤ 3
          · rw [hs]; exact in9 (mE9 g hgb.1 da x y hxy hda hx1 hgx hy1)
          · by_cases hhy : (side C h (1 - db) \ N y).card ≤ 3
            · rw [hs, Sym2.eq_swap]; exact in9 (mE9 h hhb.1 db y x hxy.symm hdb hy2 hhy hx2)
            · rw [hs]; exact in10 (mE10 a ha b g h da db x y hxy hgb hhb hrg hrh hda hdb hx1 hy2 (by omega) (by omega))
        by_cases hc1 : 4 ≤ (side (n := n) C g1 (1 - d1)).card ∧ (side C g1 (1 - d1) \ N u).card ≤ 1
        · exact in2 (mE2 g1 hg1j (1 - d1) u v hadj hc1.1 hc1.2 hv1)
        · by_cases hc2 : 4 ≤ (side (n := n) C g2 (1 - d2)).card ∧ (side C g2 (1 - d2) \ N u).card ≤ 1
          · exact in2 (mE2 g2 hg2j (1 - d2) u v hadj hc2.1 hc2.2 hv2)
          · by_cases hc3 : 4 ≤ (side (n := n) C g1 d1).card ∧ (side C g1 d1 \ N v).card ≤ 1
            · rw [Sym2.eq_swap]; exact in2 (mE2 g1 hg1j d1 v u hadj.symm hc3.1 hc3.2 hu1)
            · by_cases hc4 : 4 ≤ (side (n := n) C g2 d2).card ∧ (side C g2 d2 \ N v).card ≤ 1
              · rw [Sym2.eq_swap]; exact in2 (mE2 g2 hg2j d2 v u hadj.symm hc4.1 hc4.2 hu2)
              · have hBs : (side (n := n) C g1 (1 - d1)).card ≤ 3 ∨ (side (n := n) C g2 (1 - d2)).card ≤ 3 := by
                  rcases hB12 with h1 | h2'
                  · left; by_contra hcon; exact hc1 ⟨by omega, h1⟩
                  · right; by_contra hcon; exact hc2 ⟨by omega, h2'⟩
                have hAs : (side (n := n) C g1 d1).card ≤ 3 ∨ (side (n := n) C g2 d2).card ≤ 3 := by
                  rcases hA12 with h1 | h2'
                  · left; by_contra hcon; exact hc3 ⟨by omega, h1⟩
                  · right; by_contra hcon; exact hc4 ⟨by omega, h2'⟩
                rcases hAs with hA1 | hA2 <;> rcases hBs with hB1 | hB2
                · exact in8 (mE8 g1 hg1j d1 u v hA1 hB1 hu1 hv1)
                · exact hIII3 0 g1 g2 d1 (1 - d2) u v rfl hadj hgb1 hgb2 hrg1
                    (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hrg2) hA1 hB2 hu1 hv1 hv2
                    (by simpa [show (1 : Fin 2) - (1 - d2) = d2 by fin_cases d2 <;> decide] using hu2)
                · exact hIII3 1 g2 g1 d2 (1 - d1) u v rfl hadj hgb2 hgb1 hrg2
                    (by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hrg1) hA2 hB1 hu2 hv2 hv1
                    (by simpa [show (1 : Fin 2) - (1 - d1) = d1 by fin_cases d1 <;> decide] using hu1)
                · exact in8 (mE8 g2 hg2j d2 u v hA2 hB2 hu2 hv2)
      have hsplit : ∀ {g : ℕ}, IsBottom g → gateVal n C g (pairInput u v) = true →
          u ∈ S1 g ∨ v ∈ S1 g ∨ ∃ d : Fin 2, u ∈ side C g d ∧ v ∈ side C g (1 - d) := by
        intro g hg hvg
        obtain ⟨⟨w0, hw0, hxw0⟩, ⟨w1, hw1, hxw1⟩⟩ := (bottom_eval hg (pairInput u v)).mp hvg
        rw [hpair_def, decide_eq_true_eq] at hxw0 hxw1
        rcases hxw0 with rfl | rfl <;> rcases hxw1 with rfl | rfl
        · exact Or.inl (Finset.mem_inter.mpr ⟨hw0, hw1⟩)
        · exact Or.inr (Or.inr ⟨0, hw0, by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hw1⟩)
        · exact Or.inr (Or.inr ⟨1, hw1, by simpa [show (1 : Fin 2) - 1 = 0 by decide] using hw0⟩)
        · exact Or.inr (Or.inl (Finset.mem_inter.mpr ⟨hw0, hw1⟩))
      have hno_same : ∀ w : Fin n, w ∈ S1 g1 → w ∈ S1 g2 → False := by
        intro w hw1 hw2
        simp only [S1, Finset.mem_inter] at hw1 hw2
        exact G.irrefl (hTop2 0 ha hgb1 hgb2 hrg1
          (by simpa [show (1 : Fin 2) - 0 = 1 by decide] using hrg2) w w
          (Or.inl hw1.1) (Or.inl hw1.2) (Or.inl hw2.1) (Or.inl hw2.2))
      have hrg2' : OrReaches n C (opnd C a (1 - 0)) g2 := by
        simpa [show (1 : Fin 2) - 0 = 1 by decide] using hrg2
      have hrg1' : OrReaches n C (opnd C a (1 - 1)) g1 := by
        simpa [show (1 : Fin 2) - 1 = 0 by decide] using hrg1
      rcases hsplit hgb1 hvg1 with hu1 | hv1 | ⟨d1, hu1, hv1⟩ <;>
        rcases hsplit hgb2 hvg2 with hu2 | hv2 | ⟨d2, hu2, hv2⟩
      · exact (hno_same u hu1 hu2).elim
      · exact hcaseI 0 g1 g2 u v rfl hadj hgb1 hgb2 hrg1 hrg2' hu1 hv2
      · exact hcaseII 0 g1 g2 d2 u v rfl hadj hgb1 hgb2 hrg1 hrg2' hu1 hu2 hv2
      · exact hcaseI 0 g1 g2 v u Sym2.eq_swap hadj.symm hgb1 hgb2 hrg1 hrg2' hv1 hu2
      · exact (hno_same v hv1 hv2).elim
      · exact hcaseII 0 g1 g2 (1 - d2) v u Sym2.eq_swap hadj.symm hgb1 hgb2 hrg1 hrg2' hv1 hv2
          (by simpa [show (1 : Fin 2) - (1 - d2) = d2 by fin_cases d2 <;> decide] using hu2)
      · exact hcaseII 1 g2 g1 d1 u v rfl hadj hgb2 hgb1 hrg2 hrg1' hu2 hu1 hv1
      · exact hcaseII 1 g2 g1 (1 - d1) v u Sym2.eq_swap hadj.symm hgb2 hgb1 hrg2 hrg1' hv2 hv1
          (by simpa [show (1 : Fin 2) - (1 - d1) = d1 by fin_cases d1 <;> decide] using hu1)
      · exact hcaseIII d1 d2 hu1 hv1 hu2 hv2
  obtain ⟨k1, hk1⟩ := bottomDeep
  obtain ⟨k2, hk2⟩ := deepDeep
  refine ⟨204 + k1 + k2, ?_⟩
  intro n G _ C hG5 hL hT
  obtain ⟨EBB, hBB, mBB⟩ := bottomBottom n G C hG5 hL hT
  obtain ⟨EBD, hBD, mBD⟩ := hk1 n G C hG5 hL hT
  obtain ⟨EDD, hDD, mDD⟩ := hk2 n G C hG5 hL hT
  have hU1 := Finset.card_union_le (EBB ∪ EBD) EDD
  have hU2 := Finset.card_union_le EBB EBD
  have hBB' : EBB.card ≤ 204 * (C.size + 1) := hBB.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  calc _ ≤ (EBB ∪ EBD ∪ EDD).card := Finset.card_le_card (by
          intro e he
          rw [Finset.mem_filter] at he
          obtain ⟨heU, hns, u, v, rfl, a, ha, g1, hg1, g2, hg2, hne, hr1, hr2, hv1, hv2⟩ := he
          by_cases hd1 : ∃ j ∈ junk G C, InCone n C j g1
          · by_cases hd2 : ∃ j ∈ junk G C, InCone n C j g2
            · exact Finset.mem_union_right _
                (mDD s(u, v) heU hns ⟨u, v, rfl, a, ha, g1, hg1, g2, hg2, hne, hr1, hr2, hv1, hv2, hd1, hd2⟩)
            · refine Finset.mem_union_left _ (Finset.mem_union_right _
                (mBD s(u, v) heU hns ⟨u, v, rfl, a, ha, 1, g2, hg2, g1, hg1, hne.symm, hr2, ?_, hv2, hv1,
                  fun j hj hc => hd2 ⟨j, hj, hc⟩, hd1⟩))
              simpa [show (1 : Fin 2) - 1 = 0 by decide] using hr1
          · by_cases hd2 : ∃ j ∈ junk G C, InCone n C j g2
            · refine Finset.mem_union_left _ (Finset.mem_union_right _
                (mBD s(u, v) heU hns ⟨u, v, rfl, a, ha, 0, g1, hg1, g2, hg2, hne, hr1, ?_, hv1, hv2,
                  fun j hj hc => hd1 ⟨j, hj, hc⟩, hd2⟩))
              simpa [show (1 : Fin 2) - 0 = 1 by decide] using hr2
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (mBB s(u, v) heU ⟨u, v, rfl, a, ha, g1, hg1, g2, hg2, hne, hr1, hr2, hv1, hv2,
                  fun j hj hc => hd1 ⟨j, hj, hc⟩, fun j hj hc => hd2 ⟨j, hj, hc⟩⟩)))
    _ ≤ EBB.card + EBD.card + EDD.card := by omega
    _ ≤ 204 * (C.size + 1) + k1 * (C.size + 1) + k2 * (C.size + 1) := by omega
    _ = (204 + k1 + k2) * (C.size + 1) := by ring
