import PEqualNP.MetaComplexity.Helpers.EdgeFnGraphPlan

/-!
# The five semantic conditions at a run of four

`r4Run G q0 q1 q2 q3 q4 q5`: four distinct inner vertices `q1 .. q4`, each with exactly its two
run neighbours, and outer vertices `q0`, `q5` off the inner four. `q0 = q5` is allowed (the
5-cycle through `q0`), and nothing is said about the neighbours of `q0`, `q5`.

`r4_stmtG3` is the analog of `stmtG3` (`EdgeFnGraphPlan.lean`): the conditions `DeepHyp` hold for
`F G A` on `{q1, q2, q3, q4}`. The proof is the proof of `stmtG3`; only the pair funnel step at
the pair `(q1, q4)` changes: `stmtG3` used the witness `q0` there, which needs `q0 ≠ q5`; here the
witnesses are the inner neighbours `q2` (of `q1`) and `q3` (of `q4`).
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

/-- A run of four: inner vertices `q1 .. q4` pairwise distinct with exactly their run neighbours;
outer vertices `q0`, `q5` not inner (`q0 = q5` allowed). -/
structure r4Run {n : ℕ} (G : SimpleGraph (Fin n)) (q0 q1 q2 q3 q4 q5 : Fin n) : Prop where
  nd : [q1, q2, q3, q4].Nodup
  out0 : q0 ∉ [q1, q2, q3, q4]
  out5 : q5 ∉ [q1, q2, q3, q4]
  h1 : ∀ w, G.Adj q1 w ↔ w = q0 ∨ w = q2
  h2 : ∀ w, G.Adj q2 w ↔ w = q1 ∨ w = q3
  h3 : ∀ w, G.Adj q3 w ↔ w = q2 ∨ w = q4
  h4 : ∀ w, G.Adj q4 w ↔ w = q3 ∨ w = q5

theorem r4_stmtG3 : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (A : Finset (Fin (n + 1)))
    (q0 q1 q2 q3 q4 q5 : Fin (n + 1)), AFree G A → r4Run G q0 q1 q2 q3 q4 q5 →
    DeepHyp (F G A) {q1, q2, q3, q4} ∧ 2 ≤ ({q1, q2, q3, q4} : Finset (Fin (n + 1))).card := by
  intro n G A a' a s t b b' hinv hr
  have nd := hr.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := nd
  have o0 := hr.out0
  have o5 := hr.out5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o0 o5
  obtain ⟨h01, h02, h03, h04⟩ := o0
  obtain ⟨h51, h52, h53, h54⟩ := o5
  have h15 : a ≠ b' := Ne.symm h51
  have h25 : s ≠ b' := Ne.symm h52
  have h35 : t ≠ b' := Ne.symm h53
  have h45 : b ≠ b' := Ne.symm h54
  have haa' : G.Adj a a' := (hr.h1 a').2 (Or.inl rfl)
  have has : G.Adj a s := (hr.h1 s).2 (Or.inr rfl)
  have hsa : G.Adj s a := (hr.h2 a).2 (Or.inl rfl)
  have hst : G.Adj s t := (hr.h2 t).2 (Or.inr rfl)
  have hts : G.Adj t s := (hr.h3 s).2 (Or.inl rfl)
  have htb : G.Adj t b := (hr.h3 b).2 (Or.inr rfl)
  have hbt : G.Adj b t := (hr.h4 t).2 (Or.inl rfl)
  have hbb' : G.Adj b b' := (hr.h4 b').2 (Or.inr rfl)
  have ha1 : ∀ w, G.Adj a w → w = a' ∨ w = s := fun w h => (hr.h1 w).1 h
  have hs1 : ∀ w, G.Adj s w → w = a ∨ w = t := fun w h => (hr.h2 w).1 h
  have ht1 : ∀ w, G.Adj t w → w = s ∨ w = b := fun w h => (hr.h3 w).1 h
  have hb1 : ∀ w, G.Adj b w → w = t ∨ w = b' := fun w h => (hr.h4 w).1 h
  have mem : ∀ w, w = a ∨ w = s ∨ w = t ∨ w = b → w ∈ ({a, s, t, b} : Finset (Fin (n + 1))) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hw
  refine ⟨⟨?_, ?_, ?_, ?_, F_zero G A⟩, ?_⟩
  · intro y hy bv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h <;> rw [h]
    · exact nc_of hinv hst (Ne.symm h12) (Ne.symm h13) has bv
    · exact nc_of hinv htb (Ne.symm h23) (Ne.symm h24) hst bv
    · exact nc_of hinv has h13 h23 hts bv
    · exact nc_of hinv has h14 h24 hbt bv
  · intro y hy y' hy' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
    rcases hy with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> rw [h, h'] at hne ⊢
    · exact absurd rfl hne
    · exact nf_of hinv hne haa' h02 hs1 h01 h03 hst (Ne.symm h13)
    · exact nf_of hinv hne haa' h03 ht1 h02 h04 htb (Ne.symm h14)
    · exact nf_of hinv hne has h24 hb1 h23 h25 hbt (Ne.symm h13)
    · exact nf_of hinv hne hst (Ne.symm h13) ha1 (Ne.symm h03) (Ne.symm h23) haa' h02
    · exact absurd rfl hne
    · exact nf_of hinv hne hsa h13 ht1 h12 h14 htb (Ne.symm h24)
    · exact nf_of hinv hne hsa h14 hb1 h13 h15 hbb' (Ne.symm h25)
    · exact nf_of hinv hne htb (Ne.symm h14) ha1 (Ne.symm h04) (Ne.symm h24) haa' h03
    · exact nf_of hinv hne htb (Ne.symm h24) hs1 (Ne.symm h14) (Ne.symm h34) hsa h13
    · exact absurd rfl hne
    · exact nf_of hinv hne hts h24 hb1 h23 h25 hbb' (Ne.symm h35)
    · exact nf_of hinv hne hbt (Ne.symm h13) ha1 (Ne.symm h03) (Ne.symm h23) has h24
    · exact nf_of hinv hne hbb' (Ne.symm h25) hs1 (Ne.symm h15) (Ne.symm h35) hsa h14
    · exact nf_of hinv hne hbb' (Ne.symm h35) ht1 (Ne.symm h25) (Ne.symm h45) hts h24
    · exact absurd rfl hne
  · intro y hy x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have nb : ∀ (w u v : Fin (n + 1)), (w = u ∨ w = v) → (u = a ∨ u = s ∨ u = t ∨ u = b) →
        (v = a ∨ v = s ∨ v = t ∨ v = b) → w ∈ ({a, s, t, b} : Finset (Fin (n + 1))) := by
      intro w u v hw hu hv
      rcases hw with rfl | rfl
      · exact mem _ hu
      · exact mem _ hv
    rcases hy with h | h | h | h <;> rw [h]
    · exact win_of hinv (mem a (by simp)) (mem s (by simp)) has
        (fun w hw => nb w a t (hs1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem s (by simp)) (mem t (by simp)) hst
        (fun w hw => nb w s b (ht1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem t (by simp)) (mem s (by simp)) hts
        (fun w hw => nb w a t (hs1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem b (by simp)) (mem t (by simp)) hbt
        (fun w hw => nb w s b (ht1 w hw) (by simp) (by simp)) x hx
  · intro x hx
    refine F_mono (fun i h => ?_) hx
    unfold zeroOn at h
    split_ifs at h <;> simp_all
  · have hsub : ({a, s} : Finset (Fin (n + 1))) ⊆ {a, s, t, b} := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      tauto
    have := Finset.card_le_card hsub
    rw [Finset.card_pair h12] at this
    exact this

end PEqualNP.MetaComplexity.EdgeFn
