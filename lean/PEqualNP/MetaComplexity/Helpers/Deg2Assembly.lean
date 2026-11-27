import PEqualNP.MetaComplexity.Helpers.Deg2Count
import PEqualNP.MetaComplexity.Helpers.Deg2Bridge
import PEqualNP.MetaComplexity.Helpers.Deg2Cover

/-!
# The assembly of L-meta-649 (card D2-18), from the cards still missing

Conjecture until the checker accepts it. `assembly_of` proves the exact statement of L-meta-649
from the statements of the cards of the skeleton plan (the degree-two card plan)
that are not yet proved, each verbatim and universally quantified: `card10_e0`, `card12_alpha`,
`card13_beta`, `card15_identity`, `card15c_contexts`, `card16_form`, `card17_cover`. The cards
on main are used directly (D2-03c, D2-03d, D2-04 in `Deg2Bridge`; D2-07, D2-08 in `Deg2Circuit`;
D2-09, D2-10 E1, D2-11 through `card14_of` in `Deg2Count`). `card15_identity` and
`card15c_contexts` enter the chain only inside the proofs of D2-16 and D2-17, so the assembly
itself does not use them.

`assembly_of_identity` needs fewer: D2-17 (cover) is replaced by `cv_cover_of_identity`
(`Deg2Cover`, on main), which derives it from `card15_identity`. Its hypotheses are `card10_e0`,
`card12_alpha`, `card13_beta`, `card15_identity`, `card16_form`.

The proof is the plan's assembly: translate (D2-03), clean (D2-04), cover every incident pair by
pinned, served, `F_2` of the cone, or marker edges (D2-17), put the marker edges in a sound form
of at most `|M| + |X| + 4 |T|` gates (D2-16) and count it (D2-14), then add up:
`2 |OrM| + 2 |AndM| + 8 |X| + 12 (|M| + |X| + 4 |T|) + 2 N ≤ 48 size + 2 N`.
-/

namespace PEqualNP.MetaComplexity.Deg2

-- The hypotheses repeat the plan statements verbatim, binder names included.
set_option linter.unusedVariables false

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Deg2.Api

/-- The assembly from D2-14, D2-16 and D2-17 (cover) as hypotheses. -/
theorem assembly_core
    (h14 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.countedEdges W R).card ≤ 12 * (D.rootCone W R).card + 2 * W.card)
    (h16 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2),
      ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
        D.markerEdges I ⊆ F.countedEdges W R ∧
        (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card)
    (h17 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone),
      ∀ p w : Fin N, I p w →
        (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N := by
  intro N I _ C hI hmono hdeg hfun
  have hI' : NoRect I := hI
  let D : Dag N := ofCircuit N C
  have hwf : D.WF := card03b_wf C
  have hsize : D.size = C.size := by simp [D, Dag.size, ofCircuit, Circuit.size]
  have hcomp : Computes I D.fn := by
    intro z
    rw [← hfun z]
    show (ofCircuit N C).val z C.output = true ↔ C.eval (List.ofFn z) = true
    rw [Bridge.card03c_val C hmono z C.output]
    rfl
  have hd : D.deg D.out ≤ 2 := le_trans (Bridge.card03d_deg C hmono C.output) hdeg
  obtain ⟨D', hwf', hs', hc', hd', hcl'⟩ := Bridge.card04_clean I D hwf hcomp hd
  have hcov := h17 I D' hwf' hc' hd' hcl'
  obtain ⟨F, W, R, hsound, hmk, hF⟩ := h16 I D' hwf' hc' hd'
  have h14' := h14 I hI' F W R hsound
  have hW : W.card ≤ N := by
    simpa using Finset.card_le_univ W
  have hp := card08_pinned I hI' D'
  have hsv := card17s_served I D'
  have h7 : (D'.fSet I D'.cone 2).card ≤ 8 * D'.X.card :=
    card07_two_line I hI' D' D'.cone (api_coneOf_down D' {D'.out})
  have hcl := api_classes_card D'
  have hao := api_andor_card D'
  have hE : Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2) ⊆
      D'.pinned I ∪ D'.served I ∪ D'.fSet I D'.cone 2 ∪ F.countedEdges W R := by
    intro e he
    have he' : I e.1 e.2 := (Finset.mem_filter.1 he).2
    have h := hcov e.1 e.2 he'
    simp only [Finset.mem_union] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (hmk h)
  have hU := Finset.card_le_card hE
  have hU1 := Finset.card_union_le (D'.pinned I ∪ D'.served I ∪ D'.fSet I D'.cone 2)
    (F.countedEdges W R)
  have hU2 := Finset.card_union_le (D'.pinned I ∪ D'.served I) (D'.fSet I D'.cone 2)
  have hU3 := Finset.card_union_le (D'.pinned I) (D'.served I)
  omega

/-- D2-18, in the exact form of L-meta-649, from the statements of the seven missing cards. -/
theorem assembly_of
    (h10e0 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card)
    (h12 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card)
    (h13 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card)
    (_h15 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool),
      D.fn x = true ↔
        ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (_h15c : ∀ {N : ℕ} (D : Dag N) (hwf : D.WF) (hd : D.deg D.out ≤ 2),
      ∃ D' : Dag N, D.gates <+: D'.gates ∧ D'.WF ∧
        D'.size ≤ D.size + 2 * D.Tor.card + 2 * D.Tandf.card ∧
        ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
          ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
            D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size))
    (h16 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2),
      ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
        D.markerEdges I ⊆ F.countedEdges W R ∧
        (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card)
    (h17 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (hcl : D.Cleaned I D.cone),
      ∀ p w : Fin N, I p w →
        (p, w) ∈ D.pinned I ∪ D.served I ∪ D.fSet I D.cone 2 ∪ D.markerEdges I) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N :=
  assembly_core (fun I hI D W R hs => card14_of h10e0 h12 h13 I hI D W R hs) h16 h17

/-- D2-18, in the exact form of L-meta-649, from five missing cards: D2-17 (cover) comes from
`card15_identity` through `cv_cover_of_identity`, and `card15c_contexts` is not needed here. -/
theorem assembly_of_identity
    (h10e0 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R),
      (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card)
    (h12 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.alphaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card + W.card)
    (h13 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N)
      (W : Finset (Fin N)) (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R)
      (hcl : D.Cleaned I (D.rootCone W R)),
      (D.betaEdges I W R \ (D.e0Set W R ∪ D.e1Set I W R ∪ D.fSet I (D.rootCone W R) 2)).card ≤
        2 * ((D.rootCone W R).filter (fun f => D.deg f = 1)).card)
    (h15 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2) (x : Fin (N + N) → Bool),
      D.fn x = true ↔
        ∃ b, D.IsItem b ∧ D.ctx b x = true ∧ ∀ r, D.IsFactor b r → D.val x r = true)
    (h16 : ∀ {N : ℕ} (I : Fin N → Fin N → Prop) (D : Dag N) (hwf : D.WF)
      (hc : Computes I D.fn) (hd : D.deg D.out ≤ 2),
      ∃ (F : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ), Dag.SoundPartialForm I F W R ∧
        D.markerEdges I ⊆ F.countedEdges W R ∧
        (F.rootCone W R).card ≤ D.M.card + D.X.card + 4 * D.T.card) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 48 * C.size + 2 * N :=
  assembly_core (fun I hI D W R hs => card14_of h10e0 h12 h13 I hI D W R hs) h16
    (fun I D hwf hc hd hcl => cv_cover_of_identity (fun I D => h15 I D) I D hwf hc hd hcl)

end PEqualNP.MetaComplexity.Deg2
