import PEqualNP.MetaComplexity.Helpers.LocalCore
import PEqualNP.MetaComplexity.Helpers.Coding

/-!
# The core of the local reduction chain, with well-formedness given

Helper for `L-meta-036`. The argument of `LocalCore.core_of`, started from any decomposition of
the image of the all-false input as an instance instead of from the lemma that produces one.
The only numeric hypothesis left is `3 q < n`: after fixing at most `3 q` input positions the
subcube still has a free position.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalCoreWf

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.LocalCore

theorem core_wf : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, (w x).length ≤ M) → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → ∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → (¬ ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) ∧ 2 ^ ((n - 3 * q) / (4 * q)) ≤ 8 * q * ((s + 1) * ((s + 1) * ((3 * ((Nat.log 2 M + s + 2) * (Nat.log 2 M + s + 2))) ^ s * (Nat.log 2 M + s + 1)))) := by
  classical
  intro n q M w hq hloc hlen hcor hn n0 s0 T0 hz hT0
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hc, hs⟩
    have hmem : w (fun _ : Fin n => false) ∈ PartialMCSP := ⟨n0, s0, T0, hz, hT0, f, hc, hs⟩
    have := (hcor _).mpr hmem
    simp at this
  -- the all-false input and the length of its image
  obtain ⟨z, hzdef⟩ : ∃ z : Fin n → Bool, z = fun _ => false := ⟨_, rfl⟩
  rw [← hzdef] at hz
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = (w z).length := ⟨_, rfl⟩
  have hL0' : L0 = s0 + 1 + 2 * 2 ^ n0 := by
    rw [hL0, hz]
    simp only [List.length_append, List.length_replicate, List.length_cons, length_enc, hT0]
    omega
  have hL0M : L0 ≤ M := hL0 ▸ hlen z
  -- the three certificates
  obtain ⟨S1, c1, h1⟩ := hloc (L0 - 1) z
  obtain ⟨S2, c2, h2⟩ := hloc L0 z
  obtain ⟨S3, c3, h3⟩ := hloc s0 z
  have hU : (S1 ∪ S2 ∪ S3).card ≤ 3 * q := by
    have a := Finset.card_union_le (S1 ∪ S2) S3
    have b := Finset.card_union_le S1 S2
    omega
  obtain ⟨m, ext, hm, hextU, hpar, hV⟩ := subcube n (S1 ∪ S2 ∪ S3)
  have hzi : ∀ i : Fin n, z i = false := fun i => by rw [hzdef]
  -- on the subcube: constant length, separator bit false
  have len : ∀ y : Fin m → Bool, (w (ext y)).length = L0 := by
    intro y
    have a1 := h1 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    have a2 := h2 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    have b1 : L0 ≤ (w (ext y)).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega), eq_comm, List.getElem?_eq_none_iff] at a1
      omega
    have b2 : (w (ext y)).length ≤ L0 := by
      rw [List.getElem?_eq_none (l := w z) (by omega), List.getElem?_eq_none_iff] at a2
      exact a2
    omega
  have sep : ∀ y : Fin m → Bool, (w (ext y))[s0]? = some false := by
    intro y
    have a3 := h3 (ext y) (fun i hi => by
      rw [hzi, hextU y i (by simp [hi])])
    rw [a3, hz]
    exact (get_fmt s0 _).2.1
  -- the cover
  let E : Idx L0 s0 → Finset (Fin m → Bool) := fun a =>
    Finset.univ.filter (fun y => Fmt a.1 (nn L0 a.1) a.2.1 (w (ext y)))
  let eqv : Idx L0 s0 ≃ Fin (Fintype.card (Idx L0 s0)) := Fintype.equivFin _
  have hm0 : 0 < m := by omega
  have hfin := Coding.parity_cover m (2 * q) (Fintype.card (Idx L0 s0)) (fun a => E (eqv.symm a)) (by omega) hm0
    (by
      intro a y hy
      obtain ⟨⟨s, f⟩, hsf⟩ : ∃ p, p = eqv.symm a := ⟨_, rfl⟩
      simp only [← hsf] at hy ⊢
      have hy' : ¬ Fmt s (nn L0 s) f.1 (w (ext y)) :=
        fun h => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      by_cases hl : L0 = (s : ℕ) + 1 + 2 * 2 ^ nn L0 s
      · obtain ⟨p1, p2, b1, b2, e1, e2, hw⟩ :=
          fmt_witness s (nn L0 s) f.1 (w (ext y)) ((len y).trans hl) hy'
        obtain ⟨Sa, ca, ha⟩ := hloc p1 (ext y)
        obtain ⟨Sb, cb, hb⟩ := hloc p2 (ext y)
        obtain ⟨V, cV, hVV⟩ := hV (Sa ∪ Sb)
        have cab := Finset.card_union_le Sa Sb
        refine ⟨V, by omega, fun y' hy'' hmem => ?_⟩
        have agree := hVV y y' hy''
        exact hw (w (ext y'))
          ((ha (ext y') (fun i hi => agree i (Finset.mem_union_left _ hi))).trans e1)
          ((hb (ext y') (fun i hi => agree i (Finset.mem_union_right _ hi))).trans e2)
          (Finset.mem_filter.mp hmem).2
      · refine ⟨∅, by simp, fun y' _ hmem => ?_⟩
        obtain ⟨T, e, hTl, -⟩ := (Finset.mem_filter.mp hmem).2
        have hlen' := len y'
        rw [e] at hlen'
        simp only [List.length_append, List.length_replicate, List.length_cons, length_enc,
          hTl] at hlen'
        omega)
    (by
      intro y
      constructor
      · rintro ⟨a, ha⟩
        obtain ⟨T, e, hTl, hc⟩ := (Finset.mem_filter.mp ha).2
        have hmem : w (ext y) ∈ PartialMCSP :=
          ⟨_, _, T, e, hTl, (eqv.symm a).2.1, hc, (eqv.symm a).2.2⟩
        rw [← hpar y]
        exact (hcor _).mpr hmem
      · intro hodd
        obtain ⟨n'', s, T, e, hTl, f, hc, hs⟩ := (hcor (ext y)).mp (by rw [hpar y]; exact hodd)
        have hs0 : s ≤ s0 := by
          by_contra hgt
          have a := (get_fmt s (encodePartial T)).1 s0 (by omega)
          rw [← e, sep y] at a
          simp at a
        have hLs : L0 = s + 1 + 2 * 2 ^ n'' := by
          have hlen' := len y
          rw [e] at hlen'
          simp only [List.length_append, List.length_replicate, List.length_cons, length_enc,
            hTl] at hlen'
          omega
        have hnn : n'' = nn L0 s := by rw [hLs, nn_eq]
        subst hnn
        refine ⟨eqv ⟨⟨s, by omega⟩, ⟨f, hs⟩⟩, ?_⟩
        show y ∈ E (eqv.symm (eqv _))
        rw [Equiv.symm_apply_apply]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T, e, hTl, hc⟩)
  -- the arithmetic
  have hN := card_idx L0 s0 (Nat.log 2 M) (Nat.log_mono_right hL0M)
  obtain ⟨N, hNdef⟩ : ∃ N, N = Fintype.card (Idx L0 s0) := ⟨_, rfl⟩
  rw [← hNdef] at hfin hN
  obtain ⟨d, hd⟩ : ∃ d, d = m / (2 * (2 * q)) := ⟨_, rfl⟩
  rw [← hd] at hfin
  have hdm : d ≤ m := hd ▸ Nat.div_le_self _ _
  have h2 : 2 ^ m = 2 ^ (m - d) * 2 ^ d := by
    rw [← pow_add]; congr 1; omega
  have h3 : 2 ^ d ≤ 8 * q * N := by
    have h4 : 2 ^ (m - d) * 2 ^ d ≤ 2 ^ (m - d) * (8 * q * N) := by
      rw [← h2]
      calc 2 ^ m ≤ N * (4 * (2 * q) * 2 ^ (m - d)) := hfin
        _ = 2 ^ (m - d) * (8 * q * N) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  have h5 : (n - 3 * q) / (4 * q) ≤ d := by
    rw [hd, show 4 * q = 2 * (2 * q) by ring]
    exact Nat.div_le_div_right (by omega)
  calc 2 ^ ((n - 3 * q) / (4 * q)) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h5
    _ ≤ 8 * q * N := h3
    _ ≤ 8 * q * ((s0 + 1) * cnt (Nat.log 2 M) s0) := Nat.mul_le_mul_left _ hN

end PEqualNP.MetaComplexity.Helpers.LocalCoreWf
