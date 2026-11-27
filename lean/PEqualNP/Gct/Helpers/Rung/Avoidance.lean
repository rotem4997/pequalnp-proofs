import Mathlib
import PEqualNP.Gct.Helpers.Rung.Statements

/-!
# Avoidance

Finitely many subspaces of dimension at most `q` of a finite dimensional complex vector space
are met only in `0` by one subspace of dimension `dim V - q`. Induction on the dimension of the
avoiding subspace: a vector outside the finitely many proper subspaces `W i ⊔ U` and `U` raises
the dimension by one.
-/

namespace PEqualNP.Gct.Rung

/-- The induction: for every `d` with `d + q ≤ dim V` there is a subspace of dimension `d`
meeting every `W i` only in `0`. -/
theorem avoidance_aux (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ι : Type) [Finite ι] (W : ι → Submodule ℂ V) (q : ℕ)
    (hq : ∀ i, Module.finrank ℂ (W i) ≤ q) :
    ∀ d : ℕ, d + q ≤ Module.finrank ℂ V →
      ∃ U : Submodule ℂ V, Module.finrank ℂ U = d ∧ ∀ i, U ⊓ W i = ⊥ := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨⊥, finrank_bot ℂ V, fun i => bot_inf_eq _⟩
  | succ d ih =>
    intro hd
    obtain ⟨U, hU, hUW⟩ := ih (by omega)
    let F : Option ι → Submodule ℂ V := fun o =>
      match o with
      | none => U
      | some i => W i ⊔ U
    have hne : ∀ o : Option ι, F o ≠ ⊤ := by
      intro o htop
      have h0 : Module.finrank ℂ (F o) = Module.finrank ℂ V := by
        rw [htop, finrank_top]
      cases o with
      | none =>
        change Module.finrank ℂ U = Module.finrank ℂ V at h0
        omega
      | some i =>
        change Module.finrank ℂ (W i ⊔ U : Submodule ℂ V) = Module.finrank ℂ V at h0
        have h1 := Submodule.finrank_add_le_finrank_add_finrank (W i) U
        have h3 := hq i
        omega
    obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top F hne
    have hcU : c ∉ U := hc none
    have hcW : ∀ i, c ∉ W i ⊔ U := fun i => hc (some i)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hcU U.zero_mem
    refine ⟨U ⊔ Submodule.span ℂ {c}, ?_, fun i => ?_⟩
    · have hdisj : U ⊓ Submodule.span ℂ {c} = ⊥ :=
        disjoint_iff.mp ((Submodule.disjoint_span_singleton' hc0).mpr hcU)
      have h := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span ℂ {c})
      rw [hdisj, finrank_bot, finrank_span_singleton hc0] at h
      omega
    · rw [Submodule.eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hx1
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hx2' : u + t • c ∈ W i := hx2
      have ht : t = 0 := by
        by_contra h0
        apply hcW i
        have e : t • c = (u + t • c) + (-u) := by abel
        have hm : t • c ∈ W i ⊔ U := by
          rw [e]
          exact Submodule.add_mem_sup hx2' (U.neg_mem hu)
        exact (Submodule.smul_mem_iff _ h0).mp hm
      rw [ht, zero_smul, add_zero] at hx2' ⊢
      have hmem : u ∈ U ⊓ W i := ⟨hu, hx2'⟩
      rw [hUW i] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem

/-- Avoidance: the case `d = dim V - q` of the induction. -/
theorem avoidance : Avoidance := by
  intro V _ _ _ ι _ W q hq
  by_cases h : q ≤ Module.finrank ℂ V
  · exact avoidance_aux V ι W q hq (Module.finrank ℂ V - q) (by omega)
  · refine ⟨⊥, ?_, fun i => bot_inf_eq _⟩
    rw [finrank_bot]
    omega

end PEqualNP.Gct.Rung
