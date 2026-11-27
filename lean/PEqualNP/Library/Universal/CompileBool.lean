import PEqualNP.Library.Universal.Compile

/-!
# Compiling a stack machine with input alphabet `Bool`

Helper module (proofs only, no statement may use it). The generic compilation environment of
`Compile` is instantiated a second time, for machines whose input alphabet is `Bool`: the input
number `1` reads as `true` and every other number below `4` reads as `false`. The simulation
lemmas of the generic development are reused unchanged (`compileBool`).
-/

namespace PEqualNP.Library.Universal

open Turing

section CompileBool

variable (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool) (eOut : tm.Γ tm.k₁ ≃ Bool)

/-- The compilation environment of a machine with input alphabet `Bool`. -/
noncomputable def envOfBool : Env tm.K tm.Γ tm.Λ tm.σ where
  M := tm.m
  nσ := @Fintype.card tm.σ tm.σFin
  nσ_pos := @Fintype.card_pos tm.σ tm.σFin ⟨tm.initialState⟩
  num v := (σEquiv tm v).val
  σof n := if h : n < @Fintype.card tm.σ tm.σFin then (σEquiv tm).symm ⟨n, h⟩ else tm.initialState
  σof_num v := by simp
  num_lt v := (σEquiv tm v).isLt
  nK := @Fintype.card tm.K tm.kFin
  numK k := (kEquiv tm k).val
  numK_lt k := (kEquiv tm k).isLt
  numK_inj := fun a b h => (kEquiv tm).injective (Fin.ext h)
  L := flatList tm
  start l := Classical.choose (flatList_placed tm l)
  placed_start l := Classical.choose_spec (flatList_placed tm l)
  k₀ := tm.k₀
  inSym n := eIn.symm (decide (n = 1))
  k₁ := tm.k₁
  outBit y := bitCode (eOut y)

theorem compileBool :
    ∃ (c : Code) (d : ℕ), ∀ (l : List Bool) (b : Bool) (n : ℕ),
      (flip bind (Turing.TM2.step tm.m))^[n] (some (Turing.initList tm (l.map eIn.invFun))) =
          some (Turing.haltList tm [eOut.invFun b]) →
      c.outputsWithin (l.map (fun b => cond b 1 0)) (d * n + d) [bitCode b] := by
  let E := envOfBool tm eIn eOut
  refine ⟨⟨E.P, E.nK, E.start tm.main, E.num tm.initialState, E.numK tm.k₀, E.numK tm.k₁⟩,
    E.L.length + 3, fun l b n hrun => ?_⟩
  -- the initial configurations are related
  have hin : List.Forall₂ (fun s y => E.decode tm.k₀ s = some y)
      (l.map (fun b => cond b 1 0)) (l.map eIn.invFun) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun x _ => ?_
    have hlt : (cond x 1 0 : ℕ) < 4 := by cases x <;> simp
    have := E.decode_in hlt
    cases x <;> simpa [E, envOfBool] using this
  have hstk : (Turing.initList tm (l.map eIn.invFun)).stk =
      Function.update (fun _ => []) tm.k₀ (l.map eIn.invFun) := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk; simp [Turing.initList]
    · simp [Turing.initList, hk]
  have hrel : E.Rel (Turing.initList tm (l.map eIn.invFun))
      ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map (fun b => cond b 1 0))⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    rw [hstk]
    exact Env.StkRel.init tm.k₀ hin
  obtain ⟨t, ht, hpc, hst, hsr⟩ := E.sim_run n _ _ _ hrun hrel
  -- read off the final configuration
  generalize hX : (step E.P)^[t] _ = X at hpc hst hsr
  obtain ⟨pc, a, T⟩ := X
  simp only at hpc hst hsr
  have hout : (Turing.haltList tm [eOut.invFun b]).stk tm.k₁ = [eOut.invFun b] := by
    simp [Turing.haltList]
  have h2 := hsr.2 tm.k₁
  rw [hout] at h2
  obtain ⟨s, hs, hy⟩ : ∃ s, T.getD (E.numK tm.k₁) [] = [s] ∧
      E.decode tm.k₁ s = some (eOut.invFun b) := by
    exact forall₂_singleton (R := fun s y => E.decode tm.k₁ s = some y) h2
  have hbit : E.outBit (eOut.invFun b) = bitCode b := by simp [E, envOfBool]
  obtain ⟨T', hfin, hT'⟩ := E.sim_fin a (by rw [hst]; exact E.num_lt _) T hsr.1 s
    (eOut.invFun b) hs hy (by rw [hbit]; exact bitCode_le b)
  have hpc' : pc = some E.L.length := hpc
  subst hpc'
  rw [← hX, ← Function.iterate_add_apply, hbit] at hfin
  rw [hbit] at hT'
  refine Code.outputsWithin_mono _ _ (t := 3 + t) ?_ _ ?_
  · have : E.L.length * n ≤ (E.L.length + 3) * n := Nat.mul_le_mul_right _ (by omega)
    omega
  · unfold Code.outputsWithin Code.run Code.init
    simp only
    rw [hfin]
    exact ⟨rfl, hT'⟩

end CompileBool

end PEqualNP.Library.Universal
