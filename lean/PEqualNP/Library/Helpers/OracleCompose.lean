import PEqualNP.Library.Machines.ComposeRun

/-!
# Running a plain machine, then an oracle machine

Helper module (proofs only, no statement may use it).

Given a plain machine `M1`, an oracle machine `O`, a map `φ` from the output alphabet of `M1` to
the input alphabet of `O.tm` and a default symbol `dd` of that alphabet, `ocomp M1 O φ dd` is
the oracle machine whose underlying machine is `comp M1 O.tm φ (some dd)` of
`Machines/Compose.lean`, with the query stack, query bits and labels `ask`, `yes`, `no` of `O`
relabelled into the composite. The run of `M1` and the transfer never stand at the relabelled
`ask`, so there the oracle step is the plain step; the run of `O` is simulated step by step,
including its oracle steps.

`ocomp_decides`: if `M1` maps the encoding of `a` to the binary string `g a` in polynomial time
and `S ∈ OracleP A`, then `{a | g a ∈ S}` is decided in polynomial time relative to `A`.
-/

namespace PEqualNP.Library.Helpers.OracleCompose

open Turing PEqualNP.Library.Machines

variable {M1 : FinTM2} {O : OracleTM2}

/-- The composite oracle machine. -/
def ocomp (M1 : FinTM2) (O : OracleTM2) (φ : M1.Γ M1.k₁ → O.tm.Γ O.tm.k₀)
    (dd : O.tm.Γ O.tm.k₀) : OracleTM2 where
  tm := comp M1 O.tm φ (some dd)
  kq := some (Sum.inr O.kq)
  queryBit := fun x => O.queryBit x
  ask := Sum.inr (Sum.inl O.ask)
  yes := Sum.inr (Sum.inl O.yes)
  no := Sum.inr (Sum.inl O.no)

variable (φ : M1.Γ M1.k₁ → O.tm.Γ O.tm.k₀) (dd : O.tm.Γ O.tm.k₀) (A : Language Bool)

/-- The oracle step, typed on configurations of the composite. -/
noncomputable def F : CCfg M1 O.tm → Option (CCfg M1 O.tm) := (ocomp M1 O φ dd).step A

theorem F_eq (c : CCfg M1 O.tm) (hc : c.l ≠ some (Sum.inr (Sum.inl O.ask))) :
    F φ dd A c = TM2.step (prog M1 O.tm φ (some dd)) c := by
  unfold F OracleTM2.step
  split
  · exact absurd ‹_› hc
  · rfl

theorem F_step1 (w : O.tm.σ × Option (O.tm.Γ O.tm.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    F φ dd A (emb1 w c) = some (emb1 w c') := by
  rw [F_eq]
  · exact step1 φ (some dd) w c c' h
  · obtain ⟨l, v, S⟩ := c
    cases l <;> simp [emb1]

theorem F_step2 (u : M1.σ) (b : Option (O.tm.Γ O.tm.k₀)) (c c' : TM2.Cfg O.tm.Γ O.tm.Λ O.tm.σ)
    (h : O.step A c = some c') :
    F φ dd A (emb2 u b c) = some (emb2 u b c') := by
  classical
  by_cases hc : c.l = some O.ask
  · obtain ⟨l, v, S⟩ := c
    simp only at hc
    subst hc
    unfold OracleTM2.step at h
    split at h
    swap
    · exact absurd rfl ‹_›
    cases h
    unfold F OracleTM2.step
    split
    swap
    · exact absurd rfl ‹_›
    show some (⟨some (if ((embStk2 S : ∀ k, List (CΓ M1 O.tm k)) (some (Sum.inr O.kq))).reverse.map
        O.queryBit ∈ A then Sum.inr (Sum.inl O.yes) else Sum.inr (Sum.inl O.no)), (u, v, b),
        Function.update (embStk2 S) (some (Sum.inr O.kq)) []⟩ : CCfg M1 O.tm) = _
    rw [← embStk2_update]
    show some (⟨_, _, _⟩ : CCfg M1 O.tm) =
      some (⟨Option.map _ (some (if (S O.kq).reverse.map O.queryBit ∈ A then O.yes else O.no)),
        _, _⟩)
    congr 2
    simp only [Option.map_some]
    congr 1
    exact (apply_ite (fun l => (Sum.inr (Sum.inl l) : CΛ M1 O.tm)) _ _ _).symm
  · have h' : TM2.step O.tm.m c = some c' := by
      unfold OracleTM2.step at h
      split at h
      · exact absurd ‹_› hc
      · exact h
    rw [F_eq]
    · exact step2 φ (some dd) u b c c' h'
    · obtain ⟨l, v, S⟩ := c
      cases l with
      | none => simp [emb2]
      | some l =>
        simp only [emb2, Option.map_some, ne_eq, Option.some.injEq, Sum.inr.injEq,
          Sum.inl.injEq]
        intro e; exact hc (by rw [e])

theorem F_tr (b : Bool) (s : Cσ M1 O.tm) (S : ∀ k, List (CΓ M1 O.tm k)) :
    F φ dd A ⟨some (Sum.inr (Sum.inr b)), s, S⟩ =
      TM2.step (prog M1 O.tm φ (some dd)) ⟨some (Sum.inr (Sum.inr b)), s, S⟩ :=
  F_eq φ dd A _ (by simp)

theorem oloopA (v1 : M1.σ) (v2 : O.tm.σ) (u : List (O.tm.Γ O.tm.k₀)) :
    ∀ (l : List (M1.Γ M1.k₁)) (t : List (O.tm.Γ O.tm.k₀)) (b : Option (O.tm.Γ O.tm.k₀)),
      (flip bind (F φ dd A))^[l.length + 1]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st l t u⟩ : CCfg M1 O.tm)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none),
          st [] ((l.map φ).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact (F_tr φ dd A _ _ _).trans (stepA_nil φ dd v1 v2 b t u)
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (F φ dd A)
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 O.tm)) =
        some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ :=
      (F_tr φ dd A _ _ _).trans (stepA_cons φ dd v1 v2 b x l t u)
    rw [e, ih]
    simp

theorem oloopB (v1 : M1.σ) (v2 : O.tm.σ) :
    ∀ (t u : List (O.tm.Γ O.tm.k₀)) (b : Option (O.tm.Γ O.tm.k₀)),
      (flip bind (F φ dd A))^[t.length + 1]
          (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] t u⟩ : CCfg M1 O.tm)) =
        some ⟨some (Sum.inr (Sum.inl O.tm.main)), (v1, v2, none), st [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact (F_tr φ dd A _ _ _).trans (stepB_nil φ dd v1 v2 b u)
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (F φ dd A)
        (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 O.tm)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ :=
      (F_tr φ dd A _ _ _).trans (stepB_cons φ dd v1 v2 b x t u)
    rw [e, ih]
    simp

theorem otransfer (v1 : M1.σ) (v2 : O.tm.σ) (o : List (M1.Γ M1.k₁)) :
    (flip bind (F φ dd A))^[((o.map φ).reverse ++ []).length + 1 + (o.length + 1)]
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, none),
          Function.update (fun _ => [] : ∀ k, List (CΓ M1 O.tm k)) (some (Sum.inl M1.k₁)) o⟩ :
          CCfg M1 O.tm)) =
      some ⟨some (Sum.inr (Sum.inl O.tm.main)), (v1, v2, none),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 O.tm k)) (some (Sum.inr O.tm.k₀))
          (o.map φ)⟩ := by
  rw [Function.iterate_add_apply, ← st_start, oloopA, oloopB, ← st_end]
  simp

/-- The run of the composite oracle machine, with its length. -/
theorem ocomp_run (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁))
    (o2 : List (O.tm.Γ O.tm.k₁)) (s1 s2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
    (h2 : (flip bind (O.step A))^[s2] (some (initList O.tm (o1.map φ))) =
      some (haltList O.tm o2)) :
    ∃ n, n ≤ s1 + (2 * o1.length + 2) + s2 ∧ o1.length ≤ i.length + maxPush M1 * s1 ∧
      (flip bind ((ocomp M1 O φ dd).step A))^[n]
          (some (initList (ocomp M1 O φ dd).tm i)) =
        some (haltList (ocomp M1 O φ dd).tm o2) := by
  have p1 := simulate (TM2.step M1.m) (F φ dd A)
    (emb1 (O.tm.initialState, none)) (F_step1 φ dd A _) s1 _ _ h1
  rw [emb1_init φ (some dd), emb1_halt] at p1
  have pt := otransfer φ dd A M1.initialState O.tm.initialState o1
  have p2 := simulate (O.step A) (F φ dd A)
    (emb2 M1.initialState none) (F_step2 φ dd A _ _) s2 _ _ h2
  rw [emb2_init, emb2_halt φ (some dd)] at p2
  refine ⟨s2 + ((((o1.map φ).reverse ++ []).length + 1 + (o1.length + 1)) + s1), ?_, ?_, ?_⟩
  · simp; omega
  · have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; simp
  · rw [Function.iterate_add_apply, Function.iterate_add_apply]
    exact (congrArg _ (congrArg _ p1)).trans ((congrArg _ pt).trans p2)

/-- Composition with a polynomial-time plain preprocessing: if `M1` maps the encoding of `a` to
the binary string `g a` (over the output alphabet `out1`) within `t1` steps, and `S ∈ OracleP A`,
then `{a | g a ∈ S}` is decided in polynomial time relative to `A`. -/
theorem ocomp_decides {α αΓ : Type} (ea : α → List αΓ) (S' : Set α) (S : Language Bool)
    (g : α → List Bool) (hS' : ∀ a, a ∈ S' ↔ g a ∈ S) (M1 : FinTM2)
    (e1 : M1.Γ M1.k₀ ≃ αΓ) (out1 : M1.Γ M1.k₁ ≃ Bool) (t1 : Polynomial ℕ)
    (hrun : ∀ a, ∃ s, s ≤ t1.eval (ea a).length ∧
      (flip bind (TM2.step M1.m))^[s] (some (initList M1 ((ea a).map e1.symm))) =
        some (haltList M1 ((g a).map out1.symm)))
    (hS : S ∈ OracleP A) : OracleDecidableInPolyTime A ea S' := by
  obtain ⟨p, fS, O, ein, eout, hfS, hO⟩ := hS
  let φ : M1.Γ M1.k₁ → O.tm.Γ O.tm.k₀ := fun x => ein.symm (out1 x)
  let dd : O.tm.Γ O.tm.k₀ := ein.symm true
  let T : Polynomial ℕ :=
    t1 + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush M1) * t1) + Polynomial.C 2) +
      p.comp (Polynomial.X + Polynomial.C (maxPush M1) * t1)
  refine ⟨T, fun a => fS (g a), ocomp M1 O φ dd, e1, eout, fun a => (hS' a).trans (hfS _),
    fun a => ?_⟩
  obtain ⟨s1, hs1, h1⟩ := hrun a
  obtain ⟨⟨⟨s2, h2⟩, hs2⟩⟩ := hO (g a)
  have hφ : ((g a).map out1.symm).map φ = (g a).map ein.symm := by
    rw [List.map_map]
    refine List.map_congr_left fun y _ => ?_
    show ein.symm (out1 (out1.symm y)) = _
    rw [Equiv.apply_symm_apply]
  have hs2' : s2 ≤ p.eval (g a).length := hs2
  rw [← hφ] at h2
  obtain ⟨n, hn, hlen, hrun'⟩ := ocomp_run φ dd A _ _ _ s1 s2 h1 h2
  refine ⟨⟨⟨n, hrun'⟩, ?_⟩⟩
  simp only [List.length_map] at hlen hn
  have hmul : maxPush M1 * s1 ≤ maxPush M1 * t1.eval (ea a).length := Nat.mul_le_mul_left _ hs1
  have b3 : p.eval (g a).length ≤
      p.eval ((ea a).length + maxPush M1 * t1.eval (ea a).length) := eval_mono _ (by omega)
  simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp]
  omega

end PEqualNP.Library.Helpers.OracleCompose
