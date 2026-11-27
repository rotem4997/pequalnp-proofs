import PEqualNP.Library.LRAT.LinkN2
import PEqualNP.Library.LRAT.PromiseGen

/-!
# Refusal certificates for circuits with NOT gates, agreement on the listed rows only

`LinkN2.lower_of_unsat2` asks a circuit of AND, OR and NOT gates (`FanInTwo`) to be right on
every input. Here it only has to be right on the rows listed, which is what representing a graph
(`Represents`) by a circuit with NOT gates needs. This is `Promise.promise_lower` and
`Promise.rep_lower_mask` with the NOT encoding `LinkN.enc2` in place of the AND/OR one: an
unsatisfiable `LinkN.enc2` formula (an LRAT refutation) says that no circuit with NOT gates of at
most `s` gates represents the graph.
-/

namespace PEqualNP.Library.LRAT.PromiseN

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.LRAT
  PEqualNP.Library.LRAT.LinkN PEqualNP.Represents

/-- A circuit of AND, OR and NOT gates of fan-in at most two that is right on the listed rows
has more than `s` gates when the NOT encoding `enc2 n s g rows` is unsatisfiable. -/
theorem promiseN_lower (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hrows : ∀ r ∈ rows, r < 2 ^ n)
    (hU : ¬ FormulaSat (enc2 n s g rows)) (C : Circuit) (hC : FanInTwo C)
    (hev : ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i) = g r) :
    s + 1 ≤ C.size := by
  by_contra h
  have hv := valid_ofCirc n s g (· ∈ rows) C hC (by simp only [Circuit.size] at h; omega)
    (fun r hr => hev r hr)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact hU ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

/-- No circuit with NOT gates of at most `s` gates represents `A`, when the NOT encoding on the
`n * m` rows of the representing problem is unsatisfiable. -/
theorem repN_lower {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ (u : Fin n) (v : Fin m), g (Promise.repRow n u v) = A u v)
    (hU : ¬ FormulaSat (enc2 (n + m) s g (Promise.repRows n m))) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C := by
  rintro ⟨C, hC, hs, hr⟩
  have hmem : ∀ r ∈ Promise.repRows n m, ∃ (u : Fin n) (v : Fin m), Promise.repRow n u v = r := by
    intro r hr'
    simpa [Promise.repRows] using hr'
  have hrow : ∀ r ∈ Promise.repRows n m, r < 2 ^ (n + m) := by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    rw [Promise.repRow_testBit u.2]
    have := u.2; have := v.2
    simp; omega
  have := promiseN_lower (n + m) s g (Promise.repRows n m) hrow hU C hC (by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    rw [Promise.repRow_eq, hr, hg])
  omega

/-- The mask form: bit `m * u + v` of `M` says whether left `u` and right `v` are joined. -/
theorem repN_lower_mask (n m M s : ℕ)
    (hU : ¬ FormulaSat (enc2 (n + m) s (Promise.gMask n m M) (Promise.repRows n m))) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧
      Represents (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) C :=
  repN_lower (n := n) (m := m) (fun u v => M.testBit (m * u + v)) s (Promise.gMask n m M)
    (fun u v => Promise.gMask_row (n := n) (m := m) M u v) hU

end PEqualNP.Library.LRAT.PromiseN
