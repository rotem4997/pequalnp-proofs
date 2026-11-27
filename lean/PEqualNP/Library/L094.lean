import PEqualNP.Library.L083
import PEqualNP.Library.Machines.FirstTime
import PEqualNP.Library.Helpers.PadMap

/-- For `k ≥ 1`, the padding `x ↦ 1 ^ (2 ^ (|x| ^ k) + k) 0 x` is computable within
`c * 2 ^ (n ^ k) + c` steps. -/
theorem PEqualNP.Library.L094 : ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) (fun n : ℕ => c * 2 ^ (n ^ k) + c) := by
  intro k hk
  have hn : ∀ n : ℕ, n ≤ 2 ^ (n ^ k) := fun n =>
    (Nat.le_self_pow (by omega) n).trans (Nat.lt_two_pow_self).le
  obtain ⟨c0, hc0⟩ := PEqualNP.Library.L083 k hk
  obtain ⟨p, hp⟩ := PEqualNP.Library.Machines.clockPair_time
  have hA := hp (fun n => 2 ^ (n ^ k)) c0 hc0
  obtain ⟨C, hC⟩ := PEqualNP.Library.Helpers.polynomial_le_two_pow_pow_add_const p k hk
  have hB := PEqualNP.Library.Machines.comp_time (fun x : List Bool => x)
    PEqualNP.Library.encodePair (fun x : List Bool => x)
    (fun x : List Bool => (List.replicate (2 ^ (x.length ^ k)) true, x))
    (fun p : List Bool × List Bool => p.1 ++ false :: p.2)
    _ (fun n => 2 * n + 3) (fun n => 2 ^ (n ^ k) + n) hA
    PEqualNP.Library.Helpers.sepPair_time (fun a b h => by dsimp; omega)
    (fun x => by simp [PEqualNP.Library.encodePair])
  have key : ∀ j : ℕ, ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + j) true ++ false :: x)
      (fun n : ℕ => c * 2 ^ (n ^ k) + c) := by
    intro j
    induction j with
    | zero =>
      refine ⟨c0 + C + 20, PEqualNP.Library.Machines.time_mono hB fun n => ?_⟩
      have e1 := hC n
      have e2 := hn n
      have e3 : (c0 + C + 20) * 2 ^ n ^ k = c0 * 2 ^ n ^ k + C * 2 ^ n ^ k + 20 * 2 ^ n ^ k := by
        ring
      rw [e3]
      generalize c0 * 2 ^ n ^ k = D
      generalize C * 2 ^ n ^ k = D' at *
      generalize 2 ^ n ^ k = E at *
      generalize p.eval n = P at *
      omega
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      have hS := PEqualNP.Library.Machines.comp_time (fun x : List Bool => x)
        (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + j) true ++ false :: x)
        (fun y : List Bool => true :: y)
        _ (fun n => 2 * n + 3) (fun n => 2 ^ (n ^ k) + j + 1 + n) hc
        PEqualNP.Library.Helpers.consTrue_time (fun a b h => by dsimp; omega)
        (fun x => by simp; omega)
      refine ⟨c + 4 * j + 20, PEqualNP.Library.Machines.time_mono hS fun n => ?_⟩
      have e2 := hn n
      have e3 : (c + 4 * j + 20) * 2 ^ n ^ k = c * 2 ^ n ^ k + 4 * (j * 2 ^ n ^ k) +
          20 * 2 ^ n ^ k := by
        ring
      rw [e3]
      generalize c * 2 ^ n ^ k = D
      generalize j * 2 ^ n ^ k = D' at *
      generalize 2 ^ n ^ k = E at *
      omega
  exact key k
