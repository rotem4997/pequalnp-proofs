import PEqualNP.Library.Machines.Clock
import PEqualNP.Library.Machines.ConstList
import PEqualNP.Library.Machines.ComposeTime
import PEqualNP.Library.Helpers.ExpDoubling
import PEqualNP.Library.Helpers.PolyBelowExp

/-- For `k ≥ 1`, `2 ^ (|x| ^ k)` ones can be written within `c * 2 ^ (n ^ k) + c` steps. -/
theorem PEqualNP.Library.L083 : ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true) (fun n : ℕ => c * 2 ^ (n ^ k) + c) := by
  intro k hk
  have h1 := PEqualNP.Library.Machines.clock_polyTime
    PEqualNP.Library.Machines.constList_polyTime (Polynomial.X ^ k)
  obtain ⟨p, hp⟩ := PEqualNP.Library.Machines.time_of_polyTime h1
  obtain ⟨C, hC⟩ := PEqualNP.Library.Helpers.polynomial_le_two_pow_pow_add_const p k hk
  have h := PEqualNP.Library.Machines.comp_time (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate ((Polynomial.X ^ k : Polynomial ℕ).eval x.length) true)
    (fun x : List Bool => List.replicate (2 ^ x.length) true)
    (fun n => p.eval n) PEqualNP.Library.Helpers.dblTime (fun n => n ^ k)
    hp PEqualNP.Library.Helpers.dbl_time PEqualNP.Library.Helpers.dblTime_mono
    (fun a => by simp)
  simp only [List.length_replicate, Polynomial.eval_pow, Polynomial.eval_X] at h
  refine ⟨C + 10, PEqualNP.Library.Machines.time_mono h fun n => ?_⟩
  have e1 := hC n
  have e2 : n ^ k < 2 ^ (n ^ k) := Nat.lt_two_pow_self
  have e3 : (C + 10) * 2 ^ n ^ k = C * 2 ^ n ^ k + 10 * 2 ^ n ^ k := by ring
  simp only [PEqualNP.Library.Helpers.dblTime]
  rw [e3]
  generalize C * 2 ^ n ^ k = D
  generalize 2 ^ n ^ k = E at *
  generalize n ^ k = N at *
  omega
