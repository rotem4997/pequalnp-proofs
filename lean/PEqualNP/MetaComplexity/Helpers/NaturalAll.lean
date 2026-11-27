import PEqualNP.MetaComplexity.Helpers.Natural
import PEqualNP.Library.L086

/-!
# If MCSP is in P, one natural property is useful against every polynomial size

Helper for `L-meta-034` (proofs only, no statement may use it).

The property, for a threshold `B`, holds the tables of length at most `B` together with the
tables `T` whose instance `instA T` is not in MCSP. The instance is the table with the size
bound `T.length / 2 ^ (Nat.size T.length / 2)` in unary in front; on a table of length `2 ^ n`
the bound is `2 ^ (n / 2)`, which is above every polynomial in `n` and still far below the
`2 ^ n / (4 * n)` up to which the count of small circuits leaves half of all tables hard.

* Polynomial time: the bound is the length of the table halved `(n + 1) / 2` times, an
  iteration of a length-nonincreasing step; the count is half of the unary binary length that
  the instance map of `Helpers/Natural.lean` already computes.
* Useful against `n ^ k + k`, for every `k`, with a threshold depending on `k`.
* Large: by the count once `10 ≤ n`; below that every table is short and is a member.
-/

namespace PEqualNP.MetaComplexity.Helpers.NaturalAll

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Natural

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptA {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Arithmetic -/

theorem lin_le_pow (m : ℕ) (hm : 5 ≤ m) : 4 * m + 3 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem two_pow_half_sq (n : ℕ) : 2 ^ (n / 2) * 2 ^ (n / 2) ≤ 2 ^ n := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem two_pow_le_half_sq (n : ℕ) : 2 ^ n ≤ 2 * (2 ^ (n / 2) * 2 ^ (n / 2)) := by
  rw [← pow_add, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The two side conditions of the count, for the bound `2 ^ (n / 2)`. -/
theorem conds (n : ℕ) (hn : 10 ≤ n) :
    2 * (n + 2 ^ (n / 2) + 2) ≤ 2 ^ n ∧ 2 * n * 2 ^ (n / 2) + 2 * n + 1 ≤ 2 ^ n := by
  have hX := lin_le_pow (n / 2) (by omega)
  have hsq := two_pow_half_sq n
  have hnm : n ≤ 2 * (n / 2) + 1 := by omega
  have h1 : n * 2 ^ (n / 2) ≤ (2 * (n / 2) + 1) * 2 ^ (n / 2) := Nat.mul_le_mul_right _ hnm
  have h2 : (4 * (n / 2) + 3) * 2 ^ (n / 2) ≤ 2 ^ (n / 2) * 2 ^ (n / 2) :=
    Nat.mul_le_mul_right _ hX
  have h5 : 5 ≤ n / 2 := by omega
  constructor <;> nlinarith

/-- Every polynomial is eventually below `2 ^ (n / 2)`. -/
theorem poly_le (k : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ^ k + k ≤ 2 ^ (n / 2) := by
  obtain ⟨N, hN⟩ := growth (2 * k + 1)
  refine ⟨N + 1 + k, fun n hn => ?_⟩
  have hg := hN n (by omega)
  have hab : n ^ k + k ≤ (n + 1) ^ (k + 1) := by
    have h1 : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
    have h2 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    have h3 : n ≤ (n + 1) ^ k * n := Nat.le_mul_of_pos_left _ (by omega)
    have e : (n + 1) ^ (k + 1) = (n + 1) ^ k * n + (n + 1) ^ k := by rw [pow_succ]; ring
    omega
  have e2 : (n + 1) ^ (2 * k + 1 + 1) = (n + 1) ^ (k + 1) * (n + 1) ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e2] at hg
  have hsq := two_pow_le_half_sq n
  have hmul : (n ^ k + k) * (n ^ k + k) ≤ (n + 1) ^ (k + 1) * (n + 1) ^ (k + 1) :=
    Nat.mul_le_mul hab hab
  by_contra hlt
  have hlt' : 2 ^ (n / 2) < n ^ k + k := Nat.lt_of_not_le hlt
  have := Nat.mul_lt_mul'' hlt' hlt'
  omega

/-! ### The instance map -/

/-- The size bound attached to a table: its length halved `Nat.size length / 2` times. -/
def bnd (T : List Bool) : ℕ := T.length / 2 ^ (Nat.size T.length / 2)

/-- The MCSP instance attached to a table. -/
def instA (T : List Bool) : List Bool := List.replicate (bnd T) true ++ false :: T

theorem half_iter_un (e N : ℕ) : half^[e] (un N) = un (N / 2 ^ e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih, half_eq, un_length, Nat.div_div_eq_div_mul, pow_succ]

theorem hd_inst_one (T : List Bool) : hd (inst 1 T) = un (Nat.size T.length) := by
  have e : inst 1 T = un (Nat.size T.length) ++ false :: T := by simp [inst, bound, un]
  rw [e, hd_un]

/-- The instance map is polynomial-time computable. -/
theorem cpt_instA : CPT instA := by
  have hlen : CPT (fun T : List Bool => un T.length) :=
    cptA (PEqualNP.Library.L055 Polynomial.X) (fun T => by simp [un])
  have hsz : CPT (fun T : List Bool => hd (inst 1 T)) := cpt_comp (cpt_inst 1) cpt_hd
  have hcnt : CPT (fun T : List Bool => half (hd (inst 1 T))) := cpt_comp hsz cpt_half'
  have hit : CPT (fun T : List Bool => half^[(half (hd (inst 1 T))).length] (un T.length)) :=
    cpt_iterLen cpt_half' half_length_le hcnt hlen
  refine cptA (cpt_app2 hit (cpt_cons1 false cpt_id)) (fun T => ?_)
  rw [hd_inst_one, half_eq, un_length, un_length, half_iter_un]
  rfl

theorem bnd_table (n : ℕ) (T : List Bool) (hT : T.length = 2 ^ n) : bnd T = 2 ^ (n / 2) := by
  rw [bnd, hT, Nat.size_pow, Nat.pow_div (by omega) (by norm_num)]
  congr 1
  omega

/-- On a table of length `2 ^ n` the instance is in MCSP exactly when the table has a circuit
of size `2 ^ (n / 2)`. -/
theorem instA_mem (n : ℕ) (T : List Bool) (hT : T.length = 2 ^ n) :
    instA T ∈ MCSP ↔ HasCircuitSize n (tableFun n T) (2 ^ (n / 2)) := by
  have hb := bnd_table n T hT
  constructor
  · rintro ⟨n', s, T', h, hT', hC⟩
    rw [instA, hb] at h
    obtain ⟨hs, rfl⟩ := split_unique _ _ _ _ h
    have hn : n' = n := Nat.pow_right_injective (le_refl 2) (hT'.symm.trans hT)
    subst hn
    rw [← hs] at hC
    exact hC
  · intro h
    exact ⟨n, 2 ^ (n / 2), T, by rw [instA, hb], hT, h⟩

/-! ### The property -/

/-- The property: the tables of length at most `B`, and the tables whose instance is not in
MCSP. -/
def natA (B : ℕ) : Language Bool :=
  ({T : List Bool | T.drop B = []} : Language Bool) ⊔
    ({T : List Bool | instA T ∈ MCSP} : Language Bool)ᶜ

theorem mem_natA (B : ℕ) (T : List Bool) :
    T ∈ natA B ↔ T.length ≤ B ∨ instA T ∉ MCSP := by
  show (T.drop B = [] ∨ ¬ instA T ∈ MCSP) ↔ _
  rw [List.drop_eq_nil_iff]

/-- If MCSP is in P, the property is in P. -/
theorem natA_mem_P (h : MCSP ∈ P) (B : ℕ) : natA B ∈ P := by
  have hred : PolyTimeReducible ({T : List Bool | instA T ∈ MCSP} : Language Bool) MCSP :=
    ⟨instA, cpt_instA, fun _ => Iff.rfl⟩
  exact PEqualNP.Library.L047 _ _ (short_mem_P B)
    (PEqualNP.Library.L008 _ (PEqualNP.Library.L016 _ _ hred h))

/-- The property is useful against circuits of size `n ^ k + k`, for every `k`. -/
theorem natA_useful (n₀ k : ℕ) : UsefulAgainst (natA (2 ^ n₀)) (fun n : ℕ => n ^ k + k) := by
  obtain ⟨N, hN⟩ := poly_le k
  refine ⟨n₀ + 1 + N, fun n hn T hT hQ hC => ?_⟩
  rcases (mem_natA (2 ^ n₀) T).1 hQ with hlen | hmem
  · have : 2 ^ n₀ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact hmem ((instA_mem n T hT).2 (hasCircuitSize_mono (hN n (by omega)) hC))

/-- The property is large, with the threshold `2 ^ 9`. -/
theorem natA_large : Large (natA (2 ^ 9)) := by
  refine ⟨1, fun n => ?_⟩
  have hpos : 2 ≤ 2 ^ (1 * (n + 1)) := by
    rw [one_mul, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rcases Nat.lt_or_ge 9 n with hn | hn
  · obtain ⟨hb, hs⟩ := conds n (by omega)
    have hH := card_hard_tables n (2 ^ (n / 2)) hb hs
    have hsub : {T : List Bool | T.length = 2 ^ n ∧
          ¬ HasCircuitSize n (tableFun n T) (2 ^ (n / 2))} ⊆
        {T : List Bool | T.length = 2 ^ n ∧ T ∈ natA (2 ^ 9)} := by
      rintro T ⟨hT, hC⟩
      exact ⟨hT, (mem_natA (2 ^ 9) T).2 (Or.inr (fun hm => hC ((instA_mem n T hT).1 hm)))⟩
    have hle := Set.ncard_le_ncard hsub (finite_len (2 ^ n) _)
    calc 2 ^ (2 ^ n) ≤ 2 * {T : List Bool | T.length = 2 ^ n ∧
          ¬ HasCircuitSize n (tableFun n T) (2 ^ (n / 2))}.ncard := hH
      _ ≤ 2 ^ (1 * (n + 1)) * {T : List Bool | T.length = 2 ^ n ∧
          T ∈ natA (2 ^ 9)}.ncard := Nat.mul_le_mul hpos hle
  · have hsub : {T : List Bool | T.length = 2 ^ n} ⊆
        {T : List Bool | T.length = 2 ^ n ∧ T ∈ natA (2 ^ 9)} := by
      intro T hT
      have hT' : T.length = 2 ^ n := hT
      refine ⟨hT, (mem_natA (2 ^ 9) T).2 (Or.inl ?_)⟩
      rw [hT']
      exact Nat.pow_le_pow_right (by norm_num) hn
    have hle := Set.ncard_le_ncard hsub (finite_len (2 ^ n) _)
    rw [ncard_length_eq] at hle
    calc 2 ^ (2 ^ n) ≤ {T : List Bool | T.length = 2 ^ n ∧ T ∈ natA (2 ^ 9)}.ncard := hle
      _ ≤ 2 ^ (1 * (n + 1)) * {T : List Bool | T.length = 2 ^ n ∧
          T ∈ natA (2 ^ 9)}.ncard := Nat.le_mul_of_pos_left _ (by omega)

/-- If MCSP is in P then one property is large, in P, and useful against circuits of size
`n ^ k + k` for every `k`. -/
theorem natural_all_of_mcsp (h : MCSP ∈ P) :
    ∃ Q : Language Bool, Large Q ∧ Q ∈ P ∧
      ∀ k : ℕ, UsefulAgainst Q (fun n : ℕ => n ^ k + k) :=
  ⟨natA (2 ^ 9), natA_large, natA_mem_P h (2 ^ 9), natA_useful 9⟩

/-- If MCSP is in P there is no exponentially secure pseudorandom function in P, in the sense
of the hypothesis of `L-lib-086`. -/
theorem no_prf_of_mcsp (h : MCSP ∈ P) :
    ¬ ∃ F : Language Bool, ∃ k : ℕ, 0 < k ∧ F ∈ P ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 2 ^ (n / k) →
        |(({s : List Bool | s.length = n ∧ ∃ T : List Bool, T.length = 2 ^ n ∧
            (∀ i : ℕ, i < 2 ^ n → (T.getD i false = true ↔
              s ++ (List.range n).map (fun j : ℕ => i.testBit j) ∈ F)) ∧
            D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ (2 ^ n) -
          (({T : List Bool | T.length = 2 ^ n ∧ D.eval T = true}.ncard : ℕ) : ℤ) * 2 ^ n| *
            2 ^ (n / k) < 2 ^ n * 2 ^ (2 ^ n) :=
  fun hF => PEqualNP.Library.L086 hF (natural_all_of_mcsp h)

end PEqualNP.MetaComplexity.Helpers.NaturalAll
