import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.List
import PEqualNP.MetaComplexity.Helpers.Counting
import PEqualNP.MetaComplexity.Helpers.Hardwire
import PEqualNP.Library.Helpers.RRSeeded
import PEqualNP.Library.Universal.Padding
import PEqualNP.Library.L008
import PEqualNP.Library.L016
import PEqualNP.Library.L047
import PEqualNP.Library.L055

/-!
# If MCSP is in P there is a natural property against circuits of size `n ^ k`

Helper for `L-meta-008` (proofs only, no statement may use it).

The property, for a fixed `k` and a threshold `B`, holds the tables of length at most `B`
together with the tables `T` whose instance `inst k T` is not in MCSP. The instance is the
table with the size bound `(Nat.size T.length) ^ k` in unary in front; on a table of length
`2 ^ n` the bound is `(n + 1) ^ k`.

* Polynomial time: the instance map is polynomial-time computable (the binary length of the
  length by counting halvings, then a polynomial clock), so the second part reduces to the
  complement of MCSP; the first part is a length test.
* Useful: a member of length `2 ^ n > B` has no circuit of size `(n + 1) ^ k`, so none of size
  `n ^ k`.
* Large: at most `2 ^ (2 * n * s + 2 * n)` functions on `n` inputs have circuits of size `s`
  (the count behind `L-meta-002`), which is at most half of all functions once
  `4 * (n + 1) ^ (k + 1) ≤ 2 ^ n`. Below that point every table is short and is a member.
-/

namespace PEqualNP.MetaComplexity.Helpers.Natural

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptN {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### Counting -/

/-- At most `2 ^ (2 * n * s + 2 * n)` functions on `n` inputs have a circuit of size `s`. -/
theorem card_easy (n s : ℕ) (hb : 2 * (n + s + 2) ≤ 2 ^ n) :
    {f : (Fin n → Bool) → Bool | HasCircuitSize n f s}.ncard ≤ 2 ^ (2 * n * s + 2 * n) := by
  set B := n + s with hB
  let φ : (Σ t : Fin (s + 1), Code B t) → ((Fin n → Bool) → Bool) := fun p => sem n p.2
  have hsub : {f : (Fin n → Bool) → Bool | HasCircuitSize n f s} ⊆ Set.range φ := by
    intro f hf
    obtain ⟨t, c, hc⟩ := exists_code n s f hf
    exact ⟨⟨t, c⟩, hc⟩
  have h1 : {f : (Fin n → Bool) → Bool | HasCircuitSize n f s}.ncard ≤ (Set.range φ).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (Set.range φ).ncard ≤ Fintype.card (Σ t : Fin (s + 1), Code B t) := by
    rw [← Set.image_univ]
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have hg : 3 * ((B + 2) * (B + 2)) ≤ 2 ^ (2 * n) := by
    rw [pow_mul', sq]; nlinarith [Nat.mul_le_mul hb hb]
  have hterm : ∀ t : Fin (s + 1), Fintype.card (Code B t) ≤ (2 ^ (2 * n)) ^ s * (B + 1) := by
    intro t
    have e : Fintype.card (Code B t) = (3 * ((B + 2) * (B + 2))) ^ (t : ℕ) * (B + 1) := by
      simp [Code, GCode]
    rw [e]
    have h1 : 1 ≤ 3 * ((B + 2) * (B + 2)) := by nlinarith
    calc (3 * ((B + 2) * (B + 2))) ^ (t : ℕ) * (B + 1)
        ≤ (3 * ((B + 2) * (B + 2))) ^ s * (B + 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right h1 (by omega))
      _ ≤ (2 ^ (2 * n)) ^ s * (B + 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hg s)
  have hsum : Fintype.card (Σ t : Fin (s + 1), Code B t)
      ≤ (s + 1) * ((2 ^ (2 * n)) ^ s * (B + 1)) := by
    rw [Fintype.card_sigma]
    calc (Finset.univ.sum fun t : Fin (s + 1) => Fintype.card (Code B t))
        ≤ Finset.univ.sum fun _ : Fin (s + 1) => (2 ^ (2 * n)) ^ s * (B + 1) :=
          Finset.sum_le_sum (fun t _ => hterm t)
      _ = (s + 1) * ((2 ^ (2 * n)) ^ s * (B + 1)) := by simp
  have hsB : (s + 1) * (B + 1) ≤ (B + 2) * (B + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsb : (s + 1) * (B + 1) ≤ 2 ^ (2 * n) := by
    rw [pow_mul', sq]; nlinarith [Nat.mul_le_mul hb hb]
  calc {f : (Fin n → Bool) → Bool | HasCircuitSize n f s}.ncard
      ≤ (s + 1) * ((2 ^ (2 * n)) ^ s * (B + 1)) := h1.trans (h2.trans hsum)
    _ = (2 ^ (2 * n)) ^ s * ((s + 1) * (B + 1)) := by ring
    _ ≤ (2 ^ (2 * n)) ^ s * 2 ^ (2 * n) := Nat.mul_le_mul_left _ hsb
    _ = 2 ^ (2 * n * s + 2 * n) := by rw [← pow_mul, ← pow_add]

/-- Every position below `2 ^ n` is the table position of the input made of its bits. -/
theorem tableIndex_testBit {n j : ℕ} (hj : j < 2 ^ n) :
    tableIndex (fun i : Fin n => Nat.testBit j i) = j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [PEqualNP.Library.Helpers.RRSeeded.testBit_tableIndex]
  by_cases hi : i < n
  · simp [hi]
  · have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hj hp)]

/-- Two tables of length `2 ^ n` with the same function are equal. -/
theorem tableFun_injOn (n : ℕ) :
    Set.InjOn (tableFun n) {T : List Bool | T.length = 2 ^ n} := by
  intro T hT T' hT' h
  have hT1 : T.length = 2 ^ n := hT
  have hT2 : T'.length = 2 ^ n := hT'
  apply List.ext_getElem (hT1.trans hT2.symm)
  intro j h1 h2
  have hj : j < 2 ^ n := hT1 ▸ h1
  have := congrFun h (fun i : Fin n => Nat.testBit j i)
  simp only [tableFun, tableIndex_testBit hj] at this
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem finite_len (N : ℕ) (p : List Bool → Prop) :
    {T : List Bool | T.length = N ∧ p T}.Finite :=
  (List.finite_length_eq Bool N).subset fun _ hT => hT.1

theorem ncard_length_eq (L : ℕ) : {l : List Bool | l.length = L}.ncard = 2 ^ L := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card (List.Vector Bool L) = _
  simp

/-- At most `2 ^ (2 * n * s + 2 * n)` tables of length `2 ^ n` have a circuit of size `s`. -/
theorem card_easy_tables (n s : ℕ) (hb : 2 * (n + s + 2) ≤ 2 ^ n) :
    {T : List Bool | T.length = 2 ^ n ∧ HasCircuitSize n (tableFun n T) s}.ncard
      ≤ 2 ^ (2 * n * s + 2 * n) := by
  have inj : Set.InjOn (tableFun n)
      {T : List Bool | T.length = 2 ^ n ∧ HasCircuitSize n (tableFun n T) s} :=
    (tableFun_injOn n).mono (fun T h => h.1)
  rw [← inj.ncard_image]
  refine (Set.ncard_le_ncard ?_ (Set.toFinite _)).trans (card_easy n s hb)
  rintro _ ⟨T, hT, rfl⟩
  exact hT.2

/-- At least half of the tables of length `2 ^ n` have no circuit of size `s`, for small `s`. -/
theorem card_hard_tables (n s : ℕ) (hb : 2 * (n + s + 2) ≤ 2 ^ n)
    (hs : 2 * n * s + 2 * n + 1 ≤ 2 ^ n) :
    2 ^ (2 ^ n) ≤
      2 * {T : List Bool | T.length = 2 ^ n ∧ ¬ HasCircuitSize n (tableFun n T) s}.ncard := by
  have hall := ncard_length_eq (2 ^ n)
  have hunion : {T : List Bool | T.length = 2 ^ n} =
      {T : List Bool | T.length = 2 ^ n ∧ HasCircuitSize n (tableFun n T) s} ∪
        {T : List Bool | T.length = 2 ^ n ∧ ¬ HasCircuitSize n (tableFun n T) s} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  have hu := Set.ncard_union_le
    {T : List Bool | T.length = 2 ^ n ∧ HasCircuitSize n (tableFun n T) s}
    {T : List Bool | T.length = 2 ^ n ∧ ¬ HasCircuitSize n (tableFun n T) s}
  rw [← hunion, hall] at hu
  have hE := card_easy_tables n s hb
  have hp : 2 * 2 ^ (2 * n * s + 2 * n) ≤ 2 ^ (2 ^ n) := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hs
  linarith

/-- A polynomial is eventually below `2 ^ n`, in the form the count needs. -/
theorem growth (k : ℕ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → 4 * (n + 1) ^ (k + 1) ≤ 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt (k + 1) (by norm_num : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / 2 ^ (k + 3) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (ge_mem_nhds hε))
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n (by omega)
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_div_iff₀ hpos (by positivity), one_mul] at h1
  have h2 : n ^ (k + 1) * 2 ^ (k + 3) ≤ 2 ^ n := by exact_mod_cast h1
  have h3 : (n + 1) ^ (k + 1) ≤ (2 * n) ^ (k + 1) := Nat.pow_le_pow_left (by omega) _
  calc 4 * (n + 1) ^ (k + 1) ≤ 4 * (2 * n) ^ (k + 1) := by omega
    _ = n ^ (k + 1) * 2 ^ (k + 3) := by rw [mul_pow]; ring
    _ ≤ 2 ^ n := h2

/-- The two side conditions of the count, for the bound `(n + 1) ^ k`. -/
theorem growth_conds (k n : ℕ) (hn : 1 ≤ n) (h : 4 * (n + 1) ^ (k + 1) ≤ 2 ^ n) :
    2 * (n + (n + 1) ^ k + 2) ≤ 2 ^ n ∧ 2 * n * (n + 1) ^ k + 2 * n + 1 ≤ 2 ^ n := by
  have hs1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have e : (n + 1) ^ (k + 1) = n * (n + 1) ^ k + (n + 1) ^ k := by rw [pow_succ]; ring
  have hns : n ≤ n * (n + 1) ^ k := Nat.le_mul_of_pos_right _ (by omega)
  rw [e] at h
  constructor <;> linarith

/-! ### The instance map -/

/-- The size bound attached to a table: the binary length of its length, to the power `k`. -/
def bound (k : ℕ) (T : List Bool) : ℕ := (Nat.size T.length) ^ k

/-- The MCSP instance attached to a table. -/
def inst (k : ℕ) (T : List Bool) : List Bool := List.replicate (bound k T) true ++ false :: T

private theorem cpt_lgStep : CPT lgStep :=
  cptN (cpt_sel cpt_unpairB2 cpt_id
    (cpt_pairB2 (cpt_cons1 true cpt_unpairB1) (cpt_comp cpt_unpairB2 cpt_half')))
    (fun _ => rfl)

private theorem lgStep_length (s : List Bool) : (lgStep s).length ≤ s.length + 2 := by
  have h := unpairB_length s
  unfold lgStep sel
  split
  · omega
  · rename_i hne
    have h1 : 1 ≤ (unpairB s).2.length := by
      rcases hb : (unpairB s).2 with _ | ⟨b, l⟩
      · exact absurd hb hne
      · simp
    rw [pairB_length, half_eq, un_length, List.length_cons]
    omega

private theorem cpt_lgU {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => lgU (f s)) :=
  cptN (cpt_unpairB1_1 (cpt_iterGrow cpt_lgStep 2 lgStep_length hf
    (cpt_pairB2 (cpt_const []) hf))) (fun _ => rfl)

/-- The instance map is polynomial-time computable. -/
theorem cpt_inst (k : ℕ) : CPT (inst k) := by
  have hlen : CPT (fun T : List Bool => un T.length) :=
    cptN (PEqualNP.Library.L055 Polynomial.X) (fun T => by simp [un])
  have hlg : CPT (fun T : List Bool => lgU (un T.length)) := cpt_lgU hlen
  have hpow : CPT (fun T : List Bool =>
      List.replicate ((Polynomial.X ^ k : Polynomial ℕ).eval (lgU (un T.length)).length) true) :=
    cpt_comp hlg (PEqualNP.Library.L055 (Polynomial.X ^ k))
  refine cptN (cpt_app2 hpow (cpt_cons1 false cpt_id)) (fun T => ?_)
  simp [inst, bound, lgU_un]

/-- The split at the first `false` is unique. -/
theorem split_unique : ∀ (s s' : ℕ) (A B : List Bool),
    List.replicate s true ++ false :: A = List.replicate s' true ++ false :: B →
      s = s' ∧ A = B
  | 0, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.nil_append] at h
    exact ⟨rfl, (List.cons.inj h).2⟩
  | 0, s' + 1, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, s' + 1, A, B, h => by
    rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at h
    obtain ⟨h1, h2⟩ := split_unique s s' A B (List.cons.inj h).2
    exact ⟨by rw [h1], h2⟩

/-- On a table of length `2 ^ n` the instance is in MCSP exactly when the table has a circuit
of size `(n + 1) ^ k`. -/
theorem inst_mem (k n : ℕ) (T : List Bool) (hT : T.length = 2 ^ n) :
    inst k T ∈ MCSP ↔ HasCircuitSize n (tableFun n T) ((n + 1) ^ k) := by
  have hb : bound k T = (n + 1) ^ k := by simp [bound, hT, Nat.size_pow]
  constructor
  · rintro ⟨n', s, T', h, hT', hC⟩
    rw [inst, hb] at h
    obtain ⟨hs, rfl⟩ := split_unique _ _ _ _ h
    have hn : n' = n := Nat.pow_right_injective (le_refl 2) (hT'.symm.trans hT)
    subst hn
    rw [← hs] at hC
    exact hC
  · intro h
    exact ⟨n, (n + 1) ^ k, T, by rw [inst, hb], hT, h⟩

/-! ### The property -/

/-- The property: the tables of length at most `B`, and the tables whose instance is not in
MCSP. -/
def natQ (k B : ℕ) : Language Bool :=
  ({T : List Bool | T.drop B = []} : Language Bool) ⊔
    ({T : List Bool | inst k T ∈ MCSP} : Language Bool)ᶜ

theorem mem_natQ (k B : ℕ) (T : List Bool) :
    T ∈ natQ k B ↔ T.length ≤ B ∨ inst k T ∉ MCSP := by
  show (T.drop B = [] ∨ ¬ inst k T ∈ MCSP) ↔ _
  rw [List.drop_eq_nil_iff]

/-- The length test is in P. -/
theorem short_mem_P (B : ℕ) : ({T : List Bool | T.drop B = []} : Language Bool) ∈ P :=
  ⟨fun T => (T.drop B).isEmpty, fun T => by
      show T.drop B = [] ↔ _
      rw [List.isEmpty_iff],
    cpt_comp (cpt_drop B cpt_id) cpt_isEmpty⟩

/-- If MCSP is in P, the property is in P. -/
theorem natQ_mem_P (h : MCSP ∈ P) (k B : ℕ) : natQ k B ∈ P := by
  have hred : PolyTimeReducible ({T : List Bool | inst k T ∈ MCSP} : Language Bool) MCSP :=
    ⟨inst k, cpt_inst k, fun _ => Iff.rfl⟩
  exact PEqualNP.Library.L047 _ _ (short_mem_P B)
    (PEqualNP.Library.L008 _ (PEqualNP.Library.L016 _ _ hred h))

/-- The property is useful against circuits of size `n ^ k`, whatever the threshold. -/
theorem natQ_useful (k n₀ : ℕ) : UsefulAgainst (natQ k (2 ^ n₀)) (fun n : ℕ => n ^ k) := by
  refine ⟨n₀ + 1, fun n hn T hT hQ hC => ?_⟩
  rcases (mem_natQ k (2 ^ n₀) T).1 hQ with hlen | hmem
  · have : 2 ^ n₀ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact hmem ((inst_mem k n T hT).2
      (hasCircuitSize_mono (Nat.pow_le_pow_left (Nat.le_succ n) k) hC))

/-- The property is large, once the threshold is past the point where the count applies. -/
theorem natQ_large (k n₀ : ℕ) (hn₀ : ∀ n : ℕ, n₀ < n → 4 * (n + 1) ^ (k + 1) ≤ 2 ^ n) :
    Large (natQ k (2 ^ n₀)) := by
  refine ⟨1, fun n => ?_⟩
  have hpos : 2 ≤ 2 ^ (1 * (n + 1)) := by
    rw [one_mul, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rcases Nat.lt_or_ge n₀ n with hn | hn
  · obtain ⟨hb, hs⟩ := growth_conds k n (by omega) (hn₀ n hn)
    have hH := card_hard_tables n ((n + 1) ^ k) hb hs
    have hsub : {T : List Bool | T.length = 2 ^ n ∧
          ¬ HasCircuitSize n (tableFun n T) ((n + 1) ^ k)} ⊆
        {T : List Bool | T.length = 2 ^ n ∧ T ∈ natQ k (2 ^ n₀)} := by
      rintro T ⟨hT, hC⟩
      exact ⟨hT, (mem_natQ k (2 ^ n₀) T).2 (Or.inr (fun hm => hC ((inst_mem k n T hT).1 hm)))⟩
    have hle := Set.ncard_le_ncard hsub (finite_len (2 ^ n) _)
    calc 2 ^ (2 ^ n) ≤ 2 * {T : List Bool | T.length = 2 ^ n ∧
          ¬ HasCircuitSize n (tableFun n T) ((n + 1) ^ k)}.ncard := hH
      _ ≤ 2 ^ (1 * (n + 1)) * {T : List Bool | T.length = 2 ^ n ∧
          T ∈ natQ k (2 ^ n₀)}.ncard := Nat.mul_le_mul hpos hle
  · have hsub : {T : List Bool | T.length = 2 ^ n} ⊆
        {T : List Bool | T.length = 2 ^ n ∧ T ∈ natQ k (2 ^ n₀)} := by
      intro T hT
      have hT' : T.length = 2 ^ n := hT
      refine ⟨hT, (mem_natQ k (2 ^ n₀) T).2 (Or.inl ?_)⟩
      rw [hT']
      exact Nat.pow_le_pow_right (by norm_num) hn
    have hle := Set.ncard_le_ncard hsub (finite_len (2 ^ n) _)
    rw [ncard_length_eq] at hle
    calc 2 ^ (2 ^ n) ≤ {T : List Bool | T.length = 2 ^ n ∧ T ∈ natQ k (2 ^ n₀)}.ncard := hle
      _ ≤ 2 ^ (1 * (n + 1)) * {T : List Bool | T.length = 2 ^ n ∧
          T ∈ natQ k (2 ^ n₀)}.ncard := Nat.le_mul_of_pos_left _ (by omega)

/-- If MCSP is in P then for every `k` some property is in P, large, and useful against
circuits of size `n ^ k`. -/
theorem natural_of_mcsp (h : MCSP ∈ P) (k : ℕ) :
    ∃ Q : Language Bool, Q ∈ P ∧ Large Q ∧ UsefulAgainst Q (fun n : ℕ => n ^ k) := by
  obtain ⟨n₀, hn₀⟩ := growth k
  exact ⟨natQ k (2 ^ n₀), natQ_mem_P h k (2 ^ n₀), natQ_large k n₀ hn₀, natQ_useful k n₀⟩

end PEqualNP.MetaComplexity.Helpers.Natural
