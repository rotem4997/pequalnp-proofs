import PEqualNP.Library.L053
import PEqualNP.Library.L095
import PEqualNP.Library.L096
import PEqualNP.Library.L097
import PEqualNP.Library.L098
import PEqualNP.Library.L099
import PEqualNP.MetaComplexity.L024

/-!
# The assembly of L-meta-016, parametrised by the short-witness verifier

Helper module (proofs only, no statement may use it).

`chain016` proves: from a verifier for partial MCSP whose witness is short when the circuit is
small (the statement of L-meta-023, taken as a hypothesis), NP-hardness of partial MCSP gives a
language decided within `2 ^ (n ^ k) + k` steps outside NP ∩ P/poly.

Layers: pure facts (unique decomposition at the first `false`, the odd bits of the code of a
partial table, the parse of the bit language, two polynomial bounds), polynomial-time facts for
the parsing maps and the two tests, then the logical assembly.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
  PEqualNP.Library.Helpers PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.Machines

/-! ## Layer A: pure facts -/

/-- The decomposition of a string as a unary block, one `false`, and a rest is unique. -/
theorem pad_inj : ∀ {t t' : ℕ} {x x' : List Bool},
    List.replicate t true ++ false :: x = List.replicate t' true ++ false :: x' →
      t = t' ∧ x = x' := by
  intro t
  induction t with
  | zero =>
    intro t' x x' h
    cases t' with
    | zero => simpa using h
    | succ m => simp [List.replicate_succ] at h
  | succ n ih =>
    intro t' x x' h
    cases t' with
    | zero => simp [List.replicate_succ] at h
    | succ m =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by omega, h2⟩

/-- Dropping through the first `false` of a padded string leaves the rest. -/
theorem dropN_pad (s : ℕ) (e : List Bool) :
    dropN (List.replicate s true ++ false :: e) = e := by
  simp [dropN]

/-- The code of a partial table has two bits per entry. -/
theorem length_encodePartial (T : List (Option Bool)) :
    (encodePartial T).length = 2 * T.length := by
  induction T with
  | nil => rfl
  | cons o T ih =>
    have e : encodePartial (o :: T) =
        (match o with
          | none => [false, false]
          | some b => [true, b]) ++ encodePartial T := rfl
    rw [e, List.length_append, ih]
    rcases o with _ | b <;> simp <;> omega

/-- The bit at position `2 * j + 1` of the code of a partial table is `true` exactly when entry
`j` is defined as `true` (for every `j`, also out of range). -/
theorem encodePartial_getD (T : List (Option Bool)) : ∀ j : ℕ,
    ((encodePartial T).getD (2 * j + 1) false = true ↔ T.getD j none = some true) := by
  induction T with
  | nil => intro j; simp [encodePartial]
  | cons o T ih =>
    intro j
    have e : encodePartial (o :: T) =
        (match o with
          | none => [false, false]
          | some b => [true, b]) ++ encodePartial T := rfl
    cases j with
    | zero => rcases o with _ | b <;> simp [e]
    | succ j =>
      have e2 : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
      rw [e, e2]
      rcases o with _ | b
      · simpa using ih j
      · simpa using ih j

/-- The exponential pad of the NEXP relation with exponent `k`. -/
def padK (k : ℕ) (x : List Bool) : List Bool :=
  List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x

/-- The suffix of an input of the bit language: it carries `x` and is read from the end. -/
def tailC (x : List Bool) : List Bool :=
  x.reverse ++ false :: List.replicate x.length true

/-- The `x` part of an input of the bit language. -/
def bitU (z : List Bool) : List Bool := (unpairB z.reverse).1

/-- The index part of an input of the bit language. -/
def bitV (z : List Bool) : List Bool := (unpairB z.reverse).2.reverse

theorem reverse_app_tailC (i x : List Bool) :
    (i ++ tailC x).reverse = pairB x i.reverse := by
  simp [tailC, pairB, un]

theorem bitU_app (i x : List Bool) : bitU (i ++ tailC x) = x := by
  unfold bitU
  rw [reverse_app_tailC, unpairB_pairB]

theorem bitV_app (i x : List Bool) : bitV (i ++ tailC x) = i := by
  unfold bitV
  rw [reverse_app_tailC, unpairB_pairB]
  exact List.reverse_reverse i

theorem length_tailC (x : List Bool) : (tailC x).length = 2 * x.length + 1 := by
  simp [tailC]; omega

/-- The test of the bit language: the bit of the table part of `r y` at position `2 * j + 1`,
where `j` is the binary value of the index. -/
def bitTest (r : List Bool → List Bool) (p : List Bool × List Bool) : Bool :=
  (dropN (r p.1)).getD
    (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0
      (true :: p.2)) false

theorem bitTest_spec (r : List Bool → List Bool) (y i : List Bool) (s : ℕ)
    (T : List (Option Bool))
    (e : r y = List.replicate s true ++ false :: encodePartial T) :
    bitTest r (y, i) = true ↔
      T.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i)
        none = some true := by
  have h := encodePartial_getD T
    (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i)
  have e1 : bitTest r (y, i) = (encodePartial T).getD
      (2 * List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i + 1)
      false := by
    simp [bitTest, e, dropN_pad]
  rw [e1]
  exact h

/-- The number of inputs of an instance produced from an exponentially padded string is
polynomial in the length of the unpadded string. -/
theorem n_bound (q : Polynomial ℕ) (k : ℕ) : ∃ N : Polynomial ℕ, ∀ n m : ℕ,
    2 ^ n ≤ q.eval (2 ^ (m ^ k) + k + 1 + m) → n ≤ N.eval m := by
  have h1 : ExpBound (fun m : ℕ => 2 ^ (m ^ k) + k + 1 + m) :=
    eb_add (eb_add (eb_add (eb_two_pow 1 1 k (f := fun m => m) (fun m => by simp))
      (eb_const k)) (eb_const 1)) eb_id
  obtain ⟨A, D, hAD⟩ := eb_poly q h1
  refine ⟨Polynomial.C A * (Polynomial.X + 1) ^ D, fun n m h => ?_⟩
  have h2 : 2 ^ n ≤ 2 ^ (A * (m + 1) ^ D) := h.trans (hAD m)
  have h3 : n ≤ A * (m + 1) ^ D := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  simpa using h3

/-- One polynomial bounds the witness length. -/
theorem pw_exists (a : ℕ) (N Q : Polynomial ℕ) : ∃ pw : Polynomial ℕ, ∀ n m : ℕ,
    n ≤ N.eval m → a * (n + (Q.eval (n + (2 * m + 1)) + 1) + 1) ^ 2 ≤ pw.eval m := by
  refine ⟨Polynomial.C a *
    (N + (Q.comp (N + Polynomial.C 2 * Polynomial.X + 1) + 1) + 1) ^ 2, fun n m h => ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_one]
  have h1 : Q.eval (n + (2 * m + 1)) ≤ Q.eval (N.eval m + 2 * m + 1) :=
    eval_mono Q (by omega)
  exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) 2)

/-! ## Layer B: polynomial-time facts -/

theorem cpt_bitU :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bitU :=
  PEqualNP.MetaComplexity.Helpers.Machines.cpt_congr
    (cpt_comp PEqualNP.Library.L099 cpt_unpairB1) (fun _ => rfl)

theorem cpt_bitV :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bitV :=
  PEqualNP.MetaComplexity.Helpers.Machines.cpt_congr
    (cpt_comp (cpt_comp PEqualNP.Library.L099 cpt_unpairB2) PEqualNP.Library.L099)
    (fun _ => rfl)

theorem cpt_bitTest {r : List Bool → List Bool}
    (hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r) :
    ComputableInPolyTime encodePair Computability.encodeBool (bitTest r) :=
  PEqualNP.MetaComplexity.Helpers.Machines.cpt_congr
    (cpt_comp
      (pair_prod (cpt_comp cpt_fst (cpt_comp hr cpt_dropN))
        (cpt_comp cpt_snd (cpt_app2 (cpt_const [true]) cpt_id)))
      PEqualNP.Library.L098)
    (fun _ => rfl)

theorem cpt_verTest {r : List Bool → List Bool} {fV : List Bool × List Bool → Bool}
    (hr : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r)
    (hf : ComputableInPolyTime encodePair Computability.encodeBool fV) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => fV (r p.1, p.2)) :=
  cpt_comp (cpt_first hr) hf

/-! ## Layer C: the assembly -/

/-- The assembly of L-meta-016 from the short-witness verifier of partial MCSP. -/
theorem chain016
    (hV : ∃ (V : Set (List Bool × List Bool)) (a : ℕ), PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair V ∧ (∀ y c : List Bool, (y, c) ∈ V → y ∈ PEqualNP.MetaComplexity.PartialMCSP) ∧ ∀ (n s t : ℕ) (T : List (Option Bool)) (f : (Fin n → Bool) → Bool), T.length = 2 ^ n → PEqualNP.MetaComplexity.Consistent n T f → PEqualNP.MetaComplexity.HasCircuitSize n f t → t ≤ s → ∃ c : List Bool, c.length ≤ a * (n + t + 1) ^ 2 ∧ (List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T, c) ∈ V) :
    PEqualNP.Library.NPHard PEqualNP.MetaComplexity.PartialMCSP → ∃ L : Language Bool, (∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) ∧ ¬ (L ∈ PEqualNP.Library.NP ∧ L ∈ PEqualNP.CircuitLowerBounds.PPoly) := by
  intro hH
  by_contra hno
  have hAll : ∀ L : Language Bool,
      (∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) →
        L ∈ PEqualNP.Library.NP ∧ L ∈ PEqualNP.CircuitLowerBounds.PPoly := by
    intro L hL
    by_contra h
    exact hno ⟨L, hL, h⟩
  -- Step 1: a language in NEXP outside NP.
  obtain ⟨D, hDX, hDN⟩ := Set.exists_of_ssubset PEqualNP.Library.L053
  obtain ⟨RL, k, hRL, hD⟩ := hDX
  -- Step 2: the padded language reduces to partial MCSP.
  obtain ⟨r, hr, hred⟩ := hH _ (PEqualNP.Library.L096 RL hRL)
  have hDR : ∀ x : List Bool, x ∈ D ↔ r (padK k x) ∈ PartialMCSP := by
    intro x
    rw [← hred, hD]
    constructor
    · rintro ⟨w, hw, hxw⟩
      exact ⟨_, x, w, rfl, hw, hxw⟩
    · rintro ⟨t, x', w, e, hw, hxw⟩
      obtain ⟨h1, h2⟩ := pad_inj e
      subst h1
      subst h2
      exact ⟨w, hw, hxw⟩
  obtain ⟨V, a, ⟨fV, hfV, cfV⟩, hsound, hshort⟩ := hV
  -- Step 3: the language of valid witnesses is decided in exponential time, so it is in NP.
  have hE : ({z : List Bool | fV (r (padK k (unpairB z).1), (unpairB z).2) = true} :
      Language Bool) ∈ PEqualNP.Library.NP := by
    obtain ⟨j, hj⟩ := PEqualNP.Library.L095 k (fun z => (unpairB z).1) (fun z => (unpairB z).2)
      (fun p : List Bool × List Bool => fV (r p.1, p.2)) cpt_unpairB1 cpt_unpairB2
      (cpt_verTest hr cfV)
    exact (hAll _ ⟨j, fun z => fV (r (padK k (unpairB z).1), (unpairB z).2),
      fun z => Iff.rfl, hj⟩).1
  -- Step 4: the bit language is decided in exponential time, so it has small circuits.
  have hB : ({z : List Bool | bitTest r (padK k (bitU z), bitV z) = true} :
      Language Bool) ∈ PEqualNP.CircuitLowerBounds.PPoly := by
    obtain ⟨j, hj⟩ := PEqualNP.Library.L095 k bitU bitV (bitTest r) cpt_bitU cpt_bitV
      (cpt_bitTest hr)
    exact (hAll _ ⟨j, fun z => bitTest r (padK k (bitU z), bitV z),
      fun z => Iff.rfl, hj⟩).2
  obtain ⟨Q, hQ⟩ := hB
  -- Step 6 (the bounds): the polynomials.
  obtain ⟨q, hq⟩ := output_length_poly r hr
  obtain ⟨N, hN⟩ := n_bound q k
  obtain ⟨pw, hpw⟩ := pw_exists a N Q
  -- Step 5: every member of `D` has a short witness.
  have hwit : ∀ x : List Bool, x ∈ D →
      ∃ c : List Bool, c.length ≤ pw.eval x.length ∧ (r (padK k x), c) ∈ V := by
    intro x hx
    obtain ⟨n, s, T, e, hlen, f, hcons, hsize⟩ := (hDR x).1 hx
    have hg : HasCircuitSize n
        (fun y : Fin n → Bool => decide (T.getD (tableIndex y) none = some true))
        (Q.eval (n + (tailC x).length) + 1) := by
      refine PEqualNP.MetaComplexity.L024 _ Q n T (tailC x) hQ (fun i _ => ?_)
      show bitTest r (padK k (bitU (i ++ tailC x)), bitV (i ++ tailC x)) = true ↔ _
      rw [bitU_app, bitV_app]
      exact bitTest_spec r _ i s T e
    have hgc : Consistent n T
        (fun y : Fin n → Bool => decide (T.getD (tableIndex y) none = some true)) := by
      intro y b hb
      show decide (T.getD (tableIndex y) none = some true) = b
      rw [hb]
      cases b <;> simp
    rw [length_tailC] at hg
    have hn : n ≤ N.eval x.length := by
      refine hN n x.length ?_
      have h1 := hq (padK k x)
      have h2 : (padK k x).length = 2 ^ (x.length ^ k) + k + 1 + x.length := by
        simp [padK]; omega
      have h3 : (r (padK k x)).length = s + (1 + 2 * 2 ^ n) := by
        rw [e]
        simp [length_encodePartial, hlen]
        omega
      rw [h2] at h1
      omega
    have hbound := hpw n x.length hn
    rcases le_total s (Q.eval (n + (2 * x.length + 1)) + 1) with h | h
    · obtain ⟨c, hc, hm⟩ := hshort n s s T f hlen hcons hsize le_rfl
      refine ⟨c, (hc.trans ?_).trans hbound, by rw [e]; exact hm⟩
      exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) 2)
    · obtain ⟨c, hc, hm⟩ := hshort n s _ T _ hlen hgc hg h
      exact ⟨c, hc.trans hbound, by rw [e]; exact hm⟩
  -- Step 7: `D` is a polynomially bounded projection of an NP language.
  have hDeq : D = ({x : List Bool | ∃ c : List Bool, c.length ≤ pw.eval x.length ∧
      (fun p : List Bool × List Bool => pairB p.1 p.2) (x, c) ∈
        ({z : List Bool | fV (r (padK k (unpairB z).1), (unpairB z).2) = true} :
          Language Bool)} : Language Bool) := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc, hm⟩ := hwit x hx
      refine ⟨c, hc, ?_⟩
      show fV (r (padK k (unpairB (pairB x c)).1), (unpairB (pairB x c)).2) = true
      rw [unpairB_pairB]
      exact (hfV _).1 hm
    · rintro ⟨c, _, hc⟩
      have hc' : fV (r (padK k (unpairB (pairB x c)).1), (unpairB (pairB x c)).2) = true := hc
      rw [unpairB_pairB] at hc'
      exact (hDR x).2 (hsound _ _ ((hfV _).2 hc'))
  apply hDN
  rw [hDeq]
  exact PEqualNP.Library.L097 _ (fun p : List Bool × List Bool => pairB p.1 p.2) pw hE cpt_pairB

end PEqualNP.MetaComplexity.Helpers
