import Mathlib
import PEqualNP.Defs

/-!
Helper module, proofs only: the approximation of constant-depth circuits by low-degree
polynomials over a prime field (Razborov 1987, Smolensky 1987).

A circuit over AND, OR, NOT and MOD `p` gates, with `s` gates and depth `d` on `n` inputs,
agrees with a polynomial over `ZMod p` of total degree at most `((p - 1) * l) ^ d` on all
points of the cube but at most `s * 2 ^ n / 2 ^ l`. The random choice of subsets in the usual
proof is a count over all choices here. The interface is `Helpers.approx`, the last theorem.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.Approx

open PEqualNP.CircuitLowerBounds

variable {p : ℕ} [Fact p.Prime]

/-- For a nonzero vector, at most half of the subsets of the index set have sum zero: toggling
a coordinate where the vector is nonzero changes the sum. -/
theorem half_subsets {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ZMod p) (hv : v ≠ 0) :
    (Finset.univ.filter fun S : Finset ι => ∑ j ∈ S, v j = 0).card * 2 ≤
      2 ^ Fintype.card ι := by
  obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  set Z := Finset.univ.filter fun S : Finset ι => ∑ j ∈ S, v j = 0 with hZ
  have h1 : Z.card ≤ Zᶜ.card := by
    apply Finset.card_le_card_of_injOn (fun S => symmDiff S {j0})
    · intro S hS
      have hS0 : ∑ j ∈ S, v j = 0 := by simpa [hZ] using hS
      have : ∑ j ∈ symmDiff S {j0}, v j ≠ 0 := by
        by_cases hj : j0 ∈ S
        · have e : symmDiff S {j0} = S.erase j0 := by
            ext a; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
            constructor
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact ⟨h2, h1⟩
              · exact absurd (h1 ▸ hj) h2
            · rintro ⟨h1, h2⟩; exact Or.inl ⟨h2, h1⟩
          rw [e, Finset.sum_erase_eq_sub hj, hS0, zero_sub]
          exact neg_ne_zero.2 hj0
        · have e : symmDiff S {j0} = insert j0 S := by
            ext a; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
            constructor
            · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
              · exact Or.inr h1
              · exact Or.inl h1
            · rintro (h1 | h1)
              · exact Or.inr ⟨h1, h1 ▸ hj⟩
              · exact Or.inl ⟨h1, fun h => hj (h ▸ h1)⟩
          rw [e, Finset.sum_insert hj, hS0, add_zero]
          exact hj0
      simpa [hZ] using this
    · intro S _ T _ h
      exact symmDiff_left_injective _ h
  have h2 : Z.card + Zᶜ.card = 2 ^ Fintype.card ι := by
    rw [Finset.card_add_card_compl, Fintype.card_finset]
  omega

/-- One OR gate, as a count: for any family of vectors `y x`, some choice of `l` subsets makes
`1 - ∏ (1 - (sum over the subset) ^ (p - 1))` the indicator of `y x ≠ 0` on all points but at
most a `2 ^ -l` fraction. -/
theorem gate_approx {X ι : Type} [Fintype X] [Fintype ι] [DecidableEq ι]
    (y : X → ι → ZMod p) (l : ℕ) :
    ∃ S : Fin l → Finset ι,
      (Finset.univ.filter fun x : X =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1).card * 2 ^ l ≤ Fintype.card X := by
  classical
  have hp1 : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  set N := Fintype.card (Fin l → Finset ι) with hN
  have hNval : N = (2 ^ Fintype.card ι) ^ l := by
    rw [hN, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
  -- per point, few choices are bad
  have hpoint : ∀ x : X,
      (Finset.univ.filter fun S : Fin l → Finset ι =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1).card * 2 ^ l ≤ N := by
    intro x
    by_cases hy : y x = 0
    · have : (Finset.univ.filter fun S : Fin l → Finset ι =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1) = ∅ := by
        apply Finset.filter_false_of_mem
        intro S _
        simp [hy, hp1]
      rw [this]
      simp
    · set Z := Finset.univ.filter fun S : Finset ι => ∑ j ∈ S, y x j = 0 with hZ
      have hsub : (Finset.univ.filter fun S : Fin l → Finset ι =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1) ⊆ Fintype.piFinset (fun _ : Fin l => Z) := by
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg hy] at hS
        rw [Fintype.mem_piFinset]
        intro i
        by_contra hi
        have hi' : ∑ j ∈ S i, y x j ≠ 0 := by simpa [hZ] using hi
        apply hS
        rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (by rw [ZMod.pow_card_sub_one_eq_one hi', sub_self]), sub_zero]
      calc _ ≤ (Fintype.piFinset (fun _ : Fin l => Z)).card * 2 ^ l :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ = (Z.card * 2) ^ l := by
            rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              mul_pow]
        _ ≤ N := by
            rw [hNval]
            exact Nat.pow_le_pow_left (half_subsets (y x) hy) l
  by_contra hcon
  push Not at hcon
  have hsum : ∑ _S : Fin l → Finset ι, Fintype.card X <
      ∑ S : Fin l → Finset ι, (Finset.univ.filter fun x : X =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1).card * 2 ^ l :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun S _ => hcon S)
  have hswap : ∑ S : Fin l → Finset ι, (Finset.univ.filter fun x : X =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1).card * 2 ^ l =
      ∑ x : X, (Finset.univ.filter fun S : Fin l → Finset ι =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1).card * 2 ^ l := by
    simp only [Finset.card_filter, Finset.sum_mul]
    exact Finset.sum_comm
  have hle : ∑ x : X, (Finset.univ.filter fun S : Fin l → Finset ι =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, y x j) ^ (p - 1)) : ZMod p) ≠
          if y x = 0 then 0 else 1).card * 2 ^ l ≤ ∑ _x : X, N :=
    Finset.sum_le_sum (fun x _ => hpoint x)
  rw [hswap] at hsum
  have := lt_of_lt_of_le hsum hle
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  rw [← hN, mul_comm] at this
  exact lt_irrefl _ this

/-- A bit as an element of the field. -/
def bit (p : ℕ) (b : Bool) : ZMod p := if b = true then 1 else 0

/-- A point of the cube as a point over the field. -/
def pt (p : ℕ) {n : ℕ} (x : Fin n → Bool) : Fin n → ZMod p :=
  fun i => if x i = true then 1 else 0

theorem bit_eq_zero (b : Bool) : bit p b = 0 ↔ b = false := by
  cases b <;> simp [bit]

theorem bit_eq_one (b : Bool) : bit p b = 1 ↔ b = true := by
  cases b <;> simp [bit]

theorem deg_one_sub {n : ℕ} (a : MvPolynomial (Fin n) (ZMod p)) :
    (1 - a).totalDegree ≤ a.totalDegree :=
  le_trans (MvPolynomial.totalDegree_sub _ _) (by simp)

theorem deg_list_sum {n : ℕ} (L : List ℕ) (F : ℕ → MvPolynomial (Fin n) (ZMod p)) (D : ℕ)
    (h : ∀ i ∈ L, (F i).totalDegree ≤ D) : (L.map F).sum.totalDegree ≤ D := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (h a (by simp)) (ih fun i hi => h i (by simp [hi])))

theorem sum_bits (L : List ℕ) (f : ℕ → ZMod p) (b : ℕ → Bool)
    (h : ∀ i ∈ L, f i = bit p (b i)) :
    (L.map f).sum = (((L.map b).count true : ℕ) : ZMod p) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons]
    rw [h a (by simp), ih fun i hi => h i (by simp [hi])]
    cases b a <;> simp [bit, add_comm]

theorem getD_snoc_ne {α : Type} (L : List α) (a d : α) (i : ℕ) (h : i ≠ L.length) :
    (L ++ [a]).getD i d = L.getD i d := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem le_foldr_max (L : List ℕ) (a : ℕ) (h : a ∈ L) : a ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The OR of polynomials, approximately: a polynomial that is the indicator of "some `G j` is
nonzero" outside a small set of points. -/
theorem or_poly {n : ℕ} (l k : ℕ) (G : Fin k → MvPolynomial (Fin n) (ZMod p)) (Dg : ℕ)
    (hG : ∀ j, (G j).totalDegree ≤ Dg) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod p)) (E : Finset (Fin n → Bool)),
      Q.totalDegree ≤ l * ((p - 1) * Dg) ∧ E.card * 2 ^ l ≤ 2 ^ n ∧
      ∀ x, x ∉ E → MvPolynomial.eval (pt p x) Q =
        if (∀ j, MvPolynomial.eval (pt p x) (G j) = 0) then 0 else 1 := by
  classical
  obtain ⟨S, hS⟩ := gate_approx (p := p)
    (fun (x : Fin n → Bool) (j : Fin k) => MvPolynomial.eval (pt p x) (G j)) l
  refine ⟨1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, G j) ^ (p - 1)),
    (Finset.univ.filter fun x : Fin n → Bool =>
        (1 - ∏ i : Fin l, (1 - (∑ j ∈ S i, MvPolynomial.eval (pt p x) (G j)) ^ (p - 1)) :
          ZMod p) ≠
          if (fun j => MvPolynomial.eval (pt p x) (G j)) = 0 then 0 else 1), ?_, ?_, ?_⟩
  rotate_left
  · simpa using hS
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
    simp only [map_sub, map_one, map_prod, map_pow, map_sum]
    rw [hx]
    simp [funext_iff]
  · refine le_trans (deg_one_sub _) ?_
    refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
    calc ∑ i : Fin l, (1 - (∑ j ∈ S i, G j) ^ (p - 1)).totalDegree
        ≤ ∑ _i : Fin l, (p - 1) * Dg := Finset.sum_le_sum (fun i _ => ?_)
      _ = l * ((p - 1) * Dg) := by simp
    refine le_trans (deg_one_sub _) ?_
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    exact Nat.mul_le_mul_left _ (MvPolynomial.totalDegree_finsetSum_le (fun j _ => hG j))

/-- One gate: from polynomials for the wires it reads, a polynomial for its value, of degree
larger by the factor `(p - 1) * l`, right outside a small set of points wherever the
polynomials it reads are right. -/
theorem gate_poly {n : ℕ} (l : ℕ) (hl : 1 ≤ l) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp))
    (F : ℕ → MvPolynomial (Fin n) (ZMod p)) (Dg : ℕ)
    (hF : ∀ i ∈ g.inputs, (F i).totalDegree ≤ Dg) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod p)) (E : Finset (Fin n → Bool)),
      Q.totalDegree ≤ l * ((p - 1) * Dg) ∧ E.card * 2 ^ l ≤ 2 ^ n ∧
      ∀ x, x ∉ E → ∀ w : List Bool,
        (∀ i ∈ g.inputs, MvPolynomial.eval (pt p x) (F i) = bit p (w.getD i false)) →
        MvPolynomial.eval (pt p x) Q =
          bit p (g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  classical
  obtain ⟨op, inputs⟩ := g
  have hp1 : 1 ≤ p - 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hmono : ∀ a : ℕ, a ≤ l * ((p - 1) * a) := fun a => by
    calc a = 1 * (1 * a) := by ring
      _ ≤ l * ((p - 1) * a) := Nat.mul_le_mul hl (Nat.mul_le_mul hp1 le_rfl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hF ⊢
  rcases hop with rfl | rfl | rfl | rfl
  · -- AND
    obtain ⟨Q, E, hQ, hE, hv⟩ := or_poly (p := p) l inputs.length
      (fun j => 1 - F (inputs.get j)) Dg
      (fun j => le_trans (deg_one_sub _) (hF _ (List.get_mem _ _)))
    refine ⟨1 - Q, E, le_trans (deg_one_sub _) hQ, hE, ?_⟩
    intro x hx w hw
    rw [map_sub, map_one, hv x hx]
    have key : (∀ j : Fin inputs.length,
        MvPolynomial.eval (pt p x) (1 - F (inputs.get j)) = 0) ↔
        ∀ i ∈ inputs, w.getD i false = true := by
      constructor
      · intro h i hi
        obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hi
        have := h j
        rw [map_sub, map_one, hw _ (List.get_mem _ _), sub_eq_zero] at this
        exact (bit_eq_one _).1 this.symm
      · intro h j
        rw [map_sub, map_one, hw _ (List.get_mem _ _), h _ (List.get_mem _ _)]
        simp [bit]
    by_cases hc : ∀ i ∈ inputs, w.getD i false = true
    · rw [if_pos (key.2 hc)]
      have : GateOp.and.eval (inputs.map fun i => w.getD i false) = true := by
        simpa [GateOp.eval] using hc
      rw [this]; simp [bit]
    · rw [if_neg (mt key.1 hc)]
      have : GateOp.and.eval (inputs.map fun i => w.getD i false) = false := by
        rw [← Bool.not_eq_true]
        simpa [GateOp.eval] using hc
      rw [this]; simp [bit]
  · -- OR
    obtain ⟨Q, E, hQ, hE, hv⟩ := or_poly (p := p) l inputs.length
      (fun j => F (inputs.get j)) Dg (fun j => hF _ (List.get_mem _ _))
    refine ⟨Q, E, hQ, hE, ?_⟩
    intro x hx w hw
    rw [hv x hx]
    have key : (∀ j : Fin inputs.length,
        MvPolynomial.eval (pt p x) (F (inputs.get j)) = 0) ↔
        ∀ i ∈ inputs, w.getD i false = false := by
      constructor
      · intro h i hi
        obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hi
        have := h j
        rw [hw _ (List.get_mem _ _)] at this
        exact (bit_eq_zero _).1 this
      · intro h j
        rw [hw _ (List.get_mem _ _), h _ (List.get_mem _ _)]
        simp [bit]
    by_cases hc : ∀ i ∈ inputs, w.getD i false = false
    · rw [if_pos (key.2 hc)]
      have : GateOp.or.eval (inputs.map fun i => w.getD i false) = false := by
        simpa [GateOp.eval] using hc
      rw [this]; simp [bit]
    · rw [if_neg (mt key.1 hc)]
      have : GateOp.or.eval (inputs.map fun i => w.getD i false) = true := by
        rw [← Bool.not_eq_false]
        simpa [GateOp.eval] using hc
      rw [this]; simp [bit]
  · -- NOT
    cases inputs with
    | nil => exact ⟨1, ∅, by simp, by simp, fun x _ w _ => by simp [GateOp.eval, bit]⟩
    | cons i t =>
      refine ⟨1 - F i, ∅, le_trans (deg_one_sub _) (le_trans (hF i (by simp)) (hmono _)),
        by simp, ?_⟩
      intro x _ w hw
      rw [map_sub, map_one, hw i (by simp)]
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      cases w.getD i false <;> simp [bit]
  · -- MOD p
    refine ⟨1 - ((inputs.map F).sum) ^ (p - 1), ∅, ?_, by simp, ?_⟩
    · refine le_trans (deg_one_sub _) (le_trans (MvPolynomial.totalDegree_pow _ _) ?_)
      exact le_trans (Nat.mul_le_mul_left _ (deg_list_sum _ _ _ hF))
        (Nat.le_mul_of_pos_left _ hl)
    · intro x _ w hw
      have hsum : MvPolynomial.eval (pt p x) (inputs.map F).sum =
          (((inputs.map fun i => w.getD i false).count true : ℕ) : ZMod p) := by
        rw [map_list_sum, List.map_map]
        exact sum_bits inputs _ _ hw
      rw [map_sub, map_one, map_pow, hsum]
      simp only [GateOp.eval]
      set c := (inputs.map fun i => w.getD i false).count true
      by_cases hc : c % p = 0
      · have h0 : ((c : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff c p).2 (Nat.dvd_of_mod_eq_zero hc)
        rw [h0, zero_pow (by omega)]
        simp [bit, hc]
      · have h0 : ((c : ℕ) : ZMod p) ≠ 0 := fun h =>
          hc (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff c p).1 h))
        rw [ZMod.pow_card_sub_one_eq_one h0]
        simp [bit, hc]

/-- The invariant of the induction over the gates: `ws x` are the wire values so far on the
point `x`, `ds` the wire depths so far, `m` the number of gates so far. Every wire index has a
polynomial of degree at most `((p - 1) * l) ^ depth`, and outside one set of at most
`m * 2 ^ n / 2 ^ l` points every polynomial takes the value of its wire. Indices past the
last wire carry the zero polynomial, as a missing wire reads `false` at depth `0`. -/
def Approximated (p n l : ℕ) (ws : (Fin n → Bool) → List Bool) (ds : List ℕ) (m : ℕ) : Prop :=
  ∃ (N : ℕ) (F : ℕ → MvPolynomial (Fin n) (ZMod p)) (E : Finset (Fin n → Bool)),
    ds.length = N ∧ (∀ x, (ws x).length = N) ∧
    (∀ i, (F i).totalDegree ≤ ((p - 1) * l) ^ ds.getD i 0) ∧
    E.card * 2 ^ l ≤ m * 2 ^ n ∧
    ∀ x, x ∉ E → ∀ i, MvPolynomial.eval (pt p x) (F i) = bit p ((ws x).getD i false)

theorem approximated_step {n l : ℕ} (hl : 1 ≤ l) (ws : (Fin n → Bool) → List Bool)
    (ds : List ℕ) (m : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp))
    (h : Approximated p n l ws ds m) :
    Approximated p n l
      (fun x => ws x ++ [g.op.eval (g.inputs.map fun i => (ws x).getD i false)])
      (ds ++ [(g.inputs.map fun i => ds.getD i 0).foldr max 0 + 1]) (m + 1) := by
  classical
  obtain ⟨N, F, E, rfl, hw, hdeg, hE, hval⟩ := h
  have hB : 1 ≤ (p - 1) * l := by
    have := (Fact.out : p.Prime).two_le
    exact Nat.mul_pos (by omega) hl
  obtain ⟨Q, E', hQ, hE', hQv⟩ := gate_poly (p := p) l hl g hop F
    (((p - 1) * l) ^ (g.inputs.map fun i => ds.getD i 0).foldr max 0) (fun i hi =>
      le_trans (hdeg i) (Nat.pow_le_pow_right hB
        (le_foldr_max _ _ (List.mem_map.2 ⟨i, hi, rfl⟩))))
  refine ⟨ds.length + 1, Function.update F ds.length Q, E ∪ E', by simp,
    fun x => by simp [hw x], ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = ds.length
    · rw [hi, Function.update_self, getD_snoc_eq, pow_succ]
      refine le_trans hQ (le_of_eq ?_)
      ring
    · rw [Function.update_of_ne hi, getD_snoc_ne _ _ _ _ hi]
      exact hdeg i
  · have := Nat.mul_le_mul_right (2 ^ l) (Finset.card_union_le E E')
    rw [add_mul] at this
    rw [add_mul, one_mul]
    omega
  · intro x hx i
    rw [Finset.mem_union, not_or] at hx
    by_cases hi : i = ds.length
    · rw [hi, Function.update_self, ← hw x, getD_snoc_eq]
      exact hQv x hx.2 (ws x) (fun i _ => hval x hx.1 i)
    · rw [Function.update_of_ne hi, getD_snoc_ne _ _ _ _ (by rw [hw x]; exact hi)]
      exact hval x hx.1 i

theorem approximated_fold {n l : ℕ} (hl : 1 ≤ l) (gs : List Gate)
    (hgs : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp)) :
    ∀ (ws : (Fin n → Bool) → List Bool) (ds : List ℕ) (m : ℕ), Approximated p n l ws ds m →
      Approximated p n l
        (fun x => gs.foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (ws x))
        (gs.foldl
          (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1]) ds)
        (m + gs.length) := by
  induction gs with
  | nil => intro ws ds m h; simpa using h
  | cons g gs ih =>
    intro ws ds m h
    have := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ _
      (approximated_step hl ws ds m g (hgs g (by simp)) h)
    have e : m + (g :: gs).length = m + 1 + gs.length := by
      rw [List.length_cons]; omega
    rw [e]
    exact this

theorem approximated_inputs (n l : ℕ) :
    Approximated p n l (fun x => List.ofFn x) (List.replicate n 0) 0 := by
  refine ⟨n, fun i => if h : i < n then MvPolynomial.X ⟨i, h⟩ else 0, ∅, by simp,
    fun x => by simp, ?_, by simp, ?_⟩
  · intro i
    have : (List.replicate n 0).getD i 0 = 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [this, pow_zero]
    by_cases h : i < n
    · simp [h]
    · simp [h]
  · intro x _ i
    by_cases h : i < n
    · simp [h, pt, bit, List.getD_eq_getElem?_getD]
    · simp [h, bit, List.getD_eq_getElem?_getD]

end PEqualNP.CircuitLowerBounds.Helpers.Approx

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

/-- The approximation of circuits by polynomials (Razborov 1987, Smolensky 1987): a circuit
over AND, OR, NOT and MOD `p`, `p` prime, with at most `s` gates and of depth at most `d` on
`n` inputs agrees with a polynomial over `ZMod p` of total degree at most `((p - 1) * l) ^ d`
on all points of the cube but at most `s * 2 ^ n / 2 ^ l`. -/
theorem approx : ∀ (p : ℕ), Nat.Prime p → ∀ (n s d l : ℕ) (C : Circuit),
    (∀ g ∈ C.gates,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp)) →
    C.size ≤ s → C.depth n ≤ d → 1 ≤ l →
    ∃ P : MvPolynomial (Fin n) (ZMod p), P.totalDegree ≤ ((p - 1) * l) ^ d ∧
      (Finset.univ.filter fun x : Fin n → Bool =>
        MvPolynomial.eval (fun i => if x i = true then (1 : ZMod p) else 0) P ≠
          (if C.eval (List.ofFn x) = true then (1 : ZMod p) else 0)).card * 2 ^ l ≤
        s * 2 ^ n := by
  intro p hp n s d l C hC hs hd hl
  have := Fact.mk hp
  obtain ⟨N, F, E, -, -, hdeg, hE, hval⟩ :=
    Approx.approximated_fold (p := p) (n := n) hl C.gates hC _ _ 0 (Approx.approximated_inputs n l)
  have hB : 1 ≤ (p - 1) * l := Nat.mul_pos (by have := hp.two_le; omega) hl
  refine ⟨F C.output, le_trans (hdeg C.output) (Nat.pow_le_pow_right hB hd), ?_⟩
  have hsub : (Finset.univ.filter fun x : Fin n → Bool =>
        MvPolynomial.eval (fun i => if x i = true then (1 : ZMod p) else 0) (F C.output) ≠
          (if C.eval (List.ofFn x) = true then (1 : ZMod p) else 0)) ⊆ E := by
    intro x hx
    by_contra hxE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx (hval x hxE C.output)
  calc _ ≤ E.card * 2 ^ l := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (0 + C.gates.length) * 2 ^ n := hE
    _ ≤ s * 2 ^ n := Nat.mul_le_mul_right _ (by simpa [Circuit.size] using hs)

end PEqualNP.CircuitLowerBounds.Helpers
