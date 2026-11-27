import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9662

open PEqualNP.Search PEqualNP.ProofComplexity

-- A lower bound for cutting planes refutations of any CNF F with N test points pt i and a
-- fractional point Y / s. Each clause line of F is false at no more than one test point, and
-- every clause line has deficiency at most 0 at the fractional point. Then every refutation has at
-- least 2 N + 1 lines: N clause lines (each test point is falsified by the final line, and a line
-- can only be false at a test point when an ancestor clause line is), N - 1 additions or
-- multiplications (a union count over sets of lines), one division (without one every line holds
-- at the fractional point), and one more line: with a single division every line has deficiency
-- below s, so the final line, whose deficiency is s, needs a further addition or a second division.

section Gen

variable {V : Type} [Fintype V] [DecidableEq V]

def lhs (a : V → Bool) (e : CPLine V) : ℤ := ∑ v, e.1 v * (if a v then 1 else 0)

def holdsB (a : V → Bool) (e : CPLine V) : Bool := decide (e.2 ≤ lhs a e)

def viol {ι : Type} [Fintype ι] (pt : ι → V → Bool) (e : CPLine V) : Finset ι :=
  Finset.univ.filter (fun i => holdsB (pt i) e = false)

def dfc (s : ℤ) (Y : V → ℤ) (e : CPLine V) : ℤ := s * e.2 - ∑ v, e.1 v * Y v

theorem mem_viol {ι : Type} [Fintype ι] (pt : ι → V → Bool) (e : CPLine V) (i : ι) :
    i ∈ viol pt e ↔ lhs (pt i) e < e.2 := by
  simp [viol, holdsB]

theorem lhs_add (a : V → Bool) (e e' : CPLine V) :
    lhs a (e.1 + e'.1, e.2 + e'.2) = lhs a e + lhs a e' := by
  simp only [lhs, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem lhs_mul (a : V → Bool) (e : CPLine V) (k : ℕ) :
    lhs a ((k : ℤ) • e.1, (k : ℤ) * e.2) = k * lhs a e := by
  simp only [lhs, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem lhs_div (a : V → Bool) (e : CPLine V) (d : ℕ) (hd : ∀ v, (d : ℤ) ∣ e.1 v) :
    lhs a (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) * d = lhs a e := by
  simp only [lhs, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_right_comm, Int.ediv_mul_cancel (hd v)]

theorem viol_add {ι : Type} [Fintype ι] [DecidableEq ι] (pt : ι → V → Bool) (e e' : CPLine V) :
    viol pt (e.1 + e'.1, e.2 + e'.2) ⊆ viol pt e ∪ viol pt e' := by
  intro i hi
  rw [mem_viol, lhs_add] at hi
  rw [Finset.mem_union, mem_viol, mem_viol]
  by_contra h
  push_neg at h
  dsimp only at hi
  omega

theorem viol_mul {ι : Type} [Fintype ι] (pt : ι → V → Bool) (e : CPLine V) (k : ℕ) :
    viol pt ((k : ℤ) • e.1, (k : ℤ) * e.2) ⊆ viol pt e := by
  intro i hi
  rw [mem_viol, lhs_mul] at hi
  rw [mem_viol]
  by_contra h
  push_neg at h
  dsimp only at hi
  have := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg k)
  omega

theorem viol_div {ι : Type} [Fintype ι] (pt : ι → V → Bool) (e : CPLine V) (d : ℕ) (hd0 : 0 < d)
    (hd : ∀ v, (d : ℤ) ∣ e.1 v) :
    viol pt (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) ⊆ viol pt e := by
  intro i hi
  rw [mem_viol] at hi
  rw [mem_viol]
  by_contra h
  push_neg at h
  have hm := lhs_div (pt i) e d hd
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd0
  have key : -(lhs (pt i) (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ)))) ≤ (-e.2) / (d : ℤ) := by
    apply Int.le_ediv_of_mul_le hdz
    linarith
  dsimp only at hi
  omega

theorem viol_boolLo {ι : Type} [Fintype ι] (pt : ι → V → Bool) (v : V) :
    viol pt ((fun u => if u = v then 1 else 0, 0) : CPLine V) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  rw [mem_viol] at hi
  simp only [lhs, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hi
  split at hi <;> omega

theorem viol_boolHi {ι : Type} [Fintype ι] (pt : ι → V → Bool) (v : V) :
    viol pt ((fun u => if u = v then -1 else 0, -1) : CPLine V) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  rw [mem_viol] at hi
  simp only [lhs, ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hi
  split at hi <;> omega

theorem viol_bot {ι : Type} [Fintype ι] (pt : ι → V → Bool) :
    viol pt (((0 : V → ℤ), (1 : ℤ)) : CPLine V) = Finset.univ := by
  ext i
  simp [mem_viol, lhs]

theorem dfc_add (s : ℤ) (Y : V → ℤ) (e e' : CPLine V) :
    dfc s Y (e.1 + e'.1, e.2 + e'.2) = dfc s Y e + dfc s Y e' := by
  simp only [dfc, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem dfc_mul (s : ℤ) (Y : V → ℤ) (e : CPLine V) (k : ℕ) :
    dfc s Y ((k : ℤ) • e.1, (k : ℤ) * e.2) = k * dfc s Y e := by
  simp only [dfc, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem dfc_div (s : ℤ) (hs : 0 < s) (Y : V → ℤ) (e : CPLine V) (d : ℕ) (hd0 : 0 < d)
    (hd : ∀ v, (d : ℤ) ∣ e.1 v) :
    (d : ℤ) * dfc s Y (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) ≤ dfc s Y e + s * (d - 1) := by
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd0
  have hsum : (d : ℤ) * ∑ v, e.1 v / (d : ℤ) * Y v = ∑ v, e.1 v * Y v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← mul_assoc, mul_comm (d : ℤ), Int.ediv_mul_cancel (hd v)]
  have hq := Int.mul_ediv_add_emod (-e.2) (d : ℤ)
  have hr0 := Int.emod_nonneg (-e.2) (ne_of_gt hdz)
  have hr1 := Int.emod_lt_of_pos (-e.2) hdz
  have hc : (d : ℤ) * (-((-e.2) / (d : ℤ))) ≤ e.2 + (d - 1) := by nlinarith
  simp only [dfc]
  rw [mul_sub, hsum]
  nlinarith

theorem dfc_bot (s : ℤ) (Y : V → ℤ) : dfc s Y (((0 : V → ℤ), (1 : ℤ)) : CPLine V) = s := by
  simp [dfc]

theorem ind_le_one {p : Prop} [Decidable p] : (if p then 1 else 0 : ℕ) ≤ 1 := by
  split_ifs <;> simp

theorem ind_mono {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    (if p then 1 else 0 : ℕ) ≤ if q then 1 else 0 := by
  split_ifs <;> simp_all

theorem erase_mem {π : List (CPLine V)} {z : CPLine V} {E : Finset (CPLine V)}
    (hEm : ∀ f ∈ E, f ∈ z :: π) {f : CPLine V} (hf : f ∈ E.erase z) : f ∈ π := by
  rcases List.mem_cons.1 (hEm f (Finset.mem_of_mem_erase hf)) with h | h
  · exact absurd h (Finset.ne_of_mem_erase hf)
  · exact h

theorem sub_parents {ι : Type} [Fintype ι] [DecidableEq ι] (pt : ι → V → Bool) {z : CPLine V}
    {E P : Finset (CPLine V)} (hz : z ∈ E) (hv : viol pt z ⊆ P.biUnion (viol pt)) :
    E.biUnion (viol pt) ⊆ (E.erase z ∪ P).biUnion (viol pt) := by
  intro i hi
  obtain ⟨f, hf, hi⟩ := Finset.mem_biUnion.1 hi
  by_cases hfz : f = z
  · subst hfz
    obtain ⟨g, hg, hi⟩ := Finset.mem_biUnion.1 (hv hi)
    exact Finset.mem_biUnion.2 ⟨g, Finset.mem_union_right _ hg, hi⟩
  · exact Finset.mem_biUnion.2 ⟨f, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hfz, hf⟩), hi⟩

-- A leaf line (a clause line or a Boolean bound): false at no more than one test point, deficiency <= 0.
theorem leaf_step {ι : Type} [Fintype ι] [DecidableEq ι] (pt : ι → V → Bool) (s : ℤ) (Y : V → ℤ)
    (π : List (CPLine V)) (z : CPLine V) (a dv : ℕ)
    (hE : ∀ E : Finset (CPLine V), (∀ e ∈ E, e ∈ π) →
      (E.biUnion (viol pt)).card + (if dv ≤ 1 ∧ s ≤ ∑ e ∈ E, dfc s Y e then 1 else 0) ≤ E.card + a)
    (hz : (viol pt z).card ≤ 1) (hd : dfc s Y z ≤ 0) :
    ∀ E : Finset (CPLine V), (∀ e ∈ E, e ∈ z :: π) →
      (E.biUnion (viol pt)).card + (if dv ≤ 1 ∧ s ≤ ∑ e ∈ E, dfc s Y e then 1 else 0) ≤ E.card + a := by
  intro E hEm
  by_cases hzE : z ∈ E
  · have h0 := hE (E.erase z) fun f hf => erase_mem hEm hf
    have hu : E.biUnion (viol pt) ⊆ (E.erase z).biUnion (viol pt) ∪ viol pt z := by
      intro i hi
      obtain ⟨f, hf, hi⟩ := Finset.mem_biUnion.1 hi
      by_cases hfz : f = z
      · subst hfz; exact Finset.mem_union_right _ hi
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨f, Finset.mem_erase.2 ⟨hfz, hf⟩, hi⟩)
    have hc := (Finset.card_le_card hu).trans (Finset.card_union_le _ _)
    have hs : ∑ e ∈ E, dfc s Y e ≤ ∑ e ∈ E.erase z, dfc s Y e := by
      rw [← Finset.sum_erase_add _ _ hzE]; linarith
    have hi : (if dv ≤ 1 ∧ s ≤ ∑ e ∈ E, dfc s Y e then 1 else 0) ≤
        (if dv ≤ 1 ∧ s ≤ ∑ e ∈ E.erase z, dfc s Y e then 1 else 0) :=
      ind_mono fun h => ⟨h.1, h.2.trans hs⟩
    have := Finset.card_erase_add_one hzE
    omega
  · exact hE E fun f hf => by
      rcases List.mem_cons.1 (hEm f hf) with rfl | h
      · exact absurd hf hzE
      · exact h

-- The invariant, by induction on the derivation (newest line first).
theorem inv {F : Set (Clause V)} {ι : Type} [Fintype ι] [DecidableEq ι] (pt : ι → V → Bool)
    (s : ℤ) (hs : 0 < s) (Y : V → ℤ) (hY : ∀ v, 0 ≤ Y v ∧ Y v ≤ s)
    (hax : ∀ C ∈ F, (viol pt (clauseCP C)).card ≤ 1) (hdf : ∀ C ∈ F, dfc s Y (clauseCP C) ≤ 0) :
    ∀ π : List (CPLine V), IsCPDerivation F π → ∃ nax a dv : ℕ, ∃ U : Finset ι,
      nax + a + dv ≤ π.length ∧ U.card ≤ nax ∧ (∀ e ∈ π, viol pt e ⊆ U) ∧
      (dv = 0 → ∀ e ∈ π, dfc s Y e ≤ 0) ∧
      ∀ E : Finset (CPLine V), (∀ e ∈ E, e ∈ π) →
        (E.biUnion (viol pt)).card + (if dv ≤ 1 ∧ s ≤ ∑ e ∈ E, dfc s Y e then 1 else 0)
          ≤ E.card + a := by
  intro π h
  induction h with
  | nil =>
    refine ⟨0, 0, 0, ∅, by simp, by simp, by simp, by simp, fun E hE => ?_⟩
    have : E = ∅ := Finset.eq_empty_of_forall_notMem fun e he => by simpa using hE e he
    subst this
    simpa using hs
  | @ax π C hπ hC ih =>
    obtain ⟨nax, a, dv, U, hlen, hU, hvU, hdv, hE⟩ := ih
    refine ⟨nax + 1, a, dv, U ∪ viol pt (clauseCP C), by simp; omega,
      (Finset.card_union_le _ _).trans (by have := hax C hC; omega), ?_, ?_,
      leaf_step pt s Y π _ a dv hE (hax C hC) (hdf C hC)⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Finset.subset_union_right
      · exact (hvU e he).trans Finset.subset_union_left
    · intro h0 e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hdf C hC
      · exact hdv h0 e he
  | @boolLo π v hπ ih =>
    obtain ⟨nax, a, dv, U, hlen, hU, hvU, hdv, hE⟩ := ih
    refine ⟨nax, a, dv, U, by simp; omega, hU, ?_, ?_,
      leaf_step pt s Y π _ a dv hE (by rw [viol_boolLo]; simp) (by simp [dfc]; exact (hY v).1)⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · rw [viol_boolLo]; exact Finset.empty_subset _
      · exact hvU e he
    · intro h0 e he
      rcases List.mem_cons.1 he with rfl | he
      · simp [dfc]; exact (hY v).1
      · exact hdv h0 e he
  | @boolHi π v hπ ih =>
    obtain ⟨nax, a, dv, U, hlen, hU, hvU, hdv, hE⟩ := ih
    refine ⟨nax, a, dv, U, by simp; omega, hU, ?_, ?_,
      leaf_step pt s Y π _ a dv hE (by rw [viol_boolHi]; simp) (by simp [dfc]; linarith [(hY v).2])⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · rw [viol_boolHi]; exact Finset.empty_subset _
      · exact hvU e he
    · intro h0 e he
      rcases List.mem_cons.1 he with rfl | he
      · simp [dfc]; linarith [(hY v).2]
      · exact hdv h0 e he
  | @add π e e' hπ he he' ih =>
    obtain ⟨nax, a, dv, U, hlen, hU, hvU, hdv, hE⟩ := ih
    refine ⟨nax, a + 1, dv, U, by simp; omega, hU, ?_, ?_, ?_⟩
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact (viol_add pt e e').trans (Finset.union_subset (hvU e he) (hvU e' he'))
      · exact hvU f hf
    · intro h0 f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [dfc_add]; linarith [hdv h0 e he, hdv h0 e' he']
      · exact hdv h0 f hf
    · intro E hEm
      by_cases hz : (e.1 + e'.1, e.2 + e'.2) ∈ E
      · set z : CPLine V := (e.1 + e'.1, e.2 + e'.2)
        have hsub := sub_parents pt hz (P := {e, e'}) (by
          intro i hi
          rcases Finset.mem_union.1 (viol_add pt e e' hi) with h | h
          · exact Finset.mem_biUnion.2 ⟨e, by simp, h⟩
          · exact Finset.mem_biUnion.2 ⟨e', by simp, h⟩)
        have hE' := hE (E.erase z ∪ {e, e'}) (by
          intro f hf
          rcases Finset.mem_union.1 hf with hf | hf
          · exact erase_mem hEm hf
          · rcases Finset.mem_insert.1 hf with rfl | hf
            · exact he
            · rw [Finset.mem_singleton.1 hf]; exact he')
        have hcU := Finset.card_le_card hsub
        have hcE : (E.erase z ∪ {e, e'}).card ≤ E.card + 1 := by
          have h1 := Finset.card_union_le (E.erase z) {e, e'}
          have h2 : ({e, e'} : Finset (CPLine V)).card ≤ 2 := Finset.card_le_two
          have h3 := Finset.card_erase_add_one hz
          omega
        by_cases hle : (E.erase z ∪ {e, e'}).card ≤ E.card
        · have := ind_le_one (p := dv ≤ 1 ∧ s ≤ ∑ f ∈ E, dfc s Y f)
          have := Nat.zero_le (if dv ≤ 1 ∧ s ≤ ∑ f ∈ E.erase z ∪ {e, e'}, dfc s Y f then 1 else 0)
          omega
        · have hsum : ∑ f ∈ E, dfc s Y f = ∑ f ∈ E.erase z ∪ {e, e'}, dfc s Y f := by
            have h1 := Finset.card_union_add_card_inter (E.erase z) {e, e'}
            have h2 : ({e, e'} : Finset (CPLine V)).card ≤ 2 := Finset.card_le_two
            have h3 := Finset.card_erase_add_one hz
            have hP : ({e, e'} : Finset (CPLine V)).card = 2 := by omega
            have hI : (E.erase z ∩ {e, e'}).card = 0 := by omega
            have hne : e ≠ e' := by
              intro h; rw [h] at hP; simp at hP
            rw [Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.card_eq_zero.1 hI)),
              Finset.sum_pair hne, ← Finset.sum_erase_add _ _ hz, dfc_add]
          rw [hsum]
          omega
      · have := hE E (fun f hf => by
          rcases List.mem_cons.1 (hEm f hf) with rfl | h
          · exact absurd hf hz
          · exact h)
        omega
  | @mul π e k hπ he ih =>
    obtain ⟨nax, a, dv, U, hlen, hU, hvU, hdv, hE⟩ := ih
    refine ⟨nax, a + 1, dv, U, by simp; omega, hU, ?_, ?_, ?_⟩
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact (viol_mul pt e k).trans (hvU e he)
      · exact hvU f hf
    · intro h0 f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [dfc_mul]; exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg k) (hdv h0 e he)
      · exact hdv h0 f hf
    · intro E hEm
      by_cases hz : ((k : ℤ) • e.1, (k : ℤ) * e.2) ∈ E
      · set z : CPLine V := ((k : ℤ) • e.1, (k : ℤ) * e.2)
        have hsub := sub_parents pt hz (P := {e}) (by
          intro i hi; exact Finset.mem_biUnion.2 ⟨e, by simp, viol_mul pt e k hi⟩)
        have hE' := hE (E.erase z ∪ {e}) (by
          intro f hf
          rcases Finset.mem_union.1 hf with hf | hf
          · exact erase_mem hEm hf
          · rw [Finset.mem_singleton.1 hf]; exact he)
        have hcU := Finset.card_le_card hsub
        have hcE : (E.erase z ∪ {e}).card ≤ E.card := by
          have h1 := Finset.card_union_le (E.erase z) {e}
          have h3 := Finset.card_erase_add_one hz
          rw [Finset.card_singleton] at h1; omega
        have := ind_le_one (p := dv ≤ 1 ∧ s ≤ ∑ f ∈ E, dfc s Y f)
        omega
      · have := hE E (fun f hf => by
          rcases List.mem_cons.1 (hEm f hf) with rfl | h
          · exact absurd hf hz
          · exact h)
        omega
  | @div π e d hπ he hd0 hd ih =>
    obtain ⟨nax, a, dv, U, hlen, hU, hvU, hdv, hE⟩ := ih
    refine ⟨nax, a, dv + 1, U, by simp; omega, hU, ?_, by simp, ?_⟩
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact (viol_div pt e d hd0 hd).trans (hvU e he)
      · exact hvU f hf
    · intro E hEm
      by_cases hz : ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) : CPLine V) ∈ E
      · set z : CPLine V := (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ)))
        have hsub := sub_parents pt hz (P := {e}) (by
          intro i hi; exact Finset.mem_biUnion.2 ⟨e, by simp, viol_div pt e d hd0 hd hi⟩)
        have hE' := hE (E.erase z ∪ {e}) (by
          intro f hf
          rcases Finset.mem_union.1 hf with hf | hf
          · exact erase_mem hEm hf
          · rw [Finset.mem_singleton.1 hf]; exact he)
        have hcU := Finset.card_le_card hsub
        have hcE : (E.erase z ∪ {e}).card ≤ E.card := by
          have h1 := Finset.card_union_le (E.erase z) {e}
          have h3 := Finset.card_erase_add_one hz
          rw [Finset.card_singleton] at h1; omega
        have h0 : (if dv + 1 ≤ 1 ∧ s ≤ ∑ f ∈ E, dfc s Y f then 1 else 0) = 0 := by
          rw [if_neg]
          rintro ⟨h1, h2⟩
          have hdv0 : dv = 0 := by omega
          have hold : ∑ f ∈ E.erase z, dfc s Y f ≤ 0 :=
            Finset.sum_nonpos fun f hf => hdv hdv0 f (erase_mem hEm hf)
          have hdz := dfc_div s hs Y e d hd0 hd
          have hde := hdv hdv0 e he
          have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd0
          have hlt : dfc s Y z < s := by
            by_contra hc
            push_neg at hc
            have : (d : ℤ) * s ≤ (d : ℤ) * dfc s Y z := mul_le_mul_of_nonneg_left hc (by omega)
            nlinarith
          rw [← Finset.sum_erase_add _ _ hz] at h2
          linarith
        rw [h0]
        have := Nat.zero_le (if dv ≤ 1 ∧ s ≤ ∑ f ∈ E.erase z ∪ {e}, dfc s Y f then 1 else 0)
        omega
      · have := hE E (fun f hf => by
          rcases List.mem_cons.1 (hEm f hf) with rfl | h
          · exact absurd hf hz
          · exact h)
        have : (if dv + 1 ≤ 1 ∧ s ≤ ∑ f ∈ E, dfc s Y f then 1 else 0) ≤
            (if dv ≤ 1 ∧ s ≤ ∑ f ∈ E, dfc s Y f then 1 else 0) :=
          ind_mono fun h => ⟨by omega, h.2⟩
        omega

theorem lower {F : Set (Clause V)} {ι : Type} [Fintype ι] [DecidableEq ι] (pt : ι → V → Bool)
    (s : ℤ) (hs : 0 < s) (Y : V → ℤ) (hY : ∀ v, 0 ≤ Y v ∧ Y v ≤ s)
    (hax : ∀ C ∈ F, (viol pt (clauseCP C)).card ≤ 1) (hdf : ∀ C ∈ F, dfc s Y (clauseCP C) ≤ 0)
    (π : List (CPLine V)) (h : IsCPRefutation F π) : 2 * Fintype.card ι + 1 ≤ π.length := by
  obtain ⟨nax, a, dv, U, hlen, hU, hvU, hdv, hE⟩ := inv pt s hs Y hY hax hdf π h.1
  have hf := h.2
  have h1 : Fintype.card ι ≤ U.card := by
    have := hvU _ hf
    rw [viol_bot] at this
    simpa using Finset.card_le_card this
  have h2 : dv ≠ 0 := by
    intro h0
    have := hdv h0 _ hf
    rw [dfc_bot] at this
    omega
  have h3 := hE {((0 : V → ℤ), (1 : ℤ))} (by simpa using hf)
  rw [Finset.singleton_biUnion, viol_bot, Finset.sum_singleton, dfc_bot] at h3
  simp only [Finset.card_univ, Finset.card_singleton, le_refl, and_true] at h3
  split_ifs at h3 with hc <;> omega

end Gen

-- The instance: one test point per clause of PHP (2 + 1) 2, falsifying that clause only (bit
-- 2 * i + j: pigeon i sits in hole j; the point of a pigeon clause leaves that pigeon out and puts
-- the others one per hole; the point of a hole clause puts both pigeons in that hole and the
-- others one per remaining hole), and the fractional point 1 / 2 everywhere (Y = 1, s = 2).

def codes : List ℕ := [36, 33, 9, 37, 25, 22, 26, 38, 41]

def pt (i : Fin 9) (v : Fin (2 + 1) × Fin 2) : Bool := (codes.getD i 0).testBit (2 * v.1.val + v.2.val)

theorem hax : ∀ C ∈ PHP (2 + 1) 2, (viol pt (clauseCP C)).card ≤ 1 := by
  rintro C (⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩)
  · revert i
    decide +kernel
  · revert i i' j hne
    decide +kernel

theorem hdf : ∀ C ∈ PHP (2 + 1) 2, dfc 2 (fun _ => 1) (clauseCP C) ≤ 0 := by
  rintro C (⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩)
  · revert i
    decide +kernel
  · revert i i' j hne
    decide +kernel

end PEqualNP.Outside.L_meta_9662

theorem PEqualNP.Outside.L_meta_9662 : ¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (2 + 1) × Fin 2)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (2 + 1) 2) π ∧ π.length ≤ 18) := by
  rintro ⟨π, h, hl⟩
  have := PEqualNP.Outside.L_meta_9662.lower PEqualNP.Outside.L_meta_9662.pt 2 (by norm_num) (fun _ => 1)
    (fun _ => by norm_num) PEqualNP.Outside.L_meta_9662.hax PEqualNP.Outside.L_meta_9662.hdf π h
  simp only [Fintype.card_fin] at this
  omega
