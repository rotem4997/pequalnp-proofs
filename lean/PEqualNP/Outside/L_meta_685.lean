import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_685

def L {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : F) : F →+ F where
  toFun x := x ^ p - m * x
  map_zero' := by simp [zero_pow (Fact.out : p.Prime).ne_zero]
  map_add' x y := by rw [add_pow_char]; ring

lemma ker_card_le {F : Type} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : F) :
    Nat.card (L p m).ker ≤ p := by
  classical
  have hp : p.Prime := Fact.out
  have h1 : 0 < p - 1 := by have := hp.two_le; omega
  have hsub : ((L p m).ker : Set F) ⊆
      ((insert 0 (Polynomial.nthRootsFinset (p - 1) m) : Finset F) : Set F) := by
    intro x hx
    change x ^ p - m * x = 0 at hx
    rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Polynomial.mem_nthRootsFinset h1]
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      have hx' : x ^ p = x * x ^ (p - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2 : x * (x ^ (p - 1) - m) = 0 := by
        rw [mul_sub, ← hx']
        linear_combination hx
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h h0
      · exact sub_eq_zero.mp h
  have hS : (Polynomial.nthRootsFinset (p - 1) m).card ≤ p - 1 := by
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  change ((L p m).ker : Set F).ncard ≤ p
  calc ((L p m).ker : Set F).ncard
      ≤ ((insert 0 (Polynomial.nthRootsFinset (p - 1) m) : Finset F) : Set F).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (insert 0 (Polynomial.nthRootsFinset (p - 1) m) : Finset F).card := Set.ncard_coe_finset _
    _ ≤ (Polynomial.nthRootsFinset (p - 1) m).card + 1 := Finset.card_insert_le _ _
    _ ≤ p - 1 + 1 := by omega
    _ = p := by omega

lemma ker_card {F : Type} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : F) :
    Nat.card (L p m).ker = 1 ∨ Nat.card (L p m).ker = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hd : Nat.card (L p m).ker ∣ p ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hle := ker_card_le p m
  rw [he] at hle ⊢
  rcases e with _ | _ | e
  · left; simp
  · right; simp
  · exfalso
    have h2 : p ^ 2 ≤ p ^ (e + 1 + 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega

lemma comap_card {G : Type} [AddCommGroup G] [Finite G] (p : ℕ) (hp : p.Prime) (f : G →+ G)
    (hr : Nat.card f.ker = 1 ∨ Nat.card f.ker = p) (A : AddSubgroup G) :
    Nat.card (A.comap f) = Nat.card A ∨ Nat.card (A.comap f) = p * Nat.card A := by
  have h1 := (A.comap f).card_mul_index
  have h2 : (A.comap f).index = A.relIndex f.range := A.index_comap f
  have h3 : A.relIndex f.range * f.range.index = (A ⊓ f.range).index := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_mul_index inf_le_right
  have h4 : f.range.relIndex A * A.index = (A ⊓ f.range).index := by
    rw [inf_comm, ← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_mul_index inf_le_right
  have h5 := A.card_mul_index
  have h6 : f.range.index = Nat.card f.ker := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := f.range))
    rw [f.range.index_mul_card, AddSubgroup.card_ker_mul_card_range]
  have h7 : f.range.relIndex A ∣ f.range.index := AddSubgroup.relIndex_dvd_index_of_normal _ _
  have hN : 0 < Nat.card G := Nat.card_pos
  have hi : 0 < (A.comap f).index := Nat.pos_of_ne_zero (AddSubgroup.index_ne_zero_of_finite)
  rw [h6] at h7
  rw [h6, ← h2] at h3
  rw [← h4] at h3
  rw [← h5] at h1
  rcases hr with hr | hr
  · rw [hr, Nat.dvd_one] at h7
    rw [hr, h7, mul_one, one_mul] at h3
    left
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right (lt_of_lt_of_eq hi h3) h1
  · rw [hr] at h7 h3
    rcases hp.eq_one_or_self_of_dvd _ h7 with hj | hj
    · right
      rw [hj, one_mul] at h3
      rw [← h3] at h1
      apply Nat.eq_of_mul_eq_mul_right hi
      rw [h1]
      ring
    · left
      rw [hj, mul_comm] at h3
      have h8 : (A.comap f).index = A.index := Nat.eq_of_mul_eq_mul_left hp.pos h3
      rw [h8] at h1
      exact Nat.eq_of_mul_eq_mul_right (lt_of_lt_of_eq hi h8) h1

end PEqualNP.Outside.L_meta_685

theorem PEqualNP.Outside.L_meta_685 : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (A : AddSubgroup F),
    (∀ a ∈ A, ∀ c : ZMod p, (ZMod.cast c : F) * a ∈ A) →
    ∀ m k : F,
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = 0 ∨
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = Nat.card A ∨
      Nat.card {x : F // x ^ p - m * x + k ∈ A} = p * Nat.card A := by
  intro p _ F _ _ _ A _ m k
  classical
  by_cases hex : ∃ s : F, s ^ p - m * s + k ∈ A
  · obtain ⟨s, hs⟩ := hex
    have hs' : PEqualNP.Outside.L_meta_685.L p m s + k ∈ A := hs
    have hC : Nat.card {x : F // x ^ p - m * x + k ∈ A} =
        Nat.card (A.comap (PEqualNP.Outside.L_meta_685.L p m)) := by
      apply Nat.card_congr
      refine Equiv.subtypeEquiv (Equiv.addRight (-s)) (fun t => ?_)
      change PEqualNP.Outside.L_meta_685.L p m t + k ∈ A ↔
        PEqualNP.Outside.L_meta_685.L p m (t + -s) ∈ A
      have he : PEqualNP.Outside.L_meta_685.L p m (t + -s) =
          (PEqualNP.Outside.L_meta_685.L p m t + k) -
            (PEqualNP.Outside.L_meta_685.L p m s + k) := by
        rw [map_add, map_neg]
        abel
      rw [he]
      exact ⟨fun h => A.sub_mem h hs', fun h => by simpa only [sub_add_cancel] using A.add_mem h hs'⟩
    rw [hC]
    right
    exact PEqualNP.Outside.L_meta_685.comap_card p Fact.out _
      (PEqualNP.Outside.L_meta_685.ker_card p m) A
  · left
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun x => hex ⟨x.1, x.2⟩⟩
