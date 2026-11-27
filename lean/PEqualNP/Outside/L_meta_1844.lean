import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1844

theorem pow_bd (d e : ℕ) : 2 ^ e + d ≤ 2 ^ (d + e) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 : 1 ≤ 2 ^ (d + e) := Nat.one_le_two_pow
    have h2 : 2 ^ (d + 1 + e) = 2 * 2 ^ (d + e) := by
      rw [show d + 1 + e = (d + e) + 1 by omega, pow_succ]; ring
    omega

theorem key (u v w u' v' w' : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (huu : u ≤ u')
    (hvv : v ≤ v') (hww : w ≤ w') : u * v * w ≤ u' * v' * w' := by
  have h1 : u * v ≤ u' * v' := mul_le_mul huu hvv hv (hu.trans huu)
  exact mul_le_mul h1 hww hw (mul_nonneg (hu.trans huu) (hv.trans hvv))

theorem xbd (d m r q N : ℤ) (hdm : d ≤ m) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hmr : 4 * m * r ≤ q) (hN : N = q ^ 2 + q + 1) :
    3 * N - 4 * m ≤ 4 * (N - d * (1 + r * (q + 1))) := by
  have h0 : 0 ≤ 1 + r * (q + 1) := add_nonneg zero_le_one (mul_nonneg hr (by linarith))
  have h1 : d * (1 + r * (q + 1)) ≤ m * (1 + r * (q + 1)) := mul_le_mul_of_nonneg_right hdm h0
  have h2 : 4 * m * r * (q + 1) ≤ q * (q + 1) := mul_le_mul_of_nonneg_right hmr (by linarith)
  subst hN
  nlinarith [h1, h2]

theorem stage (a c r T q X Y : ℤ) (hT : q + 1 ≤ 2 * T) (hq : 0 ≤ q) (hrq : r ≤ q)
    (h : a * (3 * q * T) ≤ c * (r * T * X * Y)) :
    a * max (r * max (2 * T) (q + 1)) (3 * q * T) ≤ c * (r * T * X * Y) := by
  rw [max_eq_left hT, max_eq_right (by
    nlinarith [mul_nonneg (show 0 ≤ T by linarith) (show 0 ≤ 3 * q - 2 * r by linarith)])]
  exact h

theorem fin (N m q r T X Y a c : ℤ) (ha : a = (3 * N - 4 * m) * (q - m) * (q - 4 * m))
    (hc : c = 48 * m * q) (h1 : 0 ≤ 3 * N - 4 * m) (h2 : 0 ≤ q - m) (h3 : 0 ≤ q - 4 * m)
    (hX : 3 * N - 4 * m ≤ 4 * X) (hY : q - m ≤ Y) (hW : q - 4 * m ≤ 4 * m * r)
    (hT : 0 ≤ T) (hq : 0 ≤ q) : a * (3 * q * T) ≤ c * (r * T * X * Y) := by
  subst ha hc
  have hk := key _ _ _ _ _ _ h1 h2 h3 hX hY hW
  have h4 : 0 ≤ 3 * q * T := mul_nonneg (by linarith) hT
  have h5 := mul_le_mul_of_nonneg_left hk h4
  linarith

end PEqualNP.Outside.L_meta_1844

open PEqualNP.Outside.L_meta_1844

theorem PEqualNP.Outside.L_meta_1844 : (∀ (qlv18 Nlv18 klv18 mlv18 alv18 clv18 : ℕ) (Ilv18 : Fin Nlv18 → Fin Nlv18 → Prop) [DecidableRel Ilv18] (Clv18 : PEqualNP.CircuitLowerBounds.Circuit) (Rlv18 : ℕ → ℕ), 2 ≤ qlv18 → Nlv18 = qlv18 ^ 2 + qlv18 + 1 → (∀ llv18 : Fin Nlv18, (Finset.univ.filter (fun plv18 => Ilv18 plv18 llv18)).card = qlv18 + 1) → (∀ palv18 pblv18 : Fin Nlv18, palv18 ≠ pblv18 → ∃! lblv18 : Fin Nlv18, Ilv18 palv18 lblv18 ∧ Ilv18 pblv18 lblv18) → 1 ≤ klv18 → klv18 ≤ qlv18 → ((∀ glv18 ∈ Clv18.gates, (glv18.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv18.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv18.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv18 + Nlv18) Clv18) → Set.ncard {jlv18 : ℕ | jlv18 < Clv18.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv18x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.Ico Nlv18 (Nlv18 + Nlv18))).getD ilv18x3 0 = 0) ∨ (∀ hlv18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.range Nlv18)).getD hlv18 0 = 0))} ≤ mlv18 → (∀ plv18x1 llv18x1 : Fin Nlv18, Ilv18 plv18x1 llv18x1 → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 (fun klv18x1 => decide (klv18x1 = Fin.castAdd Nlv18 plv18x1 ∨ klv18x1 = Fin.natAdd Nlv18 llv18x1)) = true) → (∀ zlv18 : Fin (Nlv18 + Nlv18) → Bool, (Finset.univ.filter (fun llv18x2 : Fin Nlv18 => zlv18 (Fin.natAdd Nlv18 llv18x2) = true)).card ≤ klv18 → (¬ ∃ plv18x2 llv18x3 : Fin Nlv18, Ilv18 plv18x2 llv18x3 ∧ zlv18 (Fin.castAdd Nlv18 plv18x2) = true ∧ zlv18 (Fin.natAdd Nlv18 llv18x3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 zlv18 = false) → (∀ dlv18 < mlv18, 1 ≤ Rlv18 dlv18 ∧ Rlv18 dlv18 ≤ qlv18) → (∀ dlv18x1 elv18x1 : ℕ, dlv18x1 + elv18x1 = mlv18 → 2 ^ elv18x1 + dlv18x1 ≤ klv18 ∧ ∑ ilv18 ∈ Finset.range dlv18x1, (1 + Rlv18 ilv18 * (qlv18 + 1)) < Nlv18) → (∀ dlv18x2 elv18x2 : ℕ, dlv18x2 + elv18x2 + 1 = mlv18 → (alv18 : ℤ) * max ((Rlv18 dlv18x2 : ℤ) * max (2 * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ≤ (clv18 : ℤ) * ((Rlv18 dlv18x2 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1)) * ((Nlv18 : ℤ) - ∑ ilv18x1 ∈ Finset.range dlv18x2, (1 + (Rlv18 ilv18x1 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (dlv18x2 : ℤ)))) → (alv18 : ℤ) * max ((qlv18 : ℤ) * max (2 * ((klv18 : ℤ) - (mlv18 : ℤ))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ))) ≤ (clv18 : ℤ) * ((qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ)) * ((Nlv18 : ℤ) - ∑ ilv18x2 ∈ Finset.range mlv18, (1 + (Rlv18 ilv18x2 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (mlv18 : ℤ))) → alv18 ≤ clv18 * Clv18.size) → (∀ (N112 km112 : ℕ) (C112 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C112 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) C112 → Set.ncard {j112 : ℕ | j112 < C112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112 0 = 0) ∨ (∀ h112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112 0 = 0))} ≤ km112 → (∃ z112 z112a : Fin (N112 + N112) → Bool, PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112 ≠ PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112a) → ∃ D112 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g112 ∈ D112.gates, (g112.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g112.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g112.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) D112) ∧ Set.ncard {j112a : ℕ | j112a < D112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112a 0 = 0) ∨ (∀ h112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112a 0 = 0))} ≤ km112 ∧ D112.size ≤ C112.size ∧ PEqualNP.MetaComplexity.circuitFun (N112 + N112) D112 = PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112) → ∀ (qlv18g Nlv18g : ℕ) (Ilv18g : Fin Nlv18g → Fin Nlv18g → Prop) [DecidableRel Ilv18g] (Clv18g : PEqualNP.CircuitLowerBounds.Circuit) (mlv18g : ℕ), 2 ≤ qlv18g → Nlv18g = qlv18g ^ 2 + qlv18g + 1 → (∀ llv18g : Fin Nlv18g, (Finset.univ.filter (fun plv18g => Ilv18g plv18g llv18g)).card = qlv18g + 1) → (∀ palv18g pblv18g : Fin Nlv18g, palv18g ≠ pblv18g → ∃! lblv18g : Fin Nlv18g, Ilv18g palv18g lblv18g ∧ Ilv18g pblv18g lblv18g) → PEqualNP.MetaComplexity.Monotone2 Clv18g → PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv18g + Nlv18g) Clv18g → Set.ncard {jlv18g : ℕ | jlv18g < Clv18g.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18g jlv18g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv18g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18g jlv18g).inputs, (Clv18g.lineDegrees (Nlv18g + Nlv18g) (Finset.Ico Nlv18g (Nlv18g + Nlv18g))).getD ilv18g 0 = 0) ∨ (∀ hlv18g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18g jlv18g).inputs, (Clv18g.lineDegrees (Nlv18g + Nlv18g) (Finset.range Nlv18g)).getD hlv18g 0 = 0))} ≤ mlv18g → 1 ≤ mlv18g → 4 * mlv18g ≤ qlv18g → 2 ^ (mlv18g + 1) ≤ qlv18g + 1 → (∀ plv18gx1 llv18gx1 : Fin Nlv18g, Ilv18g plv18gx1 llv18gx1 → PEqualNP.MetaComplexity.circuitFun (Nlv18g + Nlv18g) Clv18g (fun klv18g => decide (klv18g = Fin.castAdd Nlv18g plv18gx1 ∨ klv18g = Fin.natAdd Nlv18g llv18gx1)) = true) → (∀ zlv18g : Fin (Nlv18g + Nlv18g) → Bool, (Finset.univ.filter (fun llv18gx2 : Fin Nlv18g => zlv18g (Fin.natAdd Nlv18g llv18gx2) = true)).card ≤ qlv18g → (¬ ∃ plv18gx2 llv18gx3 : Fin Nlv18g, Ilv18g plv18gx2 llv18gx3 ∧ zlv18g (Fin.castAdd Nlv18g plv18gx2) = true ∧ zlv18g (Fin.natAdd Nlv18g llv18gx3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv18g + Nlv18g) Clv18g zlv18g = false) → ((3 : ℤ) * (Nlv18g : ℤ) - 4 * (mlv18g : ℤ)) * ((qlv18g : ℤ) - (mlv18g : ℤ)) * ((qlv18g : ℤ) - 4 * (mlv18g : ℤ)) ≤ 48 * (mlv18g : ℤ) * (qlv18g : ℤ) * (Clv18g.size : ℤ) := by
  intro hLV hNorm q N I inst C m hq hN hline hpts hmono hrb hcross hm1 hm4 hpow hacc hrej
  have hNpos : 0 < N := by rw [hN]; positivity
  have hnc : ∃ z z' : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z ≠
        PEqualNP.MetaComplexity.circuitFun (N + N) C z' := by
    have hc := hline ⟨0, hNpos⟩
    have hne : (Finset.univ.filter (fun p => I p ⟨0, hNpos⟩)).Nonempty := by
      rw [← Finset.card_pos, hc]; omega
    obtain ⟨p, hp⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N ⟨0, hNpos⟩), fun _ => false, ?_⟩
    rw [hacc p ⟨0, hNpos⟩ hp, hrej (fun _ => false) (by simp) (by simp)]
    simp
  obtain ⟨D, ⟨hD2, hDrb⟩, hDcross, hDsize, hDfun⟩ := hNorm N m C hmono hrb hcross hnc
  obtain ⟨r, hr⟩ : ∃ r, r = q / (4 * m) := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [hr]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hr2 : 4 * m * r ≤ q := by rw [hr]; exact Nat.mul_div_le q (4 * m)
  have hr3 : q < 4 * m * r + 4 * m := by
    have := Nat.lt_mul_div_succ q (show 0 < 4 * m by omega)
    rw [← hr] at this
    rw [Nat.mul_add] at this
    omega
  have hrq : r ≤ q := by rw [hr]; exact Nat.div_le_self _ _
  have hp2 : 2 * 2 ^ m ≤ q + 1 := by
    have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    omega
  have hNq : q ≤ N := by rw [hN]; omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = (3 * N - 4 * m) * (q - m) * (q - 4 * m) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = 48 * m * q := ⟨_, rfl⟩
  have haz : (a : ℤ) = (3 * (N : ℤ) - 4 * m) * ((q : ℤ) - m) * ((q : ℤ) - 4 * m) := by
    rw [ha]
    push_cast [Nat.cast_sub (show 4 * m ≤ 3 * N by omega), Nat.cast_sub (show m ≤ q by omega),
      Nat.cast_sub hm4]
    ring
  have hcz : (c : ℤ) = 48 * (m : ℤ) * (q : ℤ) := by rw [hc]; push_cast; ring
  have hNz : (N : ℤ) = (q : ℤ) ^ 2 + q + 1 := by rw [hN]; push_cast; ring
  have hm1z : (1 : ℤ) ≤ m := by exact_mod_cast hm1
  have hm4z : 4 * (m : ℤ) ≤ q := by exact_mod_cast hm4
  have hr1z : (1 : ℤ) ≤ r := by exact_mod_cast hr1
  have hr2z : 4 * (m : ℤ) * r ≤ q := by exact_mod_cast hr2
  have hr3z : (q : ℤ) < 4 * m * r + 4 * m := by exact_mod_cast hr3
  have hrqz : (r : ℤ) ≤ q := by exact_mod_cast hrq
  have hp2z : 2 * (2 : ℤ) ^ m ≤ q + 1 := by exact_mod_cast hp2
  have hNqz : (q : ℤ) ≤ N := by exact_mod_cast hNq
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hmain : a ≤ c * D.size := by
    refine hLV q N q m a c I D (fun _ => r) hq hN hline hpts (by omega) le_rfl ⟨hD2, hDrb⟩ hDcross
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro p l h
      rw [hDfun]; exact hacc p l h
    · intro z h1 h2
      rw [hDfun]; exact hrej z h1 h2
    · intro d _
      exact ⟨hr1, hrq⟩
    · intro d e hde
      have hb := pow_bd d e
      rw [hde] at hb
      refine ⟨by omega, ?_⟩
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h1 : d * (1 + r * (q + 1)) ≤ m * (1 + r * (q + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : 4 * m * r * (q + 1) ≤ q * (q + 1) := Nat.mul_le_mul_right _ hr2
      rw [hN]
      nlinarith [h1, h2, sq_nonneg q]
    · intro d e hde
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hb := pow_bd d (e + 1)
      rw [show d + (e + 1) = m by omega] at hb
      have hbz : (2 : ℤ) ^ (e + 1) + d ≤ 2 ^ m := by exact_mod_cast hb
      have hdm : (d : ℤ) ≤ m := by
        have : d ≤ m := by omega
        exact_mod_cast this
      have hd0 : (0 : ℤ) ≤ d := by positivity
      have hT : (q : ℤ) + 1 ≤ 2 * ((q : ℤ) + 1 - d - 2 ^ (e + 1)) := by linarith
      refine stage _ _ _ _ _ _ _ hT hq0 hrqz ?_
      refine fin N m q r _ _ _ a c haz hcz (by linarith) (by linarith) (by linarith)
        (xbd d m r q N hdm (by linarith) hq0 hr2z hNz) (by linarith) (by linarith) (by linarith) hq0
    · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hT : (q : ℤ) + 1 ≤ 2 * ((q : ℤ) - m) := by linarith
      refine stage _ _ _ _ _ _ _ hT hq0 le_rfl ?_
      have hW : (q : ℤ) - 4 * m ≤ 4 * m * q := by
        have := mul_le_mul_of_nonneg_right hm1z hq0
        linarith
      refine fin N m q q _ _ _ a c haz hcz (by linarith) (by linarith) (by linarith)
        (xbd m m r q N le_rfl (by linarith) hq0 hr2z hNz) le_rfl hW (by linarith) hq0
  have h2 : a ≤ c * C.size := hmain.trans (Nat.mul_le_mul_left _ hDsize)
  have h3 : (a : ℤ) ≤ (c : ℤ) * (C.size : ℤ) := by exact_mod_cast h2
  rw [haz, hcz] at h3
  exact h3
