import Mathlib
import PEqualNP.Defs

namespace LGct214M

open Module

theorem orth_bound {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Submodule ℂ (ι → ℂ))
    (h : ∀ a ∈ A, ∀ b ∈ B, dotProduct a b = 0) :
    finrank ℂ A + finrank ℂ B ≤ Fintype.card ι := by
  set W : Submodule ℂ (Module.Dual ℂ (ι → ℂ)) := A.map (dotProductEquiv ℂ ι).toLinearMap with hW
  have hWrank : finrank ℂ W = finrank ℂ A := LinearEquiv.finrank_map_eq (dotProductEquiv ℂ ι) A
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hWrank, Module.finrank_fintype_fun_eq_card] at hsum
  have hle : B ≤ W.dualCoannihilator := by
    intro x hx
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hφ
    simpa [dotProductEquiv] using h a ha x hx
  have := Submodule.finrank_mono hle
  omega

theorem rank_nullity {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] (K : Submodule ℂ V) (p : V →ₗ[ℂ] W) :
    finrank ℂ (K.map p) + finrank ℂ ↥(K ⊓ LinearMap.ker p) = finrank ℂ K := by
  have h := LinearMap.finrank_range_add_finrank_ker (p.domRestrict K)
  rw [LinearMap.range_domRestrict] at h
  have h2 : (LinearMap.ker (p.domRestrict K)).map K.subtype = K ⊓ LinearMap.ker p := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have h3 : finrank ℂ ((LinearMap.ker (p.domRestrict K)).map K.subtype) =
      finrank ℂ (LinearMap.ker (p.domRestrict K)) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ K.injective_subtype _)).symm
  rw [h2] at h3
  omega

theorem finrank_sup_span {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (L : Submodule ℂ V) (x : V) (hx : x ∉ L) :
    finrank ℂ ↥(L ⊔ Submodule.span ℂ {x}) = finrank ℂ L + 1 := by
  have hinf : L ⊓ Submodule.span ℂ {x} = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvL, hvS⟩ := Submodule.mem_inf.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvS
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((L.smul_mem_iff hc).1 hvL) hx
  have hx0 : x ≠ 0 := by
    intro h; apply hx; rw [h]; exact L.zero_mem
  have := Submodule.finrank_sup_add_finrank_inf_eq L (Submodule.span ℂ {x})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at this
  exact this

def p2 (M : Fin 2 × Fin 2 → ℂ) : ℂ := M (0, 0) * M (1, 1) + M (0, 1) * M (1, 0)

def sw2 : (Fin 2 × Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 × Fin 2 → ℂ) where
  toFun y := fun q => y (Fin.rev q.1, Fin.rev q.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem p2_add (X y : Fin 2 × Fin 2 → ℂ) :
    p2 (X + y) = p2 X + p2 y + dotProduct X (sw2 y) := by
  simp [p2, sw2, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem sw2_inj : Function.Injective sw2 := by
  intro a b h
  funext q
  have := congrFun h (Fin.rev q.1, Fin.rev q.2)
  simpa [sw2] using this

theorem F2 (L : Submodule ℂ (Fin 2 × Fin 2 → ℂ)) (X0 : Fin 2 × Fin 2 → ℂ)
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {X0}, ∀ y ∈ L, p2 (X + y) = p2 X) (hne : p2 X0 ≠ 0) :
    finrank ℂ L ≤ 1 := by
  have hz : ∀ y ∈ L, p2 y = 0 := by
    intro y hy
    have := hinv 0 (Submodule.zero_mem _) y hy
    rw [zero_add] at this
    rw [this]; simp [p2]
  have hX0 : X0 ∉ L := fun h => hne (hz X0 h)
  have hdot : ∀ a ∈ L.map sw2, ∀ b ∈ L ⊔ Submodule.span ℂ {X0}, dotProduct a b = 0 := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 ha
    have e := p2_add b y
    rw [hinv b hb y hy, hz y hy] at e
    rw [dotProduct_comm]
    linear_combination -e
  have h1 := orth_bound _ _ hdot
  have h2 : finrank ℂ (L.map sw2) = finrank ℂ L :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ sw2_inj L)).symm
  have h3 := finrank_sup_span L X0 hX0
  simp only [Fintype.card_prod, Fintype.card_fin] at h1
  omega


def p3 (M : Fin 3 × Fin 3 → ℂ) : ℂ :=
  M (0, 0) * M (1, 1) * M (2, 2) + M (0, 0) * M (1, 2) * M (2, 1) +
  M (0, 1) * M (1, 0) * M (2, 2) + M (0, 1) * M (1, 2) * M (2, 0) +
  M (0, 2) * M (1, 0) * M (2, 1) + M (0, 2) * M (1, 1) * M (2, 0)

def mn3 : (Fin 3 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 × Fin 2 → ℂ) where
  toFun X := fun q => X (q.1.succ, q.2.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def row3 : (Fin 3 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := fun k => X (0, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem p3_smul (c : ℂ) (M : Fin 3 × Fin 3 → ℂ) : p3 (c • M) = c ^ 3 * p3 M := by
  simp [p3]; ring

theorem p3_lap (M : Fin 3 × Fin 3 → ℂ) (h1 : M (0, 1) = 0) (h2 : M (0, 2) = 0) :
    p3 M = M (0, 0) * p2 (mn3 M) := by
  simp [p3, p2, mn3, h1, h2]; ring

theorem p2_interp (A B : Fin 2 × Fin 2 → ℂ) :
    p2 A = 3 * p2 (A + (1 : ℂ) • B) - 3 * p2 (A + (2 : ℂ) • B) + p2 (A + (3 : ℂ) • B) := by
  simp [p2]; ring

theorem F3_core (L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)) (X0 : Fin 3 × Fin 3 → ℂ)
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {X0}, ∀ y ∈ L, p3 (X + y) = p3 X)
    (Xs : Fin 3 × Fin 3 → ℂ) (hXsC : Xs ∈ L ⊔ Submodule.span ℂ {X0})
    (hXs0 : Xs (0, 0) = 1) (hXs1 : Xs (0, 1) = 0) (hXs2 : Xs (0, 2) = 0) (hXsne : p3 Xs ≠ 0)
    (W1 : Fin 3 × Fin 3 → ℂ) (hW1C : W1 ∈ L ⊔ Submodule.span ℂ {X0})
    (hW11 : W1 (0, 1) = 1) (hW12 : W1 (0, 2) = 0)
    (W2 : Fin 3 × Fin 3 → ℂ) (hW2C : W2 ∈ L ⊔ Submodule.span ℂ {X0})
    (hW21 : W2 (0, 1) = 0) (hW22 : W2 (0, 2) = 1) :
    Module.finrank ℂ L ≤ 3 := by
  set C := L ⊔ Submodule.span ℂ {X0} with hC
  have hLC : L ≤ C := le_sup_left
  by_contra hcon
  push Not at hcon
  set K := L ⊓ LinearMap.ker row3 with hK
  have hrowL : Module.finrank ℂ (L.map row3) ≤ 2 := by
    have hne : L.map row3 ≠ ⊤ := by
      intro htop
      have : (Pi.single 0 1 : Fin 3 → ℂ) ∈ L.map row3 := by rw [htop]; trivial
      obtain ⟨y, hy, hyr⟩ := Submodule.mem_map.1 this
      have e := hinv Xs hXsC (-y) (L.neg_mem hy)
      have h0 : p3 (Xs + -y) = 0 := by
        have r0 := congrFun hyr 0
        have r1 := congrFun hyr 1
        have r2 := congrFun hyr 2
        simp [row3] at r0 r1 r2
        simp [p3, r0, r1, r2, hXs0, hXs1, hXs2]
      exact hXsne (e ▸ h0)
    have h3 := Submodule.finrank_lt hne
    rw [Module.finrank_fin_fun] at h3
    omega
  have hKdim : Module.finrank ℂ L ≤ Module.finrank ℂ K + 2 := by
    have h := rank_nullity L row3
    rw [show L ⊓ LinearMap.ker row3 = K from rfl] at h
    omega
  have KL : ∀ z ∈ K, ∀ c : ℂ, p2 (mn3 z + c • mn3 Xs) = c ^ 2 * p3 Xs := by
    intro z hz c
    have hzL : z ∈ L := (Submodule.mem_inf.1 hz).1
    have hzr : row3 z = 0 := (Submodule.mem_inf.1 hz).2
    have z0 : z (0, 0) = 0 := congrFun hzr 0
    have z1 : z (0, 1) = 0 := congrFun hzr 1
    have z2 : z (0, 2) = 0 := congrFun hzr 2
    have main : ∀ c : ℂ, c ≠ 0 → p2 (mn3 z + c • mn3 Xs) = c ^ 2 * p3 Xs := by
      intro c hc
      have e := hinv (c • Xs) (C.smul_mem c hXsC) z hzL
      rw [p3_smul] at e
      have e2 := p3_lap (c • Xs + z) (by simp [hXs1, z1]) (by simp [hXs2, z2])
      rw [e] at e2
      have hm : mn3 (c • Xs + z) = mn3 z + c • mn3 Xs := by
        rw [map_add, map_smul, add_comm]
      rw [hm] at e2
      simp [hXs0, z0] at e2
      have : c * (p2 (mn3 z + c • mn3 Xs) - c ^ 2 * p3 Xs) = 0 := by linear_combination -e2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc
      · linear_combination h
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero, p2_interp (mn3 z) (mn3 Xs), main 1 one_ne_zero,
        main 2 two_ne_zero, main 3 three_ne_zero]
      ring
    · exact main c hc
  set L2 := K.map mn3 with hL2
  have hF2 : Module.finrank ℂ L2 ≤ 1 := by
    apply F2 L2 (mn3 Xs)
    · intro M hM m hm
      obtain ⟨m1, hm1, M', hM', rfl⟩ := Submodule.mem_sup.1 hM
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hM'
      obtain ⟨z1, hz1, rfl⟩ := Submodule.mem_map.1 hm1
      obtain ⟨z2, hz2, rfl⟩ := Submodule.mem_map.1 hm
      have e1 := KL z1 hz1 c
      have e2 := KL (z1 + z2) (K.add_mem hz1 hz2) c
      rw [map_add] at e2
      rw [show mn3 z1 + c • mn3 Xs + mn3 z2 = mn3 z1 + mn3 z2 + c • mn3 Xs by abel, e2, e1]
    · have h := KL 0 K.zero_mem 1
      rw [map_zero, zero_add, one_smul, one_pow, one_mul] at h
      rw [h]; exact hXsne

  set Z := K ⊓ LinearMap.ker mn3 with hZ
  have hZdim : Module.finrank ℂ K = Module.finrank ℂ L2 + Module.finrank ℂ Z := by
    have h := rank_nullity K mn3
    rw [show K ⊓ LinearMap.ker mn3 = Z from rfl, show K.map mn3 = L2 from rfl] at h
    omega
  have hZe : ∀ z ∈ Z, z (0, 0) = 0 ∧ z (0, 1) = 0 ∧ z (0, 2) = 0 ∧ z (1, 1) = 0 ∧
      z (1, 2) = 0 ∧ z (2, 1) = 0 ∧ z (2, 2) = 0 := by
    intro z hz
    have hzK := (Submodule.mem_inf.1 hz).1
    have hzr : row3 z = 0 := (Submodule.mem_inf.1 hzK).2
    have hzm : mn3 z = 0 := (Submodule.mem_inf.1 hz).2
    refine ⟨congrFun hzr 0, congrFun hzr 1, congrFun hzr 2, congrFun hzm (0, 0),
      congrFun hzm (0, 1), congrFun hzm (1, 0), congrFun hzm (1, 1)⟩
  have hPhi : ∀ z ∈ Z, ∀ X1 ∈ C, X1 (0, 1) = 0 → X1 (0, 2) = 0 →
      z (1, 0) * X1 (2, 2) + z (2, 0) * X1 (1, 2) = 0 ∧
      z (1, 0) * X1 (2, 1) + z (2, 0) * X1 (1, 1) = 0 := by
    intro z hz X1 hX1 h1 h2
    obtain ⟨e00, e01, e02, e11, e12, e21, e22⟩ := hZe z hz
    have hzL : z ∈ L := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hz).1).1
    have hf : ∀ X ∈ C, z (1, 0) * (X (0, 1) * X (2, 2) + X (0, 2) * X (2, 1)) +
        z (2, 0) * (X (0, 1) * X (1, 2) + X (0, 2) * X (1, 1)) = 0 := by
      intro X hX
      have e := hinv X hX z hzL
      simp only [p3, Pi.add_apply, e00, e01, e02, e11, e12, e21, e22] at e
      linear_combination e
    have fa := hf (X1 + W1) (C.add_mem hX1 hW1C)
    have fb := hf (X1 - W1) (C.sub_mem hX1 hW1C)
    have fc := hf (X1 + W2) (C.add_mem hX1 hW2C)
    have fd := hf (X1 - W2) (C.sub_mem hX1 hW2C)
    simp only [Pi.add_apply, Pi.sub_apply, h1, h2, hW11, hW12, hW21, hW22] at fa fb fc fd
    constructor
    · linear_combination (fa - fb) / 2
    · linear_combination (fc - fd) / 2
  have hP : Xs (1, 1) * Xs (2, 2) + Xs (1, 2) * Xs (2, 1) ≠ 0 := by
    have := p3_lap Xs hXs1 hXs2
    rw [hXs0, one_mul] at this
    rw [this] at hXsne
    simpa [p2, mn3] using hXsne
  have hab : ∀ z ∈ Z, z ≠ 0 → z (1, 0) ≠ 0 ∧ z (2, 0) ≠ 0 := by
    intro z hz hz0
    obtain ⟨e00, e01, e02, e11, e12, e21, e22⟩ := hZe z hz
    obtain ⟨q1, q2⟩ := hPhi z hz Xs hXsC hXs1 hXs2
    have hnz : z (1, 0) ≠ 0 ∨ z (2, 0) ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hz0
      funext q
      obtain ⟨i, k⟩ := q
      fin_cases i <;> fin_cases k
      · exact e00
      · exact e01
      · exact e02
      · exact hc.1
      · exact e11
      · exact e12
      · exact hc.2
      · exact e21
      · exact e22
    constructor
    · intro ha
      have hb : z (2, 0) ≠ 0 := by tauto
      rw [ha, zero_mul, zero_add] at q1 q2
      have h12 : Xs (1, 2) = 0 := (mul_eq_zero.1 q1).resolve_left hb
      have h11 : Xs (1, 1) = 0 := (mul_eq_zero.1 q2).resolve_left hb
      apply hP; rw [h12, h11]; ring
    · intro hb
      have ha : z (1, 0) ≠ 0 := by tauto
      rw [hb, zero_mul, add_zero] at q1 q2
      have h22 : Xs (2, 2) = 0 := (mul_eq_zero.1 q1).resolve_left ha
      have h21 : Xs (2, 1) = 0 := (mul_eq_zero.1 q2).resolve_left ha
      apply hP; rw [h22, h21]; ring
  have hZpos : 1 ≤ Module.finrank ℂ Z := by omega
  have hZne : Z ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hZpos; omega
  obtain ⟨z0, hz0Z, hz0⟩ := Submodule.ne_bot_iff _ |>.1 hZne
  obtain ⟨ha, hb⟩ := hab z0 hz0Z hz0
  have hL2bot : ∀ m ∈ L2, m = 0 := by
    intro m hm
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.1 hm
    have hz'L : z' ∈ L := (Submodule.mem_inf.1 hz').1
    have hz'r : row3 z' = 0 := (Submodule.mem_inf.1 hz').2
    obtain ⟨q1, q2⟩ := hPhi z0 hz0Z z' (hLC hz'L) (congrFun hz'r 1) (congrFun hz'r 2)
    obtain ⟨s1, s2⟩ := hPhi z0 hz0Z Xs hXsC hXs1 hXs2
    have k0 := KL z' hz' 0
    have k1 := KL z' hz' 1
    simp only [zero_smul, add_zero, one_smul, one_pow, one_mul, zero_pow two_ne_zero,
      zero_mul] at k0 k1
    have hp3 := p3_lap Xs hXs1 hXs2
    rw [hXs0, one_mul] at hp3
    rw [hp3] at k1
    simp only [p2, mn3, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply] at k0 k1
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at k0 k1
    set a := z0 (1, 0)
    set b := z0 (2, 0)
    set u := z' (1, 1)
    set v := z' (1, 2)
    set w := z' (2, 1)
    set x := z' (2, 2)
    set U := Xs (1, 1)
    set V := Xs (1, 2)
    set W' := Xs (2, 1)
    set X' := Xs (2, 2)
    have e6 : u * X' + x * U + v * W' + w * V = 0 := by linear_combination k1 - k0
    have huv : b * (u * v) = 0 := by linear_combination (-(1 : ℂ) / 2) * (a * k0 - u * q1 - v * q2)
    have huV : b * (u * V + v * U) = 0 := by
      linear_combination (-(1 : ℂ) / 2) * (a * e6 - u * s1 - U * q1 - v * s2 - V * q2)
    have hUV : U * V ≠ 0 := by
      intro h
      apply hP
      have : a * (U * X' + V * W') = -2 * b * (U * V) := by
        linear_combination U * s1 + V * s2
      rw [h, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left ha
    have huv' : u * v = 0 := (mul_eq_zero.1 huv).resolve_left hb
    have huV' : u * V + v * U = 0 := (mul_eq_zero.1 huV).resolve_left hb
    have hV : V ≠ 0 := fun h => hUV (by rw [h, mul_zero])
    have hU : U ≠ 0 := fun h => hUV (by rw [h, zero_mul])
    have hu : u = 0 := by
      have : u ^ 2 * V = 0 := by linear_combination u * huV' - U * huv'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_right hV)
    have hv : v = 0 := by
      have : v ^ 2 * U = 0 := by linear_combination v * huV' - V * huv'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ((mul_eq_zero.1 this).resolve_right hU)
    have hx : x = 0 := by
      have : a * x = 0 := by linear_combination q1 - b * hv
      exact (mul_eq_zero.1 this).resolve_left ha
    have hw : w = 0 := by
      have : a * w = 0 := by linear_combination q2 - b * hu
      exact (mul_eq_zero.1 this).resolve_left ha
    funext q
    obtain ⟨i, k⟩ := q
    fin_cases i <;> fin_cases k
    · exact hu
    · exact hv
    · exact hw
    · exact hx
  have hL20 : Module.finrank ℂ L2 = 0 := by
    have : L2 = ⊥ := by
      rw [eq_bot_iff]; intro m hm; rw [Submodule.mem_bot]; exact hL2bot m hm
    rw [this, finrank_bot]
  set ev : (Fin 3 × Fin 3 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj ((1 : Fin 3), (0 : Fin 3)) with hev
  have hev1 : Module.finrank ℂ (Z.map ev) ≤ 1 := by
    have := Submodule.finrank_le (Z.map ev)
    rwa [Module.finrank_self] at this
  have hrn := rank_nullity Z ev
  have hZ2 : 1 ≤ Module.finrank ℂ ↥(Z ⊓ LinearMap.ker ev) := by omega
  have hne2 : Z ⊓ LinearMap.ker ev ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hZ2; omega
  obtain ⟨z1, hz1, hz1ne⟩ := Submodule.ne_bot_iff _ |>.1 hne2
  have := (hab z1 (Submodule.mem_inf.1 hz1).1 hz1ne).1
  exact this (Submodule.mem_inf.1 hz1).2


def rowr3 (r : Fin 3) : (Fin 3 × Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := fun k => X (r, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem p3_row_zero (r : Fin 3) (X : Fin 3 × Fin 3 → ℂ) (h : ∀ k, X (r, k) = 0) : p3 X = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  fin_cases r <;> simp only [p3] <;> simp_all

theorem p3_perm (r j : Fin 3) (X : Fin 3 × Fin 3 → ℂ) :
    p3 (X ∘ Equiv.prodCongr (Equiv.swap 0 r) (Equiv.swap 0 j)) = p3 X := by
  fin_cases r <;> fin_cases j <;>
    simp (config := { decide := true }) [p3, Equiv.swap_apply_def] <;> ring

theorem eq_zero_of_rows3 (X : Fin 3 × Fin 3 → ℂ) (h0 : ∀ k, X (0, k) = 0)
    (h1 : ∀ k, X (1, k) = 0) (h2 : ∀ k, X (2, k) = 0) : X = 0 := by
  funext q
  obtain ⟨i, k⟩ := q
  fin_cases i
  · exact h0 k
  · exact h1 k
  · exact h2 k

theorem F3 (L : Submodule ℂ (Fin 3 × Fin 3 → ℂ)) (X0 : Fin 3 × Fin 3 → ℂ)
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {X0}, ∀ y ∈ L, p3 (X + y) = p3 X) (hne : p3 X0 ≠ 0) :
    Module.finrank ℂ L ≤ 3 := by
  set C := L ⊔ Submodule.span ℂ {X0} with hC
  have hLC : L ≤ C := le_sup_left
  have hX0C : X0 ∈ C := Submodule.mem_sup_right (Submodule.mem_span_singleton_self X0)
  have hz : ∀ y ∈ L, p3 y = 0 := by
    intro y hy
    have := hinv 0 C.zero_mem y hy
    rw [zero_add] at this
    rw [this]; simp [p3]
  have hX0 : X0 ∉ L := fun h => hne (hz X0 h)
  have hCL : ∀ X ∈ C, p3 X = 0 → X ∈ L := by
    intro X hX h0
    obtain ⟨y, hy, m, hm, rfl⟩ := Submodule.mem_sup.1 hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    have e := hinv (c • X0) (C.smul_mem c hX0C) y hy
    rw [add_comm] at h0
    rw [h0, p3_smul] at e
    have hc : c = 0 := by
      rcases mul_eq_zero.1 e.symm with h | h
      · exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h
      · exact absurd h hne
    rw [hc, zero_smul, add_zero]; exact hy
  have hCdim : Module.finrank ℂ C = Module.finrank ℂ L + 1 := finrank_sup_span L X0 hX0
  by_contra hcon
  push Not at hcon
  have step1 : ∃ r, C.map (rowr3 r) = ⊤ := by
    by_contra hno
    push Not at hno
    have hK : ∀ r, Module.finrank ℂ L ≤ Module.finrank ℂ ↥(C ⊓ LinearMap.ker (rowr3 r)) + 1 := by
      intro r
      have h3 := Submodule.finrank_lt (hno r)
      rw [Module.finrank_fin_fun] at h3
      have := rank_nullity C (rowr3 r)
      omega
    have hKL : ∀ r, C ⊓ LinearMap.ker (rowr3 r) ≤ L := by
      intro r X hX
      obtain ⟨hXC, hXr⟩ := Submodule.mem_inf.1 hX
      apply hCL X hXC
      apply p3_row_zero r
      intro k
      exact congrFun (LinearMap.mem_ker.1 hXr) k
    set K0 := C ⊓ LinearMap.ker (rowr3 0)
    set K1 := C ⊓ LinearMap.ker (rowr3 1)
    set K2 := C ⊓ LinearMap.ker (rowr3 2)
    have hpair : ∀ A B : Submodule ℂ (Fin 3 × Fin 3 → ℂ), A ≤ L → B ≤ L →
        Module.finrank ℂ A + Module.finrank ℂ B ≤ Module.finrank ℂ ↥(A ⊓ B) + Module.finrank ℂ L := by
      intro A B hA hB
      have := Submodule.finrank_sup_add_finrank_inf_eq A B
      have := Submodule.finrank_mono (sup_le hA hB)
      omega
    have hall : ∀ X, X ∈ K0 → X ∈ K1 → X ∈ K2 → X = 0 := by
      intro X h0 h1 h2
      apply eq_zero_of_rows3
      · intro k; exact congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h0).2) k
      · intro k; exact congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h1).2) k
      · intro k; exact congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h2).2) k
    have i1 : (K1 ⊓ K2) ⊓ (K0 ⊓ K2) = ⊥ := by
      rw [eq_bot_iff]; intro X hX
      simp only [Submodule.mem_inf] at hX
      rw [Submodule.mem_bot]; exact hall X hX.2.1 hX.1.1 hX.1.2
    have i2 : (K1 ⊓ K2 ⊔ K0 ⊓ K2) ⊓ (K0 ⊓ K1) = ⊥ := by
      rw [eq_bot_iff]; intro X hX
      obtain ⟨hX1, hX2⟩ := Submodule.mem_inf.1 hX
      have hK2 : X ∈ K2 := (sup_le inf_le_right inf_le_right : K1 ⊓ K2 ⊔ K0 ⊓ K2 ≤ K2) hX1
      rw [Submodule.mem_bot]
      exact hall X (Submodule.mem_inf.1 hX2).1 (Submodule.mem_inf.1 hX2).2 hK2
    have d1 := Submodule.finrank_sup_add_finrank_inf_eq (K1 ⊓ K2) (K0 ⊓ K2)
    rw [i1, finrank_bot] at d1
    have d2 := Submodule.finrank_sup_add_finrank_inf_eq (K1 ⊓ K2 ⊔ K0 ⊓ K2) (K0 ⊓ K1)
    rw [i2, finrank_bot] at d2
    have hle : K1 ⊓ K2 ⊔ K0 ⊓ K2 ⊔ K0 ⊓ K1 ≤ L :=
      sup_le (sup_le (inf_le_left.trans (hKL 1)) (inf_le_left.trans (hKL 0)))
        (inf_le_left.trans (hKL 0))
    have d3 := Submodule.finrank_mono hle
    have p12 := hpair K1 K2 (hKL 1) (hKL 2)
    have p02 := hpair K0 K2 (hKL 0) (hKL 2)
    have p01 := hpair K0 K1 (hKL 0) (hKL 1)
    have k0 : Module.finrank ℂ L ≤ Module.finrank ℂ K0 + 1 := hK 0
    have k1 : Module.finrank ℂ L ≤ Module.finrank ℂ K1 + 1 := hK 1
    have k2 : Module.finrank ℂ L ≤ Module.finrank ℂ K2 + 1 := hK 2
    omega
  obtain ⟨r, hr⟩ := step1
  have hsurj : ∀ v : Fin 3 → ℂ, ∃ X ∈ C, rowr3 r X = v := by
    intro v
    have : v ∈ C.map (rowr3 r) := by rw [hr]; trivial
    obtain ⟨X, hX, hXv⟩ := Submodule.mem_map.1 this
    exact ⟨X, hX, hXv⟩
  have step2 : ∃ j, ∃ X ∈ C, rowr3 r X = Pi.single j 1 ∧ X ∉ L := by
    by_contra hno
    push Not at hno
    choose Xf hXfC hXfr using fun j => hsurj (Pi.single j 1)
    have hXfL : ∀ j, Xf j ∈ L := fun j => hno j (Xf j) (hXfC j) (hXfr j)
    set Y := X0 - ∑ j, X0 (r, j) • Xf j with hY
    have hYC : Y ∈ C := C.sub_mem hX0C (C.sum_mem fun j _ => C.smul_mem _ (hXfC j))
    have hYr : rowr3 r Y = 0 := by
      rw [hY, map_sub, map_sum]
      simp only [map_smul, hXfr]
      funext k
      simp [rowr3, Finset.sum_apply, Pi.single_apply]
    have hYL : Y ∈ L := hCL Y hYC (p3_row_zero r Y (fun k => congrFun hYr k))
    have hsumL : ∑ j, X0 (r, j) • Xf j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hXfL j)
    apply hX0
    have := L.add_mem hYL hsumL
    rwa [hY, sub_add_cancel] at this
  obtain ⟨j, Xs, hXsC, hXsr, hXsL⟩ := step2
  have hXsne : p3 Xs ≠ 0 := fun h => hXsL (hCL Xs hXsC h)
  set e := Equiv.prodCongr (Equiv.swap (0 : Fin 3) r) (Equiv.swap (0 : Fin 3) j) with he
  set T : (Fin 3 × Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e with hT
  have hTapp : ∀ X q, T X q = X (e q) := fun X q => rfl
  have hTp3 : ∀ X, p3 (T X) = p3 X := fun X => p3_perm r j X
  have hmapC : C.map T.toLinearMap = L.map T.toLinearMap ⊔ Submodule.span ℂ {T X0} := by
    rw [hC, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    rfl
  have hsw : ∀ k : Fin 3, k ≠ 0 → Equiv.swap (0 : Fin 3) j k ≠ j := by
    intro k hk h
    apply hk
    apply (Equiv.swap (0 : Fin 3) j).injective
    rw [h, Equiv.swap_apply_left]
  obtain ⟨V1, hV1C, hV1r⟩ := hsurj (Pi.single (Equiv.swap (0 : Fin 3) j 1) 1)
  obtain ⟨V2, hV2C, hV2r⟩ := hsurj (Pi.single (Equiv.swap (0 : Fin 3) j 2) 1)
  have hrowv : ∀ (X : Fin 3 × Fin 3 → ℂ) (v : Fin 3 → ℂ), rowr3 r X = v → ∀ k, X (r, k) = v k :=
    fun X v h k => congrFun h k
  have hTr : ∀ X k, T X (0, k) = X (r, Equiv.swap (0 : Fin 3) j k) := by
    intro X k
    rw [hTapp]
    simp [he, Equiv.swap_apply_left]
  have hmemT : ∀ X ∈ C, T X ∈ L.map T.toLinearMap ⊔ Submodule.span ℂ {T X0} := by
    intro X hX
    rw [← hmapC]
    exact Submodule.mem_map_of_mem hX
  have key := F3_core (L.map T.toLinearMap) (T X0) ?_ (T Xs) (hmemT Xs hXsC) ?_ ?_ ?_ ?_
    (T V1) (hmemT V1 hV1C) ?_ ?_ (T V2) (hmemT V2 hV2C) ?_ ?_
  · rw [LinearEquiv.finrank_map_eq] at key
    omega
  · intro X hX y hy
    rw [← hmapC] at hX
    obtain ⟨X1, hX1, rfl⟩ := Submodule.mem_map.1 hX
    obtain ⟨y1, hy1, rfl⟩ := Submodule.mem_map.1 hy
    have h1 : T.toLinearMap X1 + T.toLinearMap y1 = T (X1 + y1) := by simp
    rw [h1]
    change p3 (T (X1 + y1)) = p3 (T X1)
    rw [hTp3, hTp3]
    exact hinv X1 hX1 y1 hy1
  · rw [hTr, hrowv Xs _ hXsr, Equiv.swap_apply_left]; simp
  · rw [hTr, hrowv Xs _ hXsr, Pi.single_apply, if_neg (hsw 1 (by decide))]
  · rw [hTr, hrowv Xs _ hXsr, Pi.single_apply, if_neg (hsw 2 (by decide))]
  · rw [hTp3]; exact hXsne
  · rw [hTr, hrowv V1 _ hV1r]; simp
  · rw [hTr, hrowv V1 _ hV1r, Pi.single_apply, if_neg]
    intro h
    have := (Equiv.swap (0 : Fin 3) j).injective h
    exact absurd this (by decide)
  · rw [hTr, hrowv V2 _ hV2r, Pi.single_apply, if_neg]
    intro h
    have := (Equiv.swap (0 : Fin 3) j).injective h
    exact absurd this (by decide)
  · rw [hTr, hrowv V2 _ hV2r]; simp


def J4 : Fin 4 × Fin 4 → ℂ := fun _ => 1

def p4 (M : Fin 4 × Fin 4 → ℂ) : ℂ :=
  M (0, 0) * M (1, 1) * M (2, 2) * M (3, 3) +
  M (0, 0) * M (1, 1) * M (2, 3) * M (3, 2) +
  M (0, 0) * M (1, 2) * M (2, 1) * M (3, 3) +
  M (0, 0) * M (1, 2) * M (2, 3) * M (3, 1) +
  M (0, 0) * M (1, 3) * M (2, 1) * M (3, 2) +
  M (0, 0) * M (1, 3) * M (2, 2) * M (3, 1) +
  M (0, 1) * M (1, 0) * M (2, 2) * M (3, 3) +
  M (0, 1) * M (1, 0) * M (2, 3) * M (3, 2) +
  M (0, 1) * M (1, 2) * M (2, 0) * M (3, 3) +
  M (0, 1) * M (1, 2) * M (2, 3) * M (3, 0) +
  M (0, 1) * M (1, 3) * M (2, 0) * M (3, 2) +
  M (0, 1) * M (1, 3) * M (2, 2) * M (3, 0) +
  M (0, 2) * M (1, 0) * M (2, 1) * M (3, 3) +
  M (0, 2) * M (1, 0) * M (2, 3) * M (3, 1) +
  M (0, 2) * M (1, 1) * M (2, 0) * M (3, 3) +
  M (0, 2) * M (1, 1) * M (2, 3) * M (3, 0) +
  M (0, 2) * M (1, 3) * M (2, 0) * M (3, 1) +
  M (0, 2) * M (1, 3) * M (2, 1) * M (3, 0) +
  M (0, 3) * M (1, 0) * M (2, 1) * M (3, 2) +
  M (0, 3) * M (1, 0) * M (2, 2) * M (3, 1) +
  M (0, 3) * M (1, 1) * M (2, 0) * M (3, 2) +
  M (0, 3) * M (1, 1) * M (2, 2) * M (3, 0) +
  M (0, 3) * M (1, 2) * M (2, 0) * M (3, 1) +
  M (0, 3) * M (1, 2) * M (2, 1) * M (3, 0)

def mn4 : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) where
  toFun X := fun q => X (q.1.succ, q.2.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def row4 : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun X := fun k => X (0, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cofc0 (X : Fin 4 × Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![p3 (fun q => X (![1, 2, 3] q.1, q.2.succ)), p3 (fun q => X (![0, 2, 3] q.1, q.2.succ)),
    p3 (fun q => X (![0, 1, 3] q.1, q.2.succ)), p3 (fun q => X (![0, 1, 2] q.1, q.2.succ))]

def colv (y : Fin 4 → ℂ) : Fin 4 × Fin 4 → ℂ := fun q => if q.2 = 0 then y q.1 else 0

def colz (b : Fin 3) : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) where
  toFun z := fun q => if q.2 = b then z (q.1.succ, 0) else 0
  map_add' x y := by
    funext q; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by
    funext q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

def e2b (u v : Fin 4 × Fin 4 → ℂ) : ℂ :=
  (∑ a : Fin 4, ∑ k : Fin 4, u (a, k)) * (∑ a : Fin 4, ∑ k : Fin 4, v (a, k)) -
  ∑ a : Fin 4, (∑ k : Fin 4, u (a, k)) * (∑ k : Fin 4, v (a, k)) -
  ∑ k : Fin 4, (∑ a : Fin 4, u (a, k)) * (∑ a : Fin 4, v (a, k)) +
  ∑ a : Fin 4, ∑ k : Fin 4, u (a, k) * v (a, k)

theorem p4_smul (c : ℂ) (M : Fin 4 × Fin 4 → ℂ) : p4 (c • M) = c ^ 4 * p4 M := by
  simp [p4]; ring

theorem p4_lap (M : Fin 4 × Fin 4 → ℂ) (h1 : M (0, 1) = 0) (h2 : M (0, 2) = 0)
    (h3 : M (0, 3) = 0) : p4 M = M (0, 0) * p3 (mn4 M) := by
  simp [p4, p3, mn4, h1, h2, h3]; ring

theorem p3_interp4 (A B : Fin 3 × Fin 3 → ℂ) :
    p3 A = 4 * p3 (A + (1 : ℂ) • B) - 6 * p3 (A + (2 : ℂ) • B) + 4 * p3 (A + (3 : ℂ) • B) -
      p3 (A + (4 : ℂ) • B) := by
  simp [p3]; ring

theorem p4_colv (X : Fin 4 × Fin 4 → ℂ) (y : Fin 4 → ℂ) :
    p4 (X + colv y) = p4 X + ∑ i, y i * cofc0 X i := by
  simp [p4, colv, cofc0, p3, Fin.sum_univ_four]; ring

theorem sum_id (y : Fin 4 × Fin 4 → ℂ) :
    72 * (∑ a : Fin 4, ∑ k : Fin 4, y (a, k)) = 8 * (p4 (J4 + y) - p4 (J4 - y)) -
      (p4 (J4 + (2 : ℂ) • y) - p4 (J4 - (2 : ℂ) • y)) := by
  simp [p4, J4, Fin.sum_univ_four]; ring

theorem e2_id (y : Fin 4 × Fin 4 → ℂ) :
    24 * e2b y y = 16 * (p4 (J4 + y) + p4 (J4 - y)) -
      (p4 (J4 + (2 : ℂ) • y) + p4 (J4 - (2 : ℂ) • y)) - 720 := by
  simp [p4, J4, e2b, Fin.sum_univ_four]; ring

theorem e2b_add (u v : Fin 4 × Fin 4 → ℂ) :
    e2b (u + v) (u + v) = e2b u u + e2b v v + 2 * e2b u v := by
  simp [e2b, Fin.sum_univ_four]; ring


theorem phi_id (b : Fin 3) (X1 W z : Fin 4 × Fin 4 → ℂ) (hz0 : z (0, 0) = 0)
    (h1 : X1 (0, 1) = 0) (h2 : X1 (0, 2) = 0) (h3 : X1 (0, 3) = 0)
    (hW : ∀ k : Fin 3, W (0, k.succ) = if k = b then 1 else 0) :
    12 * (p3 (mn4 X1 + colz b z) - p3 (mn4 X1)) =
      8 * ((∑ i, z (i, 0) * cofc0 (X1 + W) i) - ∑ i, z (i, 0) * cofc0 (X1 - W) i) -
      ((∑ i, z (i, 0) * cofc0 (X1 + (2 : ℂ) • W) i) - ∑ i, z (i, 0) * cofc0 (X1 - (2 : ℂ) • W) i) := by
  have w1 : W (0, 1) = if (0 : Fin 3) = b then 1 else 0 := hW 0
  have w2 : W (0, 2) = if (1 : Fin 3) = b then 1 else 0 := hW 1
  have w3 : W (0, 3) = if (2 : Fin 3) = b then 1 else 0 := hW 2
  fin_cases b <;> simp at w1 w2 w3 <;>
    simp [p3, mn4, colz, cofc0, Fin.sum_univ_four, h1, h2, h3, w1, w2, w3, hz0] <;> ring

theorem alg_contra (a0 b0 c0 a1 b1 c1 a2 b2 c2 : ℂ) (s0 : a0 + b0 + c0 = 0)
    (s1 : a1 + b1 + c1 = 0) (s2 : a2 + b2 + c2 = 0)
    (o00 : a0 * a0 + b0 * b0 + c0 * c0 = 0) (o11 : a1 * a1 + b1 * b1 + c1 * c1 = 0)
    (o22 : a2 * a2 + b2 * b2 + c2 * c2 = 0) (o01 : a0 * a1 + b0 * b1 + c0 * c1 = 0)
    (o02 : a0 * a2 + b0 * b2 + c0 * c2 = 0)
    (hp : a0 * b1 * c2 + a0 * c1 * b2 + b0 * a1 * c2 + b0 * c1 * a2 + c0 * a1 * b2 +
      c0 * b1 * a2 = 0)
    (n0 : ¬ (a0 = 0 ∧ b0 = 0 ∧ c0 = 0)) (n1 : ¬ (a1 = 0 ∧ b1 = 0 ∧ c1 = 0))
    (n2 : ¬ (a2 = 0 ∧ b2 = 0 ∧ c2 = 0)) : False := by
  have hc0 : c0 = -a0 - b0 := by linear_combination s0
  have hc1 : c1 = -a1 - b1 := by linear_combination s1
  have hc2 : c2 = -a2 - b2 := by linear_combination s2
  subst hc0 hc1 hc2
  have nz : ∀ a b : ℂ, a * a + b * b + (-a - b) * (-a - b) = 0 → ¬ (a = 0 ∧ b = 0 ∧ -a - b = 0) →
      a ≠ 0 ∧ b ≠ 0 ∧ -a - b ≠ 0 := by
    intro a b ho hn
    refine ⟨?_, ?_, ?_⟩
    · intro ha
      apply hn
      have hb : b = 0 := by
        have : 2 * b ^ 2 = 0 := by rw [ha] at ho; linear_combination ho
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using this)
      exact ⟨ha, hb, by rw [ha, hb]; ring⟩
    · intro hb
      apply hn
      have ha : a = 0 := by
        have : 2 * a ^ 2 = 0 := by rw [hb] at ho; linear_combination ho
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using this)
      exact ⟨ha, hb, by rw [ha, hb]; ring⟩
    · intro hab
      apply hn
      have hb : b = -a := by linear_combination -hab
      have ha : a = 0 := by
        have : 2 * a ^ 2 = 0 := by rw [hb] at ho; linear_combination ho
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using this)
      exact ⟨ha, by rw [hb, ha]; ring, hab⟩
  obtain ⟨ha0, hb0, hcc0⟩ := nz a0 b0 o00 n0
  obtain ⟨ha1, -, -⟩ := nz a1 b1 o11 n1
  obtain ⟨ha2, -, -⟩ := nz a2 b2 o22 n2
  have d1 : a0 * b1 - a1 * b0 = 0 := by
    have : 3 * (a0 * b1 - a1 * b0) ^ 2 = 0 := by linear_combination (a0 * a0 + b0 * b0 + (-a0 - b0) * (-a0 - b0)) * o11 -
        (a0 * a1 + b0 * b1 + (-a0 - b0) * (-a1 - b1)) * o01
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using this)
  have d2 : a0 * b2 - a2 * b0 = 0 := by
    have : 3 * (a0 * b2 - a2 * b0) ^ 2 = 0 := by linear_combination (a0 * a0 + b0 * b0 + (-a0 - b0) * (-a0 - b0)) * o22 -
        (a0 * a2 + b0 * b2 + (-a0 - b0) * (-a2 - b2)) * o02
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using this)
  have key : a0 ^ 2 * (a0 * b1 * (-a2 - b2) + a0 * (-a1 - b1) * b2 + b0 * a1 * (-a2 - b2) +
      b0 * (-a1 - b1) * a2 + (-a0 - b0) * a1 * b2 + (-a0 - b0) * b1 * a2) =
      6 * a0 * a1 * a2 * b0 * (-a0 - b0) := by
    linear_combination (a0 * a0 * (-a2 - b2) - a0 * a0 * b2 - b0 * a0 * a2 + (-a0 - b0) * a0 * a2) * d1 +
      (-a0 * a1 * b0 + a0 * a1 * (-a0 - b0) - b0 * a0 * a1 + (-a0 - b0) * a0 * a1) * d2
  rw [hp, mul_zero] at key
  have : (6 : ℂ) * a0 * a1 * a2 * b0 * (-a0 - b0) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha0) ha1) ha2) hb0) hcc0
  exact this key.symm


theorem e2_struct (c : Fin 3) (zb X zc : Fin 4 × Fin 4 → ℂ)
    (hzb : ∀ i k : Fin 4, k ≠ 0 → zb (i, k) = 0) (hzb0 : zb (0, 0) = 0)
    (hX0 : ∀ k, X (0, k) = 0) (hXc : mn4 X = colz c zc) :
    e2b zb X = (zb (1, 0) + zb (2, 0) + zb (3, 0)) * (∑ a : Fin 4, ∑ k : Fin 4, X (a, k)) -
      (zb (1, 0) + zb (2, 0) + zb (3, 0)) * (X (0, 0) + X (1, 0) + X (2, 0) + X (3, 0)) -
      (zb (1, 0) * zc (1, 0) + zb (2, 0) * zc (2, 0) + zb (3, 0) * zc (3, 0)) := by
  have hm : ∀ i k : Fin 3, X (i.succ, k.succ) = if k = c then zc (i.succ, 0) else 0 :=
    fun i k => congrFun hXc (i, k)
  have m00 : X (1, 1) = if (0 : Fin 3) = c then zc (1, 0) else 0 := hm 0 0
  have m01 : X (1, 2) = if (1 : Fin 3) = c then zc (1, 0) else 0 := hm 0 1
  have m02 : X (1, 3) = if (2 : Fin 3) = c then zc (1, 0) else 0 := hm 0 2
  have m10 : X (2, 1) = if (0 : Fin 3) = c then zc (2, 0) else 0 := hm 1 0
  have m11 : X (2, 2) = if (1 : Fin 3) = c then zc (2, 0) else 0 := hm 1 1
  have m12 : X (2, 3) = if (2 : Fin 3) = c then zc (2, 0) else 0 := hm 1 2
  have m20 : X (3, 1) = if (0 : Fin 3) = c then zc (3, 0) else 0 := hm 2 0
  have m21 : X (3, 2) = if (1 : Fin 3) = c then zc (3, 0) else 0 := hm 2 1
  have m22 : X (3, 3) = if (2 : Fin 3) = c then zc (3, 0) else 0 := hm 2 2
  have z01 : zb (0, 1) = 0 := hzb 0 1 (by decide)
  have z02 : zb (0, 2) = 0 := hzb 0 2 (by decide)
  have z03 : zb (0, 3) = 0 := hzb 0 3 (by decide)
  have z11 : zb (1, 1) = 0 := hzb 1 1 (by decide)
  have z12 : zb (1, 2) = 0 := hzb 1 2 (by decide)
  have z13 : zb (1, 3) = 0 := hzb 1 3 (by decide)
  have z21 : zb (2, 1) = 0 := hzb 2 1 (by decide)
  have z22 : zb (2, 2) = 0 := hzb 2 2 (by decide)
  have z23 : zb (2, 3) = 0 := hzb 2 3 (by decide)
  have z31 : zb (3, 1) = 0 := hzb 3 1 (by decide)
  have z32 : zb (3, 2) = 0 := hzb 3 2 (by decide)
  have z33 : zb (3, 3) = 0 := hzb 3 3 (by decide)
  have x0 := hX0 0; have x1 := hX0 1; have x2 := hX0 2; have x3 := hX0 3
  fin_cases c <;> simp at m00 m01 m02 m10 m11 m12 m20 m21 m22 <;>
    simp only [e2b, Fin.sum_univ_four, m00, m01, m02, m10, m11, m12, m20, m21, m22, z01, z02, z03, z11, z12, z13, z21, z22, z23, z31, z32, z33, x0, x1, x2, x3, hzb0] <;> ring


theorem colv_of (z : Fin 4 × Fin 4 → ℂ) (hz : ∀ i k : Fin 4, k ≠ 0 → z (i, k) = 0) :
    z = colv (fun i => z (i, 0)) := by
  funext q
  obtain ⟨i, k⟩ := q
  by_cases hk : k = 0
  · subst hk; simp [colv]
  · simp [colv, hk, hz i k hk]

theorem main_core (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {J4}, ∀ y ∈ L, p4 (X + y) = p4 X)
    (hdim : 7 ≤ Module.finrank ℂ L)
    (Xs : Fin 4 × Fin 4 → ℂ) (hXsC : Xs ∈ L ⊔ Submodule.span ℂ {J4})
    (hXs0 : Xs (0, 0) = 1) (hXs1 : Xs (0, 1) = 0) (hXs2 : Xs (0, 2) = 0) (hXs3 : Xs (0, 3) = 0)
    (hXsne : p4 Xs ≠ 0)
    (W : Fin 3 → Fin 4 × Fin 4 → ℂ) (hWC : ∀ b, W b ∈ L ⊔ Submodule.span ℂ {J4})
    (hWr : ∀ b k : Fin 3, W b (0, k.succ) = if k = b then 1 else 0) : False := by
  set C := L ⊔ Submodule.span ℂ {J4} with hC
  have hLC : L ≤ C := le_sup_left
  have hJC : J4 ∈ C := Submodule.mem_sup_right (Submodule.mem_span_singleton_self J4)
  have hsum : ∀ y ∈ L, ∑ a : Fin 4, ∑ k : Fin 4, y (a, k) = 0 := by
    intro y hy
    have e := sum_id y
    have h1 := hinv J4 hJC y hy
    have h2 := hinv J4 hJC (-y) (L.neg_mem hy)
    have h3 := hinv J4 hJC ((2 : ℂ) • y) (L.smul_mem _ hy)
    have h4 := hinv J4 hJC (-((2 : ℂ) • y)) (L.neg_mem (L.smul_mem _ hy))
    rw [← sub_eq_add_neg] at h2 h4
    rw [h1, h2, h3, h4] at e
    linear_combination e / 72
  have he2 : ∀ u ∈ L, ∀ v ∈ L, e2b u v = 0 := by
    have hd : ∀ y ∈ L, e2b y y = 0 := by
      intro y hy
      have e := e2_id y
      have h1 := hinv J4 hJC y hy
      have h2 := hinv J4 hJC (-y) (L.neg_mem hy)
      have h3 := hinv J4 hJC ((2 : ℂ) • y) (L.smul_mem _ hy)
      have h4 := hinv J4 hJC (-((2 : ℂ) • y)) (L.neg_mem (L.smul_mem _ hy))
      rw [← sub_eq_add_neg] at h2 h4
      rw [h1, h2, h3, h4] at e
      have hJ : p4 J4 = 24 := by simp [p4, J4]; norm_num
      rw [hJ] at e
      linear_combination e / 24
    intro u hu v hv
    have e := e2b_add u v
    rw [hd u hu, hd v hv, hd (u + v) (L.add_mem hu hv)] at e
    linear_combination -e / 2
  have hrowL : Module.finrank ℂ (L.map row4) ≤ 3 := by
    have hne : L.map row4 ≠ ⊤ := by
      intro htop
      have : (Pi.single 0 1 : Fin 4 → ℂ) ∈ L.map row4 := by rw [htop]; trivial
      obtain ⟨y, hy, hyr⟩ := Submodule.mem_map.1 this
      have e := hinv Xs hXsC (-y) (L.neg_mem hy)
      have h0 : p4 (Xs + -y) = 0 := by
        have r0 := congrFun hyr 0
        have r1 := congrFun hyr 1
        have r2 := congrFun hyr 2
        have r3 := congrFun hyr 3
        simp [row4] at r0 r1 r2 r3
        simp [p4, r0, r1, r2, r3, hXs0, hXs1, hXs2, hXs3]
      exact hXsne (e ▸ h0)
    have h3 := Submodule.finrank_lt hne
    rw [Module.finrank_fin_fun] at h3
    omega
  set K := L ⊓ LinearMap.ker row4 with hK
  have hKdim : Module.finrank ℂ L ≤ Module.finrank ℂ K + 3 := by
    have h := rank_nullity L row4
    rw [show L ⊓ LinearMap.ker row4 = K from rfl] at h
    omega
  have hKr : ∀ z ∈ K, ∀ k, z (0, k) = 0 := fun z hz k =>
    congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hz).2) k
  have KL : ∀ z ∈ K, ∀ c : ℂ, p3 (mn4 z + c • mn4 Xs) = c ^ 3 * p4 Xs := by
    intro z hz c
    have hzL : z ∈ L := (Submodule.mem_inf.1 hz).1
    have z0 := hKr z hz 0
    have z1 := hKr z hz 1
    have z2 := hKr z hz 2
    have z3 := hKr z hz 3
    have main : ∀ c : ℂ, c ≠ 0 → p3 (mn4 z + c • mn4 Xs) = c ^ 3 * p4 Xs := by
      intro c hc
      have e := hinv (c • Xs) (C.smul_mem c hXsC) z hzL
      rw [p4_smul] at e
      have e2 := p4_lap (c • Xs + z) (by simp [hXs1, z1]) (by simp [hXs2, z2]) (by simp [hXs3, z3])
      rw [e] at e2
      have hm : mn4 (c • Xs + z) = mn4 z + c • mn4 Xs := by
        rw [map_add, map_smul, add_comm]
      rw [hm] at e2
      simp [hXs0, z0] at e2
      have : c * (p3 (mn4 z + c • mn4 Xs) - c ^ 3 * p4 Xs) = 0 := by linear_combination -e2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc
      · linear_combination h
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero, p3_interp4 (mn4 z) (mn4 Xs), main 1 one_ne_zero,
        main 2 two_ne_zero, main 3 three_ne_zero, main 4 (by norm_num)]
      ring
    · exact main c hc
  have hP : p3 (mn4 Xs) = p4 Xs := by
    have h := KL 0 K.zero_mem 1
    rwa [map_zero, zero_add, one_smul, one_pow, one_mul] at h
  set L3 := K.map mn4 with hL3
  have hF3 : Module.finrank ℂ L3 ≤ 3 := by
    apply F3 L3 (mn4 Xs)
    · intro M hM m hm
      obtain ⟨m1, hm1, M', hM', rfl⟩ := Submodule.mem_sup.1 hM
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hM'
      obtain ⟨z1, hz1, rfl⟩ := Submodule.mem_map.1 hm1
      obtain ⟨z2, hz2, rfl⟩ := Submodule.mem_map.1 hm
      have e1 := KL z1 hz1 c
      have e2 := KL (z1 + z2) (K.add_mem hz1 hz2) c
      rw [map_add] at e2
      rw [show mn4 z1 + c • mn4 Xs + mn4 z2 = mn4 z1 + mn4 z2 + c • mn4 Xs by abel, e2, e1]
    · rw [hP]; exact hXsne
  set Z := K ⊓ LinearMap.ker mn4 with hZ
  have hZdim : Module.finrank ℂ K = Module.finrank ℂ L3 + Module.finrank ℂ Z := by
    have h := rank_nullity K mn4
    rw [show K ⊓ LinearMap.ker mn4 = Z from rfl, show K.map mn4 = L3 from rfl] at h
    omega
  have hZK : ∀ z ∈ Z, z ∈ K := fun z hz => (Submodule.mem_inf.1 hz).1
  have hZe : ∀ z ∈ Z, ∀ i k : Fin 4, k ≠ 0 → z (i, k) = 0 := by
    intro z hz i k hk
    have hzm : mn4 z = 0 := (Submodule.mem_inf.1 hz).2
    obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.2 hk
    by_cases hi : i = 0
    · subst hi; exact hKr z (hZK z hz) _
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
      exact congrFun hzm (i', k')
  have hZ00 : ∀ z ∈ Z, z (0, 0) = 0 := fun z hz => hKr z (hZK z hz) 0
  have hPhi : ∀ z ∈ Z, ∀ X1 ∈ C, X1 (0, 1) = 0 → X1 (0, 2) = 0 → X1 (0, 3) = 0 →
      ∀ b, p3 (mn4 X1 + colz b z) = p3 (mn4 X1) := by
    intro z hz X1 hX1 h1 h2 h3 b
    have hzL : z ∈ L := (Submodule.mem_inf.1 (hZK z hz)).1
    have hf : ∀ X ∈ C, ∑ i, z (i, 0) * cofc0 X i = 0 := by
      intro X hX
      have e := hinv X hX z hzL
      rw [colv_of z (hZe z hz), p4_colv] at e
      linear_combination e
    have e := phi_id b X1 (W b) z (hZ00 z hz) h1 h2 h3 (hWr b)
    rw [hf _ (C.add_mem hX1 (hWC b)), hf _ (C.sub_mem hX1 (hWC b)),
      hf _ (C.add_mem hX1 (C.smul_mem _ (hWC b))), hf _ (C.sub_mem hX1 (C.smul_mem _ (hWC b)))] at e
    linear_combination e / 12

  have hKdim4 : 4 ≤ Module.finrank ℂ K := by omega
  have S5 : ∀ b : Fin 3, ∃ X ∈ K, ∃ z ∈ Z, z ≠ 0 ∧ mn4 X = colz b z := by
    intro b
    set Yb := Z.map (colz b) with hYb
    have hYdim : Module.finrank ℂ Yb = Module.finrank ℂ Z := by
      have h := rank_nullity Z (colz b)
      have hbot : Z ⊓ LinearMap.ker (colz b) = ⊥ := by
        rw [eq_bot_iff]; intro z hz
        obtain ⟨hzZ, hzk⟩ := Submodule.mem_inf.1 hz
        rw [Submodule.mem_bot]
        have hk : colz b z = 0 := hzk
        have hcol : (fun i => z (i, 0)) = 0 := by
          funext i
          by_cases hi : i = 0
          · subst hi; exact hZ00 z hzZ
          · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
            have := congrFun hk (i', b)
            simpa [colz] using this
        rw [colv_of z (hZe z hzZ), hcol]
        funext q; simp [colv]
      rw [hbot, finrank_bot, add_zero] at h
      exact h
    have hstep : ∀ z' ∈ K, ∀ c : ℂ, ∀ yb ∈ Yb,
        p3 (mn4 z' + c • mn4 Xs + yb) = c ^ 3 * p4 Xs := by
      intro z' hz' c yb hyb
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hyb
      have hX1 : z' + c • Xs ∈ C :=
        C.add_mem (hLC (Submodule.mem_inf.1 hz').1) (C.smul_mem c hXsC)
      have e := hPhi z hz (z' + c • Xs) hX1 (by simp [hKr z' hz' 1, hXs1])
        (by simp [hKr z' hz' 2, hXs2]) (by simp [hKr z' hz' 3, hXs3]) b
      rw [map_add, map_smul] at e
      rw [e, KL z' hz' c]
    have hinvb : ∀ M ∈ (L3 ⊔ Yb) ⊔ Submodule.span ℂ {mn4 Xs}, ∀ m ∈ L3 ⊔ Yb,
        p3 (M + m) = p3 M := by
      intro M hM m hm
      obtain ⟨M1, hM1, M', hM', rfl⟩ := Submodule.mem_sup.1 hM
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hM'
      obtain ⟨m1, hm1, y1, hy1, rfl⟩ := Submodule.mem_sup.1 hM1
      obtain ⟨m2, hm2, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hm
      obtain ⟨z1, hz1, rfl⟩ := Submodule.mem_map.1 hm1
      obtain ⟨z2, hz2, rfl⟩ := Submodule.mem_map.1 hm2
      have e1 := hstep z1 hz1 c y1 hy1
      have e2 := hstep (z1 + z2) (K.add_mem hz1 hz2) c (y1 + y2) (Yb.add_mem hy1 hy2)
      rw [map_add] at e2
      rw [show mn4 z1 + y1 + c • mn4 Xs + (mn4 z2 + y2) =
          mn4 z1 + mn4 z2 + c • mn4 Xs + (y1 + y2) by abel, e2,
        show mn4 z1 + y1 + c • mn4 Xs = mn4 z1 + c • mn4 Xs + y1 by abel, e1]
    have hF3b := F3 (L3 ⊔ Yb) (mn4 Xs) hinvb (by rw [hP]; exact hXsne)
    have hsi := Submodule.finrank_sup_add_finrank_inf_eq L3 Yb
    have hpos : 1 ≤ Module.finrank ℂ ↥(L3 ⊓ Yb) := by omega
    have hne : L3 ⊓ Yb ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hpos; omega
    obtain ⟨M, hM, hM0⟩ := Submodule.ne_bot_iff _ |>.1 hne
    obtain ⟨hML, hMY⟩ := Submodule.mem_inf.1 hM
    obtain ⟨X, hX, rfl⟩ := Submodule.mem_map.1 hML
    obtain ⟨z, hz, hzX⟩ := Submodule.mem_map.1 hMY
    refine ⟨X, hX, z, hz, ?_, hzX.symm⟩
    intro hz0; apply hM0; rw [← hzX, hz0, map_zero]
  have hzL : ∀ z ∈ Z, z ∈ L := fun z hz => (Submodule.mem_inf.1 (hZK z hz)).1
  have hXL : ∀ X ∈ K, X ∈ L := fun X hX => (Submodule.mem_inf.1 hX).1
  have hs : ∀ z ∈ Z, z (1, 0) + z (2, 0) + z (3, 0) = 0 := by
    intro z hz
    have e := hsum z (hzL z hz)
    rw [colv_of z (hZe z hz)] at e
    simp [colv, Fin.sum_univ_four, hZ00 z hz] at e
    linear_combination e
  have hor : ∀ z ∈ Z, ∀ c : Fin 3, ∀ X ∈ K, ∀ zc ∈ Z, mn4 X = colz c zc →
      z (1, 0) * zc (1, 0) + z (2, 0) * zc (2, 0) + z (3, 0) * zc (3, 0) = 0 := by
    intro z hz c X hX zc hzc hmX
    have e := e2_struct c z X zc (hZe z hz) (hZ00 z hz) (hKr X hX) hmX
    rw [he2 z (hzL z hz) X (hXL X hX), hsum X (hXL X hX), hs z hz] at e
    linear_combination e
  have hnz : ∀ z ∈ Z, z ≠ 0 → ¬ (z (1, 0) = 0 ∧ z (2, 0) = 0 ∧ z (3, 0) = 0) := by
    intro z hz hz0 h
    apply hz0
    obtain ⟨h1, h2, h3⟩ := h
    have hcol : (fun i => z (i, 0)) = 0 := by
      funext i
      fin_cases i
      · exact hZ00 z hz
      · exact h1
      · exact h2
      · exact h3
    rw [colv_of z (hZe z hz), hcol]
    funext q; simp [colv]
  obtain ⟨Y0, hY0, z0, hz0, hz0ne, hm0⟩ := S5 0
  obtain ⟨Y1, hY1, z1, hz1, hz1ne, hm1⟩ := S5 1
  obtain ⟨Y2, hY2, z2, hz2, hz2ne, hm2⟩ := S5 2
  have hperm : p3 (mn4 (Y0 + Y1 + Y2)) = 0 := by
    have h := KL (Y0 + Y1 + Y2) (K.add_mem (K.add_mem hY0 hY1) hY2) 0
    simpa using h
  rw [map_add, map_add, hm0, hm1, hm2] at hperm
  simp [p3, colz] at hperm
  exact alg_contra (z0 (1, 0)) (z0 (2, 0)) (z0 (3, 0)) (z1 (1, 0)) (z1 (2, 0)) (z1 (3, 0))
    (z2 (1, 0)) (z2 (2, 0)) (z2 (3, 0)) (hs z0 hz0) (hs z1 hz1) (hs z2 hz2)
    (hor z0 hz0 0 Y0 hY0 z0 hz0 hm0) (hor z1 hz1 1 Y1 hY1 z1 hz1 hm1)
    (hor z2 hz2 2 Y2 hY2 z2 hz2 hm2) (hor z0 hz0 1 Y1 hY1 z1 hz1 hm1)
    (hor z0 hz0 2 Y2 hY2 z2 hz2 hm2) (by linear_combination hperm)
    (hnz z0 hz0 hz0ne) (hnz z1 hz1 hz1ne) (hnz z2 hz2 hz2ne)


def rowr4 (r : Fin 4) : (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun X := fun k => X (r, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem p4_row_zero (r : Fin 4) (X : Fin 4 × Fin 4 → ℂ) (h : ∀ k, X (r, k) = 0) : p4 X = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  fin_cases r <;> simp only [p4] <;> simp_all

theorem p4_perm (r j : Fin 4) (X : Fin 4 × Fin 4 → ℂ) :
    p4 (X ∘ Equiv.prodCongr (Equiv.swap 0 r) (Equiv.swap 0 j)) = p4 X := by
  fin_cases r <;> fin_cases j <;>
    simp (config := { decide := true }) [p4, Equiv.swap_apply_def] <;> ring

def one4 : Fin 4 → ℂ := fun _ => 1

theorem not_mem_of_orth (S : Submodule ℂ (Fin 4 → ℂ)) (v : Fin 4 → ℂ)
    (hv : ∀ s ∈ S, dotProduct v s = 0) (hvv : dotProduct v v ≠ 0) : v ∉ S :=
  fun h => hvv (hv v h)

theorem orth_sup (S : Submodule ℂ (Fin 4 → ℂ)) (u v : Fin 4 → ℂ)
    (hS : ∀ s ∈ S, dotProduct v s = 0) (hu : dotProduct v u = 0) :
    ∀ s ∈ S ⊔ Submodule.span ℂ {u}, dotProduct v s = 0 := by
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
  rw [dotProduct_add, dotProduct_smul, hS a ha, hu, smul_zero, add_zero]

theorem orth_span (u v : Fin 4 → ℂ) (hu : dotProduct v u = 0) :
    ∀ s ∈ Submodule.span ℂ {u}, dotProduct v s = 0 := by
  intro s hs
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
  rw [dotProduct_smul, hu, smul_zero]

theorem dot_one (x : Fin 4 → ℂ) : dotProduct x one4 = ∑ i, x i := by
  simp [dotProduct, one4]

theorem one_one : dotProduct one4 one4 = 4 := by
  simp [dotProduct, one4]

theorem dec3 (x y z : Fin 4 → ℂ) (hx1 : ∑ i, x i = 0) (hy1 : ∑ i, y i = 0) (hz1 : ∑ i, z i = 0)
    (hxy : dotProduct x y = 0) (hqx : dotProduct x x ≠ 0) (hqy : dotProduct y y ≠ 0)
    (hzx : dotProduct z x = 0) (hzy : dotProduct z y = 0) (hz : z ≠ 0) :
    dotProduct z z ≠ 0 := by
  intro hzz
  set S1 := Submodule.span ℂ {one4}
  set S2 := S1 ⊔ Submodule.span ℂ {x}
  set S3 := S2 ⊔ Submodule.span ℂ {y}
  have h1 : (one4 : Fin 4 → ℂ) ≠ 0 := by
    intro h; have := congrFun h 0; simp [one4] at this
  have d1 : finrank ℂ S1 = 1 := finrank_span_singleton h1
  have hx1' : dotProduct x one4 = 0 := by rw [dot_one]; exact hx1
  have hy1' : dotProduct y one4 = 0 := by rw [dot_one]; exact hy1
  have hz1' : dotProduct z one4 = 0 := by rw [dot_one]; exact hz1
  have ox : ∀ s ∈ S1, dotProduct x s = 0 := orth_span one4 x hx1'
  have d2 : finrank ℂ S2 = 2 := by
    rw [finrank_sup_span S1 x (not_mem_of_orth S1 x ox hqx), d1]
  have oy : ∀ s ∈ S2, dotProduct y s = 0 :=
    orth_sup S1 x y (orth_span one4 y hy1') (by rw [dotProduct_comm]; exact hxy)
  have d3 : finrank ℂ S3 = 3 := by
    rw [finrank_sup_span S2 y (not_mem_of_orth S2 y oy hqy), d2]
  have oz : ∀ s ∈ S3, dotProduct z s = 0 :=
    orth_sup S2 y z (orth_sup S1 x z (orth_span one4 z hz1') hzx) hzy
  have hzS3 : z ∉ S3 := by
    intro hm
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hm
    obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.1 hb
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hb'
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 ha'
    have h1x : dotProduct one4 x = 0 := by rw [dotProduct_comm]; exact hx1'
    have h1y : dotProduct one4 y = 0 := by rw [dotProduct_comm]; exact hy1'
    have hyx : dotProduct y x = 0 := by rw [dotProduct_comm]; exact hxy
    have e1 := hz1'
    have e2 := hzx
    have e3 := hzy
    rw [← hab] at e1 e2 e3
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, h1x, h1y, hyx, hxy, hx1', hy1',
      one_one] at e1 e2 e3
    have hα : α = 0 := by linear_combination e1 / 4
    have hβ : β = 0 := by
      have : β * dotProduct x x = 0 := by linear_combination e2
      exact (mul_eq_zero.1 this).resolve_right hqx
    have hγ : γ = 0 := by
      have : γ * dotProduct y y = 0 := by linear_combination e3
      exact (mul_eq_zero.1 this).resolve_right hqy
    apply hz
    rw [← hab, hα, hβ, hγ]; simp
  have d4 : finrank ℂ ↥(S3 ⊔ Submodule.span ℂ {z}) = 4 := by
    rw [finrank_sup_span S3 z hzS3, d3]
  have hb := orth_bound (Submodule.span ℂ {z}) (S3 ⊔ Submodule.span ℂ {z}) (by
    intro a ha b hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    rw [smul_dotProduct, orth_sup S3 z z oz hzz b hb, smul_zero])
  rw [d4, finrank_span_singleton hz] at hb
  simp at hb


theorem aniso5 (x y z u : Fin 4 → ℂ) (hx1 : ∑ i, x i = 0) (hy1 : ∑ i, y i = 0)
    (hz1 : ∑ i, z i = 0) (hu1 : ∑ i, u i = 0)
    (hxy : dotProduct x y = 0) (hxz : dotProduct x z = 0) (hxu : dotProduct x u = 0)
    (hyz : dotProduct y z = 0) (hyu : dotProduct y u = 0) (hzu : dotProduct z u = 0)
    (qx : dotProduct x x ≠ 0) (qy : dotProduct y y ≠ 0) (qz : dotProduct z z ≠ 0)
    (qu : dotProduct u u ≠ 0) : False := by
  set S1 := Submodule.span ℂ {one4}
  have h1 : (one4 : Fin 4 → ℂ) ≠ 0 := by
    intro h; have := congrFun h 0; simp [one4] at this
  have d1 : finrank ℂ S1 = 1 := finrank_span_singleton h1
  have o1 : ∀ v : Fin 4 → ℂ, ∑ i, v i = 0 → ∀ s ∈ S1, dotProduct v s = 0 :=
    fun v hv => orth_span one4 v (by rw [dot_one]; exact hv)
  have c := fun (a b : Fin 4 → ℂ) (h : dotProduct a b = 0) => (by rw [dotProduct_comm]; exact h :
    dotProduct b a = 0)
  set S2 := S1 ⊔ Submodule.span ℂ {x}
  have d2 : finrank ℂ S2 = 2 := by
    rw [finrank_sup_span S1 x (not_mem_of_orth S1 x (o1 x hx1) qx), d1]
  set S3 := S2 ⊔ Submodule.span ℂ {y}
  have oy : ∀ s ∈ S2, dotProduct y s = 0 := orth_sup S1 x y (o1 y hy1) (c x y hxy)
  have d3 : finrank ℂ S3 = 3 := by
    rw [finrank_sup_span S2 y (not_mem_of_orth S2 y oy qy), d2]
  set S4 := S3 ⊔ Submodule.span ℂ {z}
  have oz : ∀ s ∈ S3, dotProduct z s = 0 :=
    orth_sup S2 y z (orth_sup S1 x z (o1 z hz1) (c x z hxz)) (c y z hyz)
  have d4 : finrank ℂ S4 = 4 := by
    rw [finrank_sup_span S3 z (not_mem_of_orth S3 z oz qz), d3]
  have ou : ∀ s ∈ S4, dotProduct u s = 0 :=
    orth_sup S3 z u (orth_sup S2 y u (orth_sup S1 x u (o1 u hu1) (c x u hxu)) (c y u hyu))
      (c z u hzu)
  have d5 : finrank ℂ ↥(S4 ⊔ Submodule.span ℂ {u}) = 5 := by
    rw [finrank_sup_span S4 u (not_mem_of_orth S4 u ou qu), d4]
  have := Submodule.finrank_le (S4 ⊔ Submodule.span ℂ {u})
  rw [d5, Module.finrank_fin_fun] at this
  omega

theorem amo_gen (x y z u : Fin 4 → ℂ) (hx1 : ∑ i, x i = 0) (hy1 : ∑ i, y i = 0)
    (hz1 : ∑ i, z i = 0) (hu1 : ∑ i, u i = 0)
    (hxy : dotProduct x y = 0) (hxz : dotProduct x z = 0) (hxu : dotProduct x u = 0)
    (hyz : dotProduct y z = 0) (hyu : dotProduct y u = 0) (hzu : dotProduct z u = 0)
    (hz : z ≠ 0) (hu : u ≠ 0)
    (qx : dotProduct x x ≠ 0) (qy : dotProduct y y ≠ 0) : False := by
  have c := fun (a b : Fin 4 → ℂ) (h : dotProduct a b = 0) => (by rw [dotProduct_comm]; exact h :
    dotProduct b a = 0)
  have qz := dec3 x y z hx1 hy1 hz1 hxy qx qy (c x z hxz) (c y z hyz) hz
  have qu := dec3 x y u hx1 hy1 hu1 hxy qx qy (c x u hxu) (c y u hyu) hu
  exact aniso5 x y z u hx1 hy1 hz1 hu1 hxy hxz hxu hyz hyu hzu qx qy qz qu

theorem prop2 (x y : Fin 4 → ℂ) (hx1 : ∑ i, x i = 0) (hy1 : ∑ i, y i = 0)
    (hxx : dotProduct x x = 0) (hyy : dotProduct y y = 0) (hxy : dotProduct x y = 0)
    (hx : x ≠ 0) : ∃ β : ℂ, y = β • x := by
  by_contra hno
  push Not at hno
  have hyS : y ∉ Submodule.span ℂ {x} := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    exact hno c hc.symm
  set A := Submodule.span ℂ {x} ⊔ Submodule.span ℂ {y}
  have dA : finrank ℂ A = 2 := by
    rw [finrank_sup_span _ y hyS, finrank_span_singleton hx]
  have hx1' : dotProduct x one4 = 0 := by rw [dot_one]; exact hx1
  have hy1' : dotProduct y one4 = 0 := by rw [dot_one]; exact hy1
  have hyx : dotProduct y x = 0 := by rw [dotProduct_comm]; exact hxy
  have hA : ∀ a ∈ A, dotProduct a x = 0 ∧ dotProduct a y = 0 ∧ dotProduct a one4 = 0 := by
    intro a ha
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hs
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 ht
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hxx, hyy, hxy, hyx, hx1', hy1']
    simp
  have h1A : one4 ∉ A := by
    intro h
    have := (hA one4 h).2.2
    rw [one_one] at this; norm_num at this
  have dB : finrank ℂ ↥(A ⊔ Submodule.span ℂ {one4}) = 3 := by
    rw [finrank_sup_span A one4 h1A, dA]
  have hb := orth_bound A (A ⊔ Submodule.span ℂ {one4}) (by
    intro a ha b hb
    have hAa := hA a ha
    have : ∀ s ∈ A, dotProduct a s = 0 := by
      intro s hs
      obtain ⟨s1, hs1, t1, ht1, rfl⟩ := Submodule.mem_sup.1 hs
      obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hs1
      obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 ht1
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hAa.1, hAa.2.1]; simp
    exact orth_sup A one4 a this hAa.2.2 b hb)
  rw [dA, dB] at hb
  simp at hb

theorem pair_zero (s a b : ℂ) (h1 : 2 * s + a + b = 0) (h2 : 2 * s ^ 2 + a ^ 2 + b ^ 2 = 0)
    (h3 : 2 * s ^ 3 + a ^ 3 + b ^ 3 = 0) : s = 0 ∧ a = 0 ∧ b = 0 := by
  have hs3 : 24 * s ^ 3 = 0 := by
    linear_combination 2 * h3 + (6 * s - 3 * (2 * s + a + b)) * h2 +
      (18 * s ^ 2 - 6 * s * (2 * s + a + b) + (2 * s + a + b) ^ 2) * h1
  have hs : s = 0 := by
    have : s ^ 3 = 0 := by linear_combination hs3 / 24
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this
  subst hs
  have hb : b = -a := by linear_combination h1
  subst hb
  have ha : a = 0 := by
    have : a ^ 2 = 0 := by linear_combination h2 / 2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  exact ⟨rfl, ha, by rw [ha]; ring⟩

theorem dist_aux (p q r t : ℂ) (h1 : p + q + r + t = 0) (h2 : p ^ 2 + q ^ 2 + r ^ 2 + t ^ 2 = 0)
    (h3 : p ^ 3 + q ^ 3 + r ^ 3 + t ^ 3 = 0) (hpq : p = q) : p = 0 ∧ q = 0 ∧ r = 0 ∧ t = 0 := by
  subst hpq
  obtain ⟨a, b, c⟩ := pair_zero p r t (by linear_combination h1) (by linear_combination h2)
    (by linear_combination h3)
  exact ⟨a, a, b, c⟩

set_option maxHeartbeats 1000000 in
theorem vand (v x : Fin 4 → ℂ) (s1 : ∑ i, v i = 0) (s2 : ∑ i, v i ^ 2 = 0)
    (s3 : ∑ i, v i ^ 3 = 0) (hv : v ≠ 0) (o0 : ∑ i, x i = 0) (o1 : ∑ i, x i * v i = 0)
    (o2 : ∑ i, x i * v i ^ 2 = 0) (o3 : ∑ i, x i * v i ^ 3 = 0) : x = 0 := by
  simp only [Fin.sum_univ_four] at s1 s2 s3 o0 o1 o2 o3
  have hv' : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0) := by
    intro h
    apply hv
    funext i; fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  have d01 : v 0 ≠ v 1 := by
    intro h
    apply hv'
    obtain ⟨e1, e2, e3, e4⟩ := dist_aux (v 0) (v 1) (v 2) (v 3) (by linear_combination s1)
      (by linear_combination s2) (by linear_combination s3) h
    exact ⟨e1, e2, e3, e4⟩
  have d02 : v 0 ≠ v 2 := by
    intro h
    apply hv'
    obtain ⟨e1, e2, e3, e4⟩ := dist_aux (v 0) (v 2) (v 1) (v 3) (by linear_combination s1)
      (by linear_combination s2) (by linear_combination s3) h
    exact ⟨e1, e3, e2, e4⟩
  have d03 : v 0 ≠ v 3 := by
    intro h
    apply hv'
    obtain ⟨e1, e2, e3, e4⟩ := dist_aux (v 0) (v 3) (v 1) (v 2) (by linear_combination s1)
      (by linear_combination s2) (by linear_combination s3) h
    exact ⟨e1, e3, e4, e2⟩
  have d12 : v 1 ≠ v 2 := by
    intro h
    apply hv'
    obtain ⟨e1, e2, e3, e4⟩ := dist_aux (v 1) (v 2) (v 0) (v 3) (by linear_combination s1)
      (by linear_combination s2) (by linear_combination s3) h
    exact ⟨e3, e1, e2, e4⟩
  have d13 : v 1 ≠ v 3 := by
    intro h
    apply hv'
    obtain ⟨e1, e2, e3, e4⟩ := dist_aux (v 1) (v 3) (v 0) (v 2) (by linear_combination s1)
      (by linear_combination s2) (by linear_combination s3) h
    exact ⟨e3, e1, e4, e2⟩
  have d23 : v 2 ≠ v 3 := by
    intro h
    apply hv'
    obtain ⟨e1, e2, e3, e4⟩ := dist_aux (v 2) (v 3) (v 0) (v 1) (by linear_combination s1)
      (by linear_combination s2) (by linear_combination s3) h
    exact ⟨e3, e4, e1, e2⟩
  have x0 : x 0 = 0 := by
    have h : x 0 * ((v 0 - v 1) * (v 0 - v 2) * (v 0 - v 3)) = 0 := by
      linear_combination o3 - (v 1 + v 2 + v 3) * o2 + (v 1 * v 2 + v 1 * v 3 + v 2 * v 3) * o1 -
        v 1 * v 2 * v 3 * o0
    have hne : (v 0 - v 1) * (v 0 - v 2) * (v 0 - v 3) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.2 d01) (sub_ne_zero.2 d02)) (sub_ne_zero.2 d03)
    exact (mul_eq_zero.1 h).resolve_right hne
  have x1 : x 1 = 0 := by
    have h : x 1 * ((v 1 - v 0) * (v 1 - v 2) * (v 1 - v 3)) = 0 := by
      linear_combination o3 - (v 0 + v 2 + v 3) * o2 + (v 0 * v 2 + v 0 * v 3 + v 2 * v 3) * o1 -
        v 0 * v 2 * v 3 * o0
    have hne : (v 1 - v 0) * (v 1 - v 2) * (v 1 - v 3) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.2 (Ne.symm d01)) (sub_ne_zero.2 d12)) (sub_ne_zero.2 d13)
    exact (mul_eq_zero.1 h).resolve_right hne
  have x2 : x 2 = 0 := by
    have h : x 2 * ((v 2 - v 0) * (v 2 - v 1) * (v 2 - v 3)) = 0 := by
      linear_combination o3 - (v 0 + v 1 + v 3) * o2 + (v 0 * v 1 + v 0 * v 3 + v 1 * v 3) * o1 -
        v 0 * v 1 * v 3 * o0
    have hne : (v 2 - v 0) * (v 2 - v 1) * (v 2 - v 3) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.2 (Ne.symm d02)) (sub_ne_zero.2 (Ne.symm d12))) (sub_ne_zero.2 d23)
    exact (mul_eq_zero.1 h).resolve_right hne
  have x3 : x 3 = 0 := by
    have h : x 3 * ((v 3 - v 0) * (v 3 - v 1) * (v 3 - v 2)) = 0 := by
      linear_combination o3 - (v 0 + v 1 + v 2) * o2 + (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) * o1 -
        v 0 * v 1 * v 2 * o0
    have hne : (v 3 - v 0) * (v 3 - v 1) * (v 3 - v 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.2 (Ne.symm d03)) (sub_ne_zero.2 (Ne.symm d13))) (sub_ne_zero.2 (Ne.symm d23))
    exact (mul_eq_zero.1 h).resolve_right hne
  funext i
  fin_cases i
  · exact x0
  · exact x1
  · exact x2
  · exact x3

theorem core_case (v y z x : Fin 4 → ℂ) (sv : ∑ i, v i = 0) (sy : ∑ i, y i = 0)
    (sz : ∑ i, z i = 0) (sx : ∑ i, x i = 0)
    (qv : dotProduct v v = 0) (qy : dotProduct y y = 0) (qz : dotProduct z z = 0)
    (ovy : dotProduct v y = 0) (ovz : dotProduct v z = 0) (ovx : dotProduct v x = 0)
    (t1 : ∑ k, v k * y k * z k = 0) (t2 : ∑ k, v k * y k * x k = 0)
    (t3 : ∑ k, v k * y k * z k * x k = 0)
    (hv : v ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hx : x ≠ 0) : False := by
  obtain ⟨β, hβ⟩ := prop2 v y sv sy qv qy ovy hv
  obtain ⟨γ, hγ⟩ := prop2 v z sv sz qv qz ovz hv
  have hβ0 : β ≠ 0 := by intro h; apply hy; rw [hβ, h, zero_smul]
  have hγ0 : γ ≠ 0 := by intro h; apply hz; rw [hγ, h, zero_smul]
  subst hβ hγ
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four] at t1 t2 t3
  apply hx
  apply vand v x sv
  · simpa [dotProduct, sq] using qv
  · have : β * γ * ∑ i, v i ^ 3 = 0 := by
      simp only [Fin.sum_univ_four]; linear_combination t1
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero hβ0 hγ0)
  · exact hv
  · exact sx
  · simpa [dotProduct, mul_comm] using ovx
  · have : β * ∑ i, x i * v i ^ 2 = 0 := by
      simp only [Fin.sum_univ_four]; linear_combination t2
    exact (mul_eq_zero.1 this).resolve_left hβ0
  · have : β * γ * ∑ i, x i * v i ^ 3 = 0 := by
      simp only [Fin.sum_univ_four]; linear_combination t3
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero hβ0 hγ0)

theorem one_row_alg (w : Fin 4 → Fin 4 → ℂ) (hs : ∀ r, ∑ k, w r k = 0)
    (ho : ∀ a b, a ≠ b → dotProduct (w a) (w b) = 0)
    (T012 : ∑ k, w 0 k * w 1 k * w 2 k = 0) (T013 : ∑ k, w 0 k * w 1 k * w 3 k = 0)
    (T023 : ∑ k, w 0 k * w 2 k * w 3 k = 0) (T123 : ∑ k, w 1 k * w 2 k * w 3 k = 0)
    (Q : ∑ k, w 0 k * w 1 k * w 2 k * w 3 k = 0) (hne : ∀ r, w r ≠ 0) : False := by
  have o : ∀ a b : Fin 4, a ≠ b → dotProduct (w a) (w b) = 0 := ho
  have re3 : ∀ (f : Fin 4 → ℂ) (g : Fin 4 → ℂ), (∀ k, f k = g k) → ∑ k, f k = 0 → ∑ k, g k = 0 :=
    fun f g h hf => by rw [← hf]; exact Finset.sum_congr rfl (fun k _ => (h k).symm)
  by_cases q0 : dotProduct (w 0) (w 0) = 0
  · by_cases q1 : dotProduct (w 1) (w 1) = 0
    · by_cases q2 : dotProduct (w 2) (w 2) = 0
      · exact core_case (w 0) (w 1) (w 2) (w 3) (hs 0) (hs 1) (hs 2) (hs 3) q0 q1 q2
          (o 0 1 (by decide)) (o 0 2 (by decide)) (o 0 3 (by decide)) T012 T013 Q
          (hne 0) (hne 1) (hne 2) (hne 3)
      · have q3 : dotProduct (w 3) (w 3) = 0 := by
          by_contra h3
          exact amo_gen (w 2) (w 3) (w 0) (w 1) (hs 2) (hs 3) (hs 0) (hs 1)
            (o 2 3 (by decide)) (o 2 0 (by decide)) (o 2 1 (by decide)) (o 3 0 (by decide))
            (o 3 1 (by decide)) (o 0 1 (by decide)) (hne 0) (hne 1) q2 h3
        exact core_case (w 0) (w 1) (w 3) (w 2) (hs 0) (hs 1) (hs 3) (hs 2) q0 q1 q3
          (o 0 1 (by decide)) (o 0 3 (by decide)) (o 0 2 (by decide)) T013 T012
          (re3 _ _ (fun k => by ring) Q) (hne 0) (hne 1) (hne 3) (hne 2)
    · have q2 : dotProduct (w 2) (w 2) = 0 := by
        by_contra h2
        exact amo_gen (w 1) (w 2) (w 0) (w 3) (hs 1) (hs 2) (hs 0) (hs 3)
          (o 1 2 (by decide)) (o 1 0 (by decide)) (o 1 3 (by decide)) (o 2 0 (by decide))
          (o 2 3 (by decide)) (o 0 3 (by decide)) (hne 0) (hne 3) q1 h2
      have q3 : dotProduct (w 3) (w 3) = 0 := by
        by_contra h3
        exact amo_gen (w 1) (w 3) (w 0) (w 2) (hs 1) (hs 3) (hs 0) (hs 2)
          (o 1 3 (by decide)) (o 1 0 (by decide)) (o 1 2 (by decide)) (o 3 0 (by decide))
          (o 3 2 (by decide)) (o 0 2 (by decide)) (hne 0) (hne 2) q1 h3
      exact core_case (w 0) (w 2) (w 3) (w 1) (hs 0) (hs 2) (hs 3) (hs 1) q0 q2 q3
        (o 0 2 (by decide)) (o 0 3 (by decide)) (o 0 1 (by decide)) T023
        (re3 _ _ (fun k => by ring) T012) (re3 _ _ (fun k => by ring) Q)
        (hne 0) (hne 2) (hne 3) (hne 1)
  · have q1 : dotProduct (w 1) (w 1) = 0 := by
      by_contra h1
      exact amo_gen (w 0) (w 1) (w 2) (w 3) (hs 0) (hs 1) (hs 2) (hs 3)
        (o 0 1 (by decide)) (o 0 2 (by decide)) (o 0 3 (by decide)) (o 1 2 (by decide))
        (o 1 3 (by decide)) (o 2 3 (by decide)) (hne 2) (hne 3) q0 h1
    have q2 : dotProduct (w 2) (w 2) = 0 := by
      by_contra h2
      exact amo_gen (w 0) (w 2) (w 1) (w 3) (hs 0) (hs 2) (hs 1) (hs 3)
        (o 0 2 (by decide)) (o 0 1 (by decide)) (o 0 3 (by decide)) (o 2 1 (by decide))
        (o 2 3 (by decide)) (o 1 3 (by decide)) (hne 1) (hne 3) q0 h2
    have q3 : dotProduct (w 3) (w 3) = 0 := by
      by_contra h3
      exact amo_gen (w 0) (w 3) (w 1) (w 2) (hs 0) (hs 3) (hs 1) (hs 2)
        (o 0 3 (by decide)) (o 0 1 (by decide)) (o 0 2 (by decide)) (o 3 1 (by decide))
        (o 3 2 (by decide)) (o 1 2 (by decide)) (hne 1) (hne 2) q0 h3
    exact core_case (w 1) (w 2) (w 3) (w 0) (hs 1) (hs 2) (hs 3) (hs 0) q1 q2 q3
      (o 1 2 (by decide)) (o 1 3 (by decide)) (o 1 0 (by decide)) T123
      (re3 _ _ (fun k => by ring) T012) (re3 _ _ (fun k => by ring) Q)
      (hne 1) (hne 2) (hne 3) (hne 0)



def oneRow (r : Fin 4) (u : Fin 4 → ℂ) : Fin 4 × Fin 4 → ℂ := fun q => if q.1 = r then u q.2 else 0

theorem sum_oneRow (r : Fin 4) (u : Fin 4 → ℂ) :
    ∑ a : Fin 4, ∑ k : Fin 4, oneRow r u (a, k) = ∑ k, u k := by
  fin_cases r <;> simp [oneRow, Fin.sum_univ_four]

theorem e2b_oneRow (a b : Fin 4) (hab : a ≠ b) (u v : Fin 4 → ℂ) :
    e2b (oneRow a u) (oneRow b v) = (∑ k, u k) * (∑ k, v k) - dotProduct u v := by
  fin_cases a <;> fin_cases b <;> simp at hab <;>
    simp [e2b, oneRow, Fin.sum_univ_four, dotProduct]

theorem ie3_012 (u v w : Fin 4 → ℂ) :
    p4 (J4 + (oneRow 0 u + oneRow 1 v + oneRow 2 w)) - p4 (J4 + (oneRow 0 u + oneRow 1 v)) - p4 (J4 + (oneRow 0 u + oneRow 2 w)) -
      p4 (J4 + (oneRow 1 v + oneRow 2 w)) + p4 (J4 + oneRow 0 u) + p4 (J4 + oneRow 1 v) + p4 (J4 + oneRow 2 w) - p4 J4 =
      (∑ k, u k) * (∑ k, v k) * (∑ k, w k) - dotProduct u v * (∑ k, w k) -
      dotProduct u w * (∑ k, v k) - dotProduct v w * (∑ k, u k) + 2 * ∑ k, u k * v k * w k := by
  simp [p4, J4, oneRow, Fin.sum_univ_four, dotProduct]
  ring

theorem ie3_013 (u v w : Fin 4 → ℂ) :
    p4 (J4 + (oneRow 0 u + oneRow 1 v + oneRow 3 w)) - p4 (J4 + (oneRow 0 u + oneRow 1 v)) - p4 (J4 + (oneRow 0 u + oneRow 3 w)) -
      p4 (J4 + (oneRow 1 v + oneRow 3 w)) + p4 (J4 + oneRow 0 u) + p4 (J4 + oneRow 1 v) + p4 (J4 + oneRow 3 w) - p4 J4 =
      (∑ k, u k) * (∑ k, v k) * (∑ k, w k) - dotProduct u v * (∑ k, w k) -
      dotProduct u w * (∑ k, v k) - dotProduct v w * (∑ k, u k) + 2 * ∑ k, u k * v k * w k := by
  simp [p4, J4, oneRow, Fin.sum_univ_four, dotProduct]
  ring

theorem ie3_023 (u v w : Fin 4 → ℂ) :
    p4 (J4 + (oneRow 0 u + oneRow 2 v + oneRow 3 w)) - p4 (J4 + (oneRow 0 u + oneRow 2 v)) - p4 (J4 + (oneRow 0 u + oneRow 3 w)) -
      p4 (J4 + (oneRow 2 v + oneRow 3 w)) + p4 (J4 + oneRow 0 u) + p4 (J4 + oneRow 2 v) + p4 (J4 + oneRow 3 w) - p4 J4 =
      (∑ k, u k) * (∑ k, v k) * (∑ k, w k) - dotProduct u v * (∑ k, w k) -
      dotProduct u w * (∑ k, v k) - dotProduct v w * (∑ k, u k) + 2 * ∑ k, u k * v k * w k := by
  simp [p4, J4, oneRow, Fin.sum_univ_four, dotProduct]
  ring

theorem ie3_123 (u v w : Fin 4 → ℂ) :
    p4 (J4 + (oneRow 1 u + oneRow 2 v + oneRow 3 w)) - p4 (J4 + (oneRow 1 u + oneRow 2 v)) - p4 (J4 + (oneRow 1 u + oneRow 3 w)) -
      p4 (J4 + (oneRow 2 v + oneRow 3 w)) + p4 (J4 + oneRow 1 u) + p4 (J4 + oneRow 2 v) + p4 (J4 + oneRow 3 w) - p4 J4 =
      (∑ k, u k) * (∑ k, v k) * (∑ k, w k) - dotProduct u v * (∑ k, w k) -
      dotProduct u w * (∑ k, v k) - dotProduct v w * (∑ k, u k) + 2 * ∑ k, u k * v k * w k := by
  simp [p4, J4, oneRow, Fin.sum_univ_four, dotProduct]
  ring

set_option maxHeartbeats 2000000 in
theorem ie4 (u v w x : Fin 4 → ℂ) :
    p4 J4 - p4 (J4 + oneRow 0 u) - p4 (J4 + oneRow 1 v)
      - p4 (J4 + oneRow 2 w) - p4 (J4 + oneRow 3 x) + p4 (J4 + (oneRow 0 u + oneRow 1 v))
      + p4 (J4 + (oneRow 0 u + oneRow 2 w)) + p4 (J4 + (oneRow 0 u + oneRow 3 x)) + p4 (J4 + (oneRow 1 v + oneRow 2 w))
      + p4 (J4 + (oneRow 1 v + oneRow 3 x)) + p4 (J4 + (oneRow 2 w + oneRow 3 x)) - p4 (J4 + (oneRow 0 u + oneRow 1 v + oneRow 2 w))
      - p4 (J4 + (oneRow 0 u + oneRow 1 v + oneRow 3 x)) - p4 (J4 + (oneRow 0 u + oneRow 2 w + oneRow 3 x)) - p4 (J4 + (oneRow 1 v + oneRow 2 w + oneRow 3 x))
      + p4 (J4 + (oneRow 0 u + oneRow 1 v + oneRow 2 w + oneRow 3 x)) =
      (∑ k, u k) * (∑ k, v k) * (∑ k, w k) * (∑ k, x k) - (dotProduct u v * (∑ k, w k) * (∑ k, x k) + dotProduct u w * (∑ k, v k) * (∑ k, x k) + dotProduct u x * (∑ k, v k) * (∑ k, w k) + dotProduct v w * (∑ k, u k) * (∑ k, x k) + dotProduct v x * (∑ k, u k) * (∑ k, w k) + dotProduct w x * (∑ k, u k) * (∑ k, v k)) + (dotProduct u v * dotProduct w x + dotProduct u w * dotProduct v x + dotProduct u x * dotProduct v w) + 2 * ((∑ k, u k * v k * w k) * (∑ k, x k) + (∑ k, u k * v k * x k) * (∑ k, w k) + (∑ k, u k * w k * x k) * (∑ k, v k) + (∑ k, v k * w k * x k) * (∑ k, u k)) - 6 * ∑ k, u k * v k * w k * x k := by
  simp [p4, J4, oneRow, Fin.sum_univ_four, dotProduct]
  ring


theorem fin4_three : ∀ r a b c i : Fin 4, a ≠ r → b ≠ r → c ≠ r → a ≠ b → a ≠ c → b ≠ c →
    i ≠ r → i = a ∨ i = b ∨ i = c := by decide

theorem level_sum (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {J4}, ∀ y ∈ L, p4 (X + y) = p4 X) :
    ∀ y ∈ L, ∑ a : Fin 4, ∑ k : Fin 4, y (a, k) = 0 := by
  have hJC : J4 ∈ L ⊔ Submodule.span ℂ {J4} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self J4)
  intro y hy
  have e := sum_id y
  have h1 := hinv J4 hJC y hy
  have h2 := hinv J4 hJC (-y) (L.neg_mem hy)
  have h3 := hinv J4 hJC ((2 : ℂ) • y) (L.smul_mem _ hy)
  have h4 := hinv J4 hJC (-((2 : ℂ) • y)) (L.neg_mem (L.smul_mem _ hy))
  rw [← sub_eq_add_neg] at h2 h4
  rw [h1, h2, h3, h4] at e
  linear_combination e / 72

theorem level_e2 (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {J4}, ∀ y ∈ L, p4 (X + y) = p4 X) :
    ∀ u ∈ L, ∀ v ∈ L, e2b u v = 0 := by
  have hJC : J4 ∈ L ⊔ Submodule.span ℂ {J4} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self J4)
  have hd : ∀ y ∈ L, e2b y y = 0 := by
    intro y hy
    have e := e2_id y
    have h1 := hinv J4 hJC y hy
    have h2 := hinv J4 hJC (-y) (L.neg_mem hy)
    have h3 := hinv J4 hJC ((2 : ℂ) • y) (L.smul_mem _ hy)
    have h4 := hinv J4 hJC (-((2 : ℂ) • y)) (L.neg_mem (L.smul_mem _ hy))
    rw [← sub_eq_add_neg] at h2 h4
    rw [h1, h2, h3, h4] at e
    have hJ : p4 J4 = 24 := by simp [p4, J4]; norm_num
    rw [hJ] at e
    linear_combination e / 24
  intro u hu v hv
  have e := e2b_add u v
  rw [hd u hu, hd v hv, hd (u + v) (L.add_mem hu hv)] at e
  linear_combination -e / 2

theorem step1 (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {J4}, ∀ y ∈ L, p4 (X + y) = p4 X)
    (hdim : 7 ≤ Module.finrank ℂ L) :
    ∃ r, (L ⊔ Submodule.span ℂ {J4}).map (rowr4 r) = ⊤ := by
  by_contra hno
  push Not at hno
  set C := L ⊔ Submodule.span ℂ {J4} with hC
  have hJC : J4 ∈ C := Submodule.mem_sup_right (Submodule.mem_span_singleton_self J4)
  have hz : ∀ y ∈ L, p4 y = 0 := by
    intro y hy
    have := hinv 0 C.zero_mem y hy
    rw [zero_add] at this
    rw [this]; simp [p4]
  have hJ : p4 J4 ≠ 0 := by simp [p4, J4]; norm_num
  have hJL : J4 ∉ L := fun h => hJ (hz J4 h)
  have hCL : ∀ X ∈ C, p4 X = 0 → X ∈ L := by
    intro X hX h0
    obtain ⟨y, hy, m, hm, rfl⟩ := Submodule.mem_sup.1 hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    have e := hinv (c • J4) (C.smul_mem c hJC) y hy
    rw [add_comm] at h0
    rw [h0, p4_smul] at e
    have hc : c = 0 := by
      rcases mul_eq_zero.1 e.symm with h | h
      · exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 h
      · exact absurd h hJ
    rw [hc, zero_smul, add_zero]; exact hy
  have hCdim : Module.finrank ℂ C = Module.finrank ℂ L + 1 := finrank_sup_span L J4 hJL
  have hK : ∀ r, Module.finrank ℂ L ≤ Module.finrank ℂ ↥(C ⊓ LinearMap.ker (rowr4 r)) + 2 := by
    intro r
    have h3 := Submodule.finrank_lt (hno r)
    rw [Module.finrank_fin_fun] at h3
    have := rank_nullity C (rowr4 r)
    omega
  have hKL : ∀ r, C ⊓ LinearMap.ker (rowr4 r) ≤ L := by
    intro r X hX
    obtain ⟨hXC, hXr⟩ := Submodule.mem_inf.1 hX
    apply hCL X hXC
    apply p4_row_zero r
    intro k
    exact congrFun (LinearMap.mem_ker.1 hXr) k
  have hpair : ∀ A B : Submodule ℂ (Fin 4 × Fin 4 → ℂ), A ≤ L → B ≤ L →
      Module.finrank ℂ A + Module.finrank ℂ B ≤ Module.finrank ℂ ↥(A ⊓ B) + Module.finrank ℂ L := by
    intro A B hA hB
    have := Submodule.finrank_sup_add_finrank_inf_eq A B
    have := Submodule.finrank_mono (sup_le hA hB)
    omega
  have hzero : ∀ r X, X ∈ C ⊓ LinearMap.ker (rowr4 r) → ∀ k, X (r, k) = 0 := by
    intro r X hX k
    exact congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hX).2) k
  have hone : ∀ r : Fin 4, ∃ o ∈ L, o ≠ 0 ∧ ∀ i, i ≠ r → ∀ k, o (i, k) = 0 := by
    intro r
    have key : ∀ a b c : Fin 4, a ≠ r → b ≠ r → c ≠ r → a ≠ b → a ≠ c → b ≠ c →
        ∃ o ∈ L, o ≠ 0 ∧ ∀ i, i ≠ r → ∀ k, o (i, k) = 0 := by
      intro a b c har hbr hcr hab hac hbc
      have p1 := hpair _ _ (hKL a) (hKL b)
      have p2 := hpair ((C ⊓ LinearMap.ker (rowr4 a)) ⊓ (C ⊓ LinearMap.ker (rowr4 b)))
        (C ⊓ LinearMap.ker (rowr4 c)) (inf_le_left.trans (hKL a)) (hKL c)
      have ka := hK a
      have kb := hK b
      have kc := hK c
      have hpos : 1 ≤ Module.finrank ℂ ↥((C ⊓ LinearMap.ker (rowr4 a)) ⊓
          (C ⊓ LinearMap.ker (rowr4 b)) ⊓ (C ⊓ LinearMap.ker (rowr4 c))) := by omega
      have hne : (C ⊓ LinearMap.ker (rowr4 a)) ⊓ (C ⊓ LinearMap.ker (rowr4 b)) ⊓
          (C ⊓ LinearMap.ker (rowr4 c)) ≠ ⊥ := by
        intro h; rw [h, finrank_bot] at hpos; omega
      obtain ⟨o, ho, ho0⟩ := Submodule.ne_bot_iff _ |>.1 hne
      obtain ⟨hoab, hoc⟩ := Submodule.mem_inf.1 ho
      obtain ⟨hoa, hob⟩ := Submodule.mem_inf.1 hoab
      refine ⟨o, hKL a hoa, ho0, ?_⟩
      intro i hi k
      have : i = a ∨ i = b ∨ i = c := fin4_three r a b c i har hbr hcr hab hac hbc hi
      rcases this with rfl | rfl | rfl
      · exact hzero _ _ hoa k
      · exact hzero _ _ hob k
      · exact hzero _ _ hoc k
    fin_cases r
    · exact key 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact key 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact key 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact key 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  choose o hoL' ho0 hoz using hone
  set w : Fin 4 → Fin 4 → ℂ := fun r k => o r (r, k) with hw
  have hor : ∀ r, o r = oneRow r (w r) := by
    intro r
    funext q
    obtain ⟨i, k⟩ := q
    by_cases hi : i = r
    · subst hi; simp [oneRow, hw]
    · simp [oneRow, hi, hoz r i hi k]
  have hoL : ∀ r, oneRow r (w r) ∈ L := fun r => by rw [← hor r]; exact hoL' r
  have hs : ∀ r, ∑ k, w r k = 0 := by
    intro r
    have := level_sum L hinv _ (hoL r)
    rwa [sum_oneRow] at this
  have hdot : ∀ a b, a ≠ b → dotProduct (w a) (w b) = 0 := by
    intro a b hab
    have := level_e2 L hinv _ (hoL a) _ (hoL b)
    rw [e2b_oneRow a b hab, hs a, hs b] at this
    linear_combination -this
  have hne : ∀ r, w r ≠ 0 := by
    intro r h
    apply ho0 r
    rw [hor r, h]
    funext q; simp [oneRow]
  have hJ' : ∀ y ∈ L, p4 (J4 + y) = p4 J4 := fun y hy => hinv J4 hJC y hy

  have T012 : ∑ k, w 0 k * w 1 k * w 2 k = 0 := by
    have e := ie3_012 (w 0) (w 1) (w 2)
    rw [hJ' _ (L.add_mem (L.add_mem (hoL 0) (hoL 1)) (hoL 2)), hJ' _ (L.add_mem (hoL 0) (hoL 1)), hJ' _ (L.add_mem (hoL 0) (hoL 2)), hJ' _ (L.add_mem (hoL 1) (hoL 2)), hJ' _ (hoL 0), hJ' _ (hoL 1), hJ' _ (hoL 2)] at e
    rw [hs 0, hs 1, hs 2, hdot 0 1 (by decide), hdot 0 2 (by decide), hdot 1 2 (by decide)] at e
    linear_combination -e / 2
  have T013 : ∑ k, w 0 k * w 1 k * w 3 k = 0 := by
    have e := ie3_013 (w 0) (w 1) (w 3)
    rw [hJ' _ (L.add_mem (L.add_mem (hoL 0) (hoL 1)) (hoL 3)), hJ' _ (L.add_mem (hoL 0) (hoL 1)), hJ' _ (L.add_mem (hoL 0) (hoL 3)), hJ' _ (L.add_mem (hoL 1) (hoL 3)), hJ' _ (hoL 0), hJ' _ (hoL 1), hJ' _ (hoL 3)] at e
    rw [hs 0, hs 1, hs 3, hdot 0 1 (by decide), hdot 0 3 (by decide), hdot 1 3 (by decide)] at e
    linear_combination -e / 2
  have T023 : ∑ k, w 0 k * w 2 k * w 3 k = 0 := by
    have e := ie3_023 (w 0) (w 2) (w 3)
    rw [hJ' _ (L.add_mem (L.add_mem (hoL 0) (hoL 2)) (hoL 3)), hJ' _ (L.add_mem (hoL 0) (hoL 2)), hJ' _ (L.add_mem (hoL 0) (hoL 3)), hJ' _ (L.add_mem (hoL 2) (hoL 3)), hJ' _ (hoL 0), hJ' _ (hoL 2), hJ' _ (hoL 3)] at e
    rw [hs 0, hs 2, hs 3, hdot 0 2 (by decide), hdot 0 3 (by decide), hdot 2 3 (by decide)] at e
    linear_combination -e / 2
  have T123 : ∑ k, w 1 k * w 2 k * w 3 k = 0 := by
    have e := ie3_123 (w 1) (w 2) (w 3)
    rw [hJ' _ (L.add_mem (L.add_mem (hoL 1) (hoL 2)) (hoL 3)), hJ' _ (L.add_mem (hoL 1) (hoL 2)), hJ' _ (L.add_mem (hoL 1) (hoL 3)), hJ' _ (L.add_mem (hoL 2) (hoL 3)), hJ' _ (hoL 1), hJ' _ (hoL 2), hJ' _ (hoL 3)] at e
    rw [hs 1, hs 2, hs 3, hdot 1 2 (by decide), hdot 1 3 (by decide), hdot 2 3 (by decide)] at e
    linear_combination -e / 2
  have Q : ∑ k, w 0 k * w 1 k * w 2 k * w 3 k = 0 := by
    have e := ie4 (w 0) (w 1) (w 2) (w 3)
    rw [hJ' _ (hoL 0), hJ' _ (hoL 1), hJ' _ (hoL 2), hJ' _ (hoL 3), hJ' _ (L.add_mem (hoL 0) (hoL 1)), hJ' _ (L.add_mem (hoL 0) (hoL 2)), hJ' _ (L.add_mem (hoL 0) (hoL 3)), hJ' _ (L.add_mem (hoL 1) (hoL 2)), hJ' _ (L.add_mem (hoL 1) (hoL 3)), hJ' _ (L.add_mem (hoL 2) (hoL 3)), hJ' _ (L.add_mem (L.add_mem (hoL 0) (hoL 1)) (hoL 2)), hJ' _ (L.add_mem (L.add_mem (hoL 0) (hoL 1)) (hoL 3)), hJ' _ (L.add_mem (L.add_mem (hoL 0) (hoL 2)) (hoL 3)), hJ' _ (L.add_mem (L.add_mem (hoL 1) (hoL 2)) (hoL 3)), hJ' _ (L.add_mem (L.add_mem (L.add_mem (hoL 0) (hoL 1)) (hoL 2)) (hoL 3))] at e
    rw [hs 0, hs 1, hs 2, hs 3, hdot 0 1 (by decide), hdot 0 2 (by decide), hdot 0 3 (by decide), hdot 1 2 (by decide), hdot 1 3 (by decide), hdot 2 3 (by decide)] at e
    linear_combination e / 6
  exact one_row_alg w hs hdot T012 T013 T023 T123 Q hne

theorem final (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hinv : ∀ X ∈ L ⊔ Submodule.span ℂ {J4}, ∀ y ∈ L, p4 (X + y) = p4 X)
    (hdim : 7 ≤ Module.finrank ℂ L) : False := by
  obtain ⟨r, hr⟩ := step1 L hinv hdim
  set C := L ⊔ Submodule.span ℂ {J4} with hC
  have hLC : L ≤ C := le_sup_left
  have hJC : J4 ∈ C := Submodule.mem_sup_right (Submodule.mem_span_singleton_self J4)
  have hz : ∀ y ∈ L, p4 y = 0 := by
    intro y hy
    have := hinv 0 C.zero_mem y hy
    rw [zero_add] at this
    rw [this]; simp [p4]
  have hJ : p4 J4 ≠ 0 := by simp [p4, J4]; norm_num
  have hJL : J4 ∉ L := fun h => hJ (hz J4 h)
  have hCL : ∀ X ∈ C, p4 X = 0 → X ∈ L := by
    intro X hX h0
    obtain ⟨y, hy, m, hm, rfl⟩ := Submodule.mem_sup.1 hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    have e := hinv (c • J4) (C.smul_mem c hJC) y hy
    rw [add_comm] at h0
    rw [h0, p4_smul] at e
    have hc : c = 0 := by
      rcases mul_eq_zero.1 e.symm with h | h
      · exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 h
      · exact absurd h hJ
    rw [hc, zero_smul, add_zero]; exact hy
  have hsurj : ∀ v : Fin 4 → ℂ, ∃ X ∈ C, rowr4 r X = v := by
    intro v
    have : v ∈ C.map (rowr4 r) := by rw [hr]; trivial
    obtain ⟨X, hX, hXv⟩ := Submodule.mem_map.1 this
    exact ⟨X, hX, hXv⟩
  have step2 : ∃ j, ∃ X ∈ C, rowr4 r X = Pi.single j 1 ∧ X ∉ L := by
    by_contra hno
    push Not at hno
    choose Xf hXfC hXfr using fun j => hsurj (Pi.single j 1)
    have hXfL : ∀ j, Xf j ∈ L := fun j => hno j (Xf j) (hXfC j) (hXfr j)
    set Y := J4 - ∑ j, J4 (r, j) • Xf j with hY
    have hYC : Y ∈ C := C.sub_mem hJC (C.sum_mem fun j _ => C.smul_mem _ (hXfC j))
    have hYr : rowr4 r Y = 0 := by
      rw [hY, map_sub, map_sum]
      simp only [map_smul, hXfr]
      funext k
      simp [rowr4, Finset.sum_apply, Pi.single_apply]
    have hYL : Y ∈ L := hCL Y hYC (p4_row_zero r Y (fun k => congrFun hYr k))
    have hsumL : ∑ j, J4 (r, j) • Xf j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hXfL j)
    apply hJL
    have := L.add_mem hYL hsumL
    rwa [hY, sub_add_cancel] at this
  obtain ⟨j, Xs, hXsC, hXsr, hXsL⟩ := step2
  have hXsne : p4 Xs ≠ 0 := fun h => hXsL (hCL Xs hXsC h)
  set e := Equiv.prodCongr (Equiv.swap (0 : Fin 4) r) (Equiv.swap (0 : Fin 4) j) with he
  set T : (Fin 4 × Fin 4 → ℂ) ≃ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e with hT
  have hTapp : ∀ X q, T X q = X (e q) := fun X q => rfl
  have hTp4 : ∀ X, p4 (T X) = p4 X := fun X => p4_perm r j X
  have hTJ : T J4 = J4 := by funext q; rfl
  have hmapC : C.map T.toLinearMap = L.map T.toLinearMap ⊔ Submodule.span ℂ {J4} := by
    rw [hC, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    change _ ⊔ Submodule.span ℂ {T J4} = _
    rw [hTJ]
  have hrowv : ∀ (X : Fin 4 × Fin 4 → ℂ) (v : Fin 4 → ℂ), rowr4 r X = v → ∀ k, X (r, k) = v k :=
    fun X v h k => congrFun h k
  have hTr : ∀ X k, T X (0, k) = X (r, Equiv.swap (0 : Fin 4) j k) := by
    intro X k
    rw [hTapp]
    simp [he, Equiv.swap_apply_left]
  have hmemT : ∀ X ∈ C, T X ∈ L.map T.toLinearMap ⊔ Submodule.span ℂ {J4} := by
    intro X hX
    rw [← hmapC]
    exact Submodule.mem_map_of_mem hX
  have hsw : ∀ k : Fin 4, k ≠ 0 → Equiv.swap (0 : Fin 4) j k ≠ j := by
    intro k hk h
    apply hk
    apply (Equiv.swap (0 : Fin 4) j).injective
    rw [h, Equiv.swap_apply_left]
  choose V hVC hVr using fun b : Fin 3 => hsurj (Pi.single (Equiv.swap (0 : Fin 4) j b.succ) 1)
  refine main_core (L.map T.toLinearMap) ?_ ?_ (T Xs) (hmemT Xs hXsC) ?_ ?_ ?_ ?_ ?_
    (fun b => T (V b)) (fun b => hmemT (V b) (hVC b)) ?_
  · intro X hX y hy
    rw [← hmapC] at hX
    obtain ⟨X1, hX1, rfl⟩ := Submodule.mem_map.1 hX
    obtain ⟨y1, hy1, rfl⟩ := Submodule.mem_map.1 hy
    have h1 : T.toLinearMap X1 + T.toLinearMap y1 = T (X1 + y1) := by simp
    rw [h1]
    change p4 (T (X1 + y1)) = p4 (T X1)
    rw [hTp4, hTp4]
    exact hinv X1 hX1 y1 hy1
  · rw [LinearEquiv.finrank_map_eq]; exact hdim
  · rw [hTr, hrowv Xs _ hXsr, Equiv.swap_apply_left]; simp
  · rw [hTr, hrowv Xs _ hXsr, Pi.single_apply, if_neg (hsw 1 (by decide))]
  · rw [hTr, hrowv Xs _ hXsr, Pi.single_apply, if_neg (hsw 2 (by decide))]
  · rw [hTr, hrowv Xs _ hXsr, Pi.single_apply, if_neg (hsw 3 (by decide))]
  · rw [hTp4]; exact hXsne
  · intro b k
    rw [hTr, hrowv (V b) _ (hVr b), Pi.single_apply]
    by_cases hkb : k = b
    · subst hkb; simp
    · rw [if_neg, if_neg hkb]
      intro h
      have := (Equiv.swap (0 : Fin 4) j).injective h
      exact hkb (Fin.succ_injective _ this)


def S1 (t : Fin 4 × Fin 4 → ℂ) : ℂ := ∑ i : Fin 4, ∑ j, t (i, j)
def S2 (t : Fin 4 × Fin 4 → ℂ) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0
def S3 (t : Fin 4 × Fin 4 → ℂ) : ℂ :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0
def S4 (t : Fin 4 × Fin 4 → ℂ) : ℂ :=
  ∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)


theorem expand (u : Fin 4 × Fin 4 → ℂ) (c : ℂ) :
    p4 (u + c • J4) = 24 * c ^ 4 + 6 * c ^ 3 * S1 u + 2 * c ^ 2 * S2 u + c * S3 u + S4 u := by
  simp only [S1, S2, S3, S4, Fin.sum_univ_four]
  simp [p4, J4]
  ring


end LGct214M

theorem PEqualNP.Outside.L_gct_214 : ∀ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), (∀ t ∈ L, (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → Module.finrank ℂ L ≤ 6 := by
  intro L hL
  by_contra hcon
  push Not at hcon
  apply LGct214M.final L _ (by omega)
  intro X hX y hy
  obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.1 hX
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
  obtain ⟨a1, a2, a3, a4⟩ := hL t ht
  obtain ⟨b1, b2, b3, b4⟩ := hL (t + y) (L.add_mem ht hy)
  rw [show t + c • LGct214M.J4 + y = (t + y) + c • LGct214M.J4 by abel, LGct214M.expand,
    LGct214M.expand]
  rw [show LGct214M.S1 (t + y) = 0 from b1, show LGct214M.S2 (t + y) = 0 from b2,
    show LGct214M.S3 (t + y) = 0 from b3, show LGct214M.S4 (t + y) = 0 from b4,
    show LGct214M.S1 t = 0 from a1, show LGct214M.S2 t = 0 from a2,
    show LGct214M.S3 t = 0 from a3, show LGct214M.S4 t = 0 from a4]
