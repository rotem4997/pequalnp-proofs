import Mathlib

/-!
# Helpers: rank retention for families of linear maps with the three-term property

Let `Φ` be an additive family of linear maps `U → W` indexed by a group `G` in which every
element is its own negative (for instance `G = (ι → ZMod 2)` and `Φ c = ∑ i, c i • M i`).
Write `K c = ker (Φ c)`. Additivity alone gives `K a ⊓ K b ≤ K (a + b)`. The family has the
*three-term property* when

  `K (a + b) ⊓ (K a ⊔ K b) ≤ K a`   for all `a b`,

that is, a vector killed by `Φ (a + b)` which splits as a vector killed by `Φ a` plus a
vector killed by `Φ b` is killed by `Φ a` (and then, by symmetry, by `Φ b`).

Main results.

* `threeTerm_finrank`: the dimension count behind everything. Inside any subspace `I`, three
  subspaces `A`, `B`, `L` with `L ⊓ (A ⊔ B) ≤ A ⊓ B` satisfy
  `dim (I ⊓ A) + dim (I ⊓ B) + dim (I ⊓ L) ≤ dim I + 2 * dim (I ⊓ A ⊓ B)`.
* `kerSum_le`: summed over all `2 ^ l` subset sums of a list of `l` group elements, shifted
  by a base point, the kernels are on average at most half of what is not already killed by
  the list.
* `exists_two_mul_finrank_ker_le`, `rank_retention`: some combination `Φ c` keeps at least
  half of the rank of the stacked map. No field extension and no determinant is used.
* `rank_retention_pi`: the same for `M : ι → U →ₗ[ZMod 2] W` and `c : ι → ZMod 2`.
* `rank_retention_mul`: the multiplication maps `f ↦ (f * q c * h α mod C)_α` on a finite
  dimensional space `U` of polynomials, for a subspace `C` of polynomials, under two closure
  hypotheses on `C`: one more multiplication by a `q c'` keeps membership, and `q c` is
  idempotent modulo `C` at this level.

The three-term property is what fails for general linear maps: for the coordinate maps
`M i u = u i` on `F ^ s` with `s ≥ 3` every combination has rank at most one while the
stacked map has rank `s`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open Module

section Abstract

variable {F U : Type*} [Field F] [AddCommGroup U] [Module F U]

/-- The three-term dimension count. -/
theorem threeTerm_finrank [FiniteDimensional F U] (I A B L : Submodule F U)
    (h : L ⊓ (A ⊔ B) ≤ A ⊓ B) :
    finrank F ↥(I ⊓ A) + finrank F ↥(I ⊓ B) + finrank F ↥(I ⊓ L)
      ≤ finrank F ↥I + 2 * finrank F ↥(I ⊓ A ⊓ B) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (I ⊓ A) (I ⊓ B)
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq ((I ⊓ A) ⊔ (I ⊓ B)) (I ⊓ L)
  have hPQ : (I ⊓ A) ⊓ (I ⊓ B) = I ⊓ A ⊓ B := by
    rw [← inf_inf_distrib_left, inf_assoc]
  have hup : ((I ⊓ A) ⊔ (I ⊓ B)) ⊔ (I ⊓ L) ≤ I :=
    sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hdown : ((I ⊓ A) ⊔ (I ⊓ B)) ⊓ (I ⊓ L) ≤ I ⊓ A ⊓ B := by
    rw [inf_assoc]
    refine le_inf ?_ ?_
    · exact inf_le_right.trans inf_le_left
    · refine le_trans ?_ h
      exact le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (sup_le_sup inf_le_right inf_le_right))
  have h1 := Submodule.finrank_mono hup
  have h2 := Submodule.finrank_mono hdown
  rw [hPQ] at e1
  omega

variable {G : Type*}

/-- The dimension of a subspace, as a plain function of the subspace. -/
noncomputable def subDim (S : Submodule F U) : ℕ := finrank F ↥S

theorem subDim_mono [FiniteDimensional F U] {S T : Submodule F U} (h : S ≤ T) :
    subDim S ≤ subDim T := Submodule.finrank_mono h

theorem subDim_top : subDim (⊤ : Submodule F U) = finrank F U := finrank_top F U

/-- The sum of the dimensions of `K (c + t)` over all subset sums `t` of the list. -/
noncomputable def kerSum [Add G] (K : G → Submodule F U) : G → List G → ℕ
  | c, [] => subDim (K c)
  | c, b :: bs => kerSum K c bs + kerSum K (c + b) bs

/-- The intersection of the `K b` over the list. -/
def listInf (K : G → Submodule F U) : List G → Submodule F U
  | [] => ⊤
  | b :: bs => K b ⊓ listInf K bs

theorem listInf_le (K : G → Submodule F U) {b : G} :
    ∀ {bs : List G}, b ∈ bs → listInf K bs ≤ K b
  | [], hb => by simp at hb
  | a :: bs, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact inf_le_left
    · exact inf_le_right.trans (listInf_le K hb)

private theorem arith_step (N S1 S2 dI dU d1 d2 d3 dJ dJ' : ℕ)
    (ih1 : 2 * S1 + N * dI ≤ N * dU + 2 * (N * d1))
    (ih2 : 2 * S2 + N * dI ≤ N * dU + 2 * (N * d2))
    (tt : d1 + d2 + d3 ≤ dI + 2 * dJ) (hJ : dJ ≤ dJ') :
    2 * (S1 + S2) + (2 * N) * d3 ≤ (2 * N) * dU + 2 * ((2 * N) * dJ') := by
  nlinarith [Nat.mul_le_mul_left N tt, Nat.mul_le_mul_left N hJ]

/-- The averaging bound. With `I` the intersection over the list and `l` its length:
`2 * ∑_t dim K (c + t) + 2 ^ l * dim I ≤ 2 ^ l * dim U + 2 * (2 ^ l * dim (I ⊓ K c))`. -/
theorem kerSum_le [Add G] [FiniteDimensional F U] (K : G → Submodule F U)
    (hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b)
    (hthree : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b)) :
    ∀ (bs : List G) (c : G),
      2 * kerSum K c bs + 2 ^ bs.length * subDim (listInf K bs)
        ≤ 2 ^ bs.length * finrank F U
          + 2 * (2 ^ bs.length * subDim (listInf K bs ⊓ K c))
  | [], c => by
    have h1 : listInf K ([] : List G) = ⊤ := rfl
    have h2 : kerSum K c [] = subDim (K c) := rfl
    rw [h1, h2, top_inf_eq, subDim_top]
    simp only [List.length_nil, pow_zero, one_mul]
    omega
  | b :: bs, c => by
    have ih1 := kerSum_le K hadd hthree bs c
    have ih2 := kerSum_le K hadd hthree bs (c + b)
    have tt : subDim (listInf K bs ⊓ K c) + subDim (listInf K bs ⊓ K (c + b))
        + subDim (K b ⊓ listInf K bs)
        ≤ subDim (listInf K bs) + 2 * subDim (listInf K bs ⊓ K c ⊓ K (c + b)) := by
      have := threeTerm_finrank (listInf K bs) (K c) (K (c + b)) (K b) (hthree c b)
      rw [inf_comm (listInf K bs) (K b)] at this
      exact this
    have hJ : listInf K bs ⊓ K c ⊓ K (c + b) ≤ K b ⊓ listInf K bs ⊓ K c := by
      refine le_inf (le_inf ?_ (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      exact le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (hadd c b)
    have hJ' := subDim_mono hJ
    have h1 : listInf K (b :: bs) = K b ⊓ listInf K bs := rfl
    have h2 : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [h1, h2, hp]
    have hU := arith_step (2 ^ bs.length) _ _ _ (finrank F U) _ _ _ _ _ ih1 ih2 tt hJ'
    exact hU

/-- Pigeonhole: some term of the sum is at most the average. -/
theorem exists_le_kerSum [Add G] (K : G → Submodule F U) :
    ∀ (bs : List G) (c : G), ∃ c', 2 ^ bs.length * subDim (K c') ≤ kerSum K c bs
  | [], c => ⟨c, by simp [kerSum]⟩
  | b :: bs, c => by
    obtain ⟨c1, h1⟩ := exists_le_kerSum K bs c
    obtain ⟨c2, h2⟩ := exists_le_kerSum K bs (c + b)
    have e : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [e, hp]
    rcases le_total (subDim (K c1)) (subDim (K c2)) with h | h
    · refine ⟨c1, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith
    · refine ⟨c2, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith

end Abstract

section Maps

variable {F U W G : Type*} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup W]
  [Module F W] [AddCommGroup G]

/-- Kernel form of rank retention. `Φ` is additive on a group in which `a + a = 0`, and has
the three-term property. Then for every list `bs` some `c` has
`2 * dim ker (Φ c) ≤ dim U + dim (⋂ b ∈ bs, ker (Φ b))`. -/
theorem exists_two_mul_finrank_ker_le [FiniteDimensional F U] (Φ : G →+ (U →ₗ[F] W))
    (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (bs : List G) :
    ∃ c : G, 2 * finrank F ↥(LinearMap.ker (Φ c))
      ≤ finrank F U + finrank F ↥(listInf (fun c => LinearMap.ker (Φ c)) bs) := by
  set K : G → Submodule F U := fun c => LinearMap.ker (Φ c) with hKdef
  have hcancel : ∀ c b : G, c + (c + b) = b := fun c b => by
    rw [← add_assoc, h2, zero_add]
  have hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b := by
    intro c b f hf
    have h1 : Φ c f = 0 := hf.1
    have h3 : Φ (c + b) f = 0 := hf.2
    have : Φ b f = 0 := by
      rw [map_add, LinearMap.add_apply, h1, zero_add] at h3
      exact h3
    exact this
  have hthree' : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b) := by
    intro c b f hf
    have hb : Φ b f = 0 := hf.1
    refine ⟨?_, ?_⟩
    · exact hthree c (c + b) f (by rw [hcancel]; exact hb) hf.2
    · refine hthree (c + b) c f ?_ ?_
      · rw [add_comm, hcancel]; exact hb
      · have := hf.2
        rwa [sup_comm] at this
  have key := kerSum_le K hadd hthree' bs 0
  obtain ⟨c, hc⟩ := exists_le_kerSum K bs (0 : G)
  refine ⟨c, ?_⟩
  have hle : subDim (listInf K bs ⊓ K 0) ≤ subDim (listInf K bs) := subDim_mono inf_le_left
  have hpos : 0 < 2 ^ bs.length := by positivity
  have t := Nat.mul_le_mul_left (2 ^ bs.length) hle
  have : 2 ^ bs.length * (2 * subDim (K c))
      ≤ 2 ^ bs.length * (finrank F U + subDim (listInf K bs)) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this hpos

/-- Rank retention, abstract form: if every `Φ b` with `b` in the list `bs` factors through
the map `S` on kernels (`ker S` contains the common kernel of the list), then some `Φ c`
has at least half the rank of `S`. -/
theorem rank_retention [FiniteDimensional F U] {W' : Type*} [AddCommGroup W'] [Module F W']
    (Φ : G →+ (U →ₗ[F] W)) (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (S : U →ₗ[F] W') (bs : List G)
    (hS : ∀ f : U, (∀ b ∈ bs, Φ b f = 0) → S f = 0) :
    ∃ c : G, finrank F ↥(LinearMap.range S) ≤ 2 * finrank F ↥(LinearMap.range (Φ c)) := by
  obtain ⟨c, hc⟩ := exists_two_mul_finrank_ker_le Φ h2 hthree bs
  refine ⟨c, ?_⟩
  have hI : listInf (fun c => LinearMap.ker (Φ c)) bs ≤ LinearMap.ker S := by
    intro f hf
    exact hS f fun b hb => listInf_le (fun c => LinearMap.ker (Φ c)) hb hf
  have hI' := Submodule.finrank_mono hI
  have r1 := LinearMap.finrank_range_add_finrank_ker S
  have r2 := LinearMap.finrank_range_add_finrank_ker (Φ c)
  omega

/-- Rank retention for finitely many maps over the two-element field: under the three-term
property some combination `∑ i, c i • M i` has at least half the rank of the stacked map. -/
theorem rank_retention_pi {ι U W : Type*} [Fintype ι] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (M : ι → U →ₗ[ZMod 2] W)
    (hthree : ∀ a b : ι → ZMod 2, ∀ f : U, (∑ i, (a i + b i) • M i) f = 0 →
      f ∈ LinearMap.ker (∑ i, a i • M i) ⊔ LinearMap.ker (∑ i, b i • M i) →
      (∑ i, a i • M i) f = 0) :
    ∃ c : ι → ZMod 2, finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi M))
      ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range (∑ i, c i • M i)) := by
  classical
  let Φ : (ι → ZMod 2) →+ (U →ₗ[ZMod 2] W) :=
    { toFun := fun c => ∑ i, c i • M i
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have h2 : ∀ a : ι → ZMod 2, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hsingle : ∀ i : ι, Φ (Pi.single i 1) = M i := fun i => by
    show ∑ j, (Pi.single i (1 : ZMod 2) : ι → ZMod 2) j • M j = M i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  refine rank_retention Φ h2 (fun a b f h1 h3 => hthree a b f h1 h3) (LinearMap.pi M)
    (Finset.univ.toList.map fun i => Pi.single i 1) ?_
  intro f hf
  funext i
  have := hf (Pi.single i 1) (List.mem_map.2 ⟨i, by simp, rfl⟩)
  rw [hsingle] at this
  simpa using this

end Maps

section Multiplication

open MvPolynomial

variable {σ ι τ : Type*}

/-- The map `f ↦ (f * q * h α mod C)_α` on a subspace `U` of polynomials. -/
noncomputable def mulMap (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) :
    ↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C) :=
  LinearMap.pi fun α => C.mkQ ∘ₗ LinearMap.mulRight (ZMod 2) (q * h α) ∘ₗ U.subtype

theorem mulMap_apply_eq_zero (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) (f : ↥U) :
    mulMap C U h q f = 0 ↔ ∀ α, (f : MvPolynomial σ (ZMod 2)) * q * h α ∈ C := by
  rw [funext_iff]
  refine forall_congr' fun α => ?_
  simp [mulMap, mul_assoc]

/-- The combination `∑ i, c i • g i`. -/
noncomputable def comb [Fintype ι] (g : ι → MvPolynomial σ (ZMod 2)) (c : ι → ZMod 2) :
    MvPolynomial σ (ZMod 2) := ∑ i, c i • g i

/-- Rank retention for multiplication maps, with the two closure properties of `C` that the
proof uses stated directly. `hmul`: at this level membership survives one more factor from
the span of the `g i`. `hidem`: every `comb g c` is idempotent modulo `C` at this level. -/
theorem rank_retention_mul [Fintype ι]
    (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (g : ι → MvPolynomial σ (ZMod 2)) (h : τ → MvPolynomial σ (ZMod 2))
    (hmul : ∀ (c c' : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * comb g c * h α ∈ C → f * comb g c * comb g c' * h α ∈ C)
    (hidem : ∀ (c : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * (comb g c * comb g c + comb g c) * h α ∈ C) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi fun i => mulMap C U h (g i)))
        ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range (mulMap C U h (comb g c))) := by
  classical
  have hcomb_add : ∀ a b : ι → ZMod 2, comb g (a + b) = comb g a + comb g b := fun a b => by
    simp [comb, add_smul, Finset.sum_add_distrib]
  have hcomb_single : ∀ i : ι, comb g (Pi.single i 1) = g i := fun i => by
    show ∑ j, (Pi.single i (1 : ZMod 2) : ι → ZMod 2) j • g j = g i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let Φ : (ι → ZMod 2) →+ (↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C)) :=
    { toFun := fun c => mulMap C U h (comb g c)
      map_zero' := by
        ext f α
        simp [mulMap, comb]
      map_add' := fun a b => by
        ext f α
        simp [mulMap, hcomb_add, add_mul, mul_add, mul_assoc] }
  have h2 : ∀ a : ι → ZMod 2, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hthree : ∀ a b : ι → ZMod 2, ∀ f : ↥U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0 := by
    intro a b f hab hf
    obtain ⟨fa, hfa, fb, hfb, rfl⟩ := Submodule.mem_sup.1 hf
    have hfa' : ∀ α, (fa : MvPolynomial σ (ZMod 2)) * comb g a * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g a) fa).1 hfa
    have hfb' : ∀ α, (fb : MvPolynomial σ (ZMod 2)) * comb g b * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g b) fb).1 hfb
    have hab' : ∀ α, ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g (a + b)) (fa + fb)).1 hab
    refine (mulMap_apply_eq_zero C U h (comb g a) (fa + fb)).2 fun α => ?_
    have A1 := hmul a b α fa fa.2 (hfa' α)
    have A2 := hmul b a α fb fb.2 (hfb' α)
    have A3 := hmul (a + b) a α _ (fa + fb).2 (hab' α)
    have A4 := hidem a α _ (fa + fb).2
    have e : ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g a * h α
        = ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * (comb g a * comb g a + comb g a) * h α
          - ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * comb g a * h α
          + ((fa : MvPolynomial σ (ZMod 2)) * comb g a * comb g b * h α
            + (fb : MvPolynomial σ (ZMod 2)) * comb g b * comb g a * h α) := by
      rw [hcomb_add, Submodule.coe_add]
      ring
    rw [e]
    exact C.add_mem (C.sub_mem A4 A3) (C.add_mem A1 A2)
  obtain ⟨c, hc⟩ := rank_retention Φ h2 hthree
    (LinearMap.pi fun i => mulMap C U h (g i))
    (Finset.univ.toList.map fun i => Pi.single i 1) (by
      intro f hf
      funext i
      have := hf (Pi.single i 1) (List.mem_map.2 ⟨i, by simp, rfl⟩)
      have e : Φ (Pi.single i 1) = mulMap C U h (g i) := by
        show mulMap C U h (comb g (Pi.single i 1)) = _
        rw [hcomb_single]
      rw [e] at this
      simpa using this)
  exact ⟨c, hc⟩

/-- The affine polynomial with constant term `a` and coefficient `B j` at the variable `j`. -/
noncomputable def affine [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) : MvPolynomial σ (ZMod 2) :=
  C a + ∑ j, C (B j) * X j

theorem comb_affine [Fintype σ] [Fintype ι] (a : ι → ZMod 2) (B : ι → σ → ZMod 2)
    (c : ι → ZMod 2) :
    comb (fun i => affine (a i) (B i)) c
      = affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) := by
  simp only [comb, affine, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · simp [map_sum, smul_eq_C_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_sum, Finset.sum_mul, smul_eq_C_mul, mul_assoc]

theorem affine_totalDegree_le [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    (affine a B).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine totalDegree_finsetSum_le fun j _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]

theorem affine_idem [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    affine a B * affine a B + affine a B = ∑ j, C (B j) * (X j * X j + X j) := by
  have ha : ∀ x : ZMod 2, x * x = x := by decide
  have hC : ∀ x : ZMod 2, (C x : MvPolynomial σ (ZMod 2)) * C x = C x := fun x => by
    rw [← C_mul, ha]
  have e1 : (∑ j, (C (B j) : MvPolynomial σ (ZMod 2)) * X j) * (∑ j, C (B j) * X j)
      = ∑ j, C (B j) * (X j * X j) := by
    rw [← sq, CharTwo.sum_sq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sq]
    calc (C (B j) : MvPolynomial σ (ZMod 2)) * X j * (C (B j) * X j)
        = (C (B j) * C (B j)) * (X j * X j) := by ring
      _ = C (B j) * (X j * X j) := by rw [hC]
  rw [affine, CharTwo.add_mul_self, hC, e1]
  have e2 : ∀ u v w : MvPolynomial σ (ZMod 2), u + v + (u + w) = (u + u) + (v + w) :=
    fun u v w => by ring
  rw [e2, CharTwo.add_self_eq_zero, zero_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Rank retention for multiplication by affine polynomials, from the closure properties of
a degree `D` polynomial calculus closure `Cl` containing the Boolean axioms:

* `hX`: a member of degree below `D` may be multiplied by a variable;
* `hBool`: `p * (X j * X j + X j)` is a member as soon as `p` has degree at most `D - 2`.

The domain `U` is any finite dimensional space of polynomials of degree at most `k`, the
`h α` have degree at most `d`, and `d + k + 2 ≤ D`. -/
theorem rank_retention_closure [Fintype σ] [Fintype ι]
    (Cl U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (D k d : ℕ)
    (hX : ∀ p ∈ Cl, p.totalDegree < D → ∀ j, X j * p ∈ Cl)
    (hBool : ∀ p : MvPolynomial σ (ZMod 2), p.totalDegree + 2 ≤ D →
      ∀ j, p * (X j * X j + X j) ∈ Cl)
    (hU : ∀ f ∈ U, f.totalDegree ≤ k)
    (a : ι → ZMod 2) (B : ι → σ → ZMod 2) (h : τ → MvPolynomial σ (ZMod 2))
    (hh : ∀ α, (h α).totalDegree ≤ d) (hD : d + k + 2 ≤ D) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2)
          ↥(LinearMap.range (LinearMap.pi fun i => mulMap Cl U h (affine (a i) (B i))))
        ≤ 2 * finrank (ZMod 2)
          ↥(LinearMap.range (mulMap Cl U h (comb (fun i => affine (a i) (B i)) c))) := by
  have hmulaff : ∀ p ∈ Cl, p.totalDegree < D → ∀ (a' : ZMod 2) (B' : σ → ZMod 2),
      p * affine a' B' ∈ Cl := by
    intro p hp hdeg a' B'
    have e : p * affine a' B' = a' • p + ∑ j, B' j • (X j * p) := by
      rw [affine, mul_add, Finset.mul_sum]
      congr 1
      · rw [smul_eq_C_mul, mul_comm]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_C_mul]
        ring
    rw [e]
    exact Cl.add_mem (Cl.smul_mem _ hp)
      (Cl.sum_mem fun j _ => Cl.smul_mem _ (hX p hp hdeg j))
  refine rank_retention_mul Cl U (fun i => affine (a i) (B i)) h ?_ ?_
  · intro c c' α f hf hmem
    rw [comb_affine] at hmem ⊢
    rw [comb_affine]
    have hdeg : (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) * h α).totalDegree
        < D := by
      have h1 := totalDegree_mul
        (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)) (h α)
      have h2 := totalDegree_mul f (affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j))
      have h3 := hU f hf
      have h4 := hh α
      have h5 := affine_totalDegree_le (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)
      omega
    have := hmulaff _ hmem hdeg (∑ i, c' i * a i) (fun j => ∑ i, c' i * B i j)
    have e : ∀ u v w x : MvPolynomial σ (ZMod 2), u * v * w * x = u * v * x * w :=
      fun u v w x => by ring
    rw [e]
    exact this
  · intro c α f hf
    rw [comb_affine, affine_idem]
    have e : f * (∑ j, C (∑ i, c i * B i j) * (X j * X j + X j)) * h α
        = ∑ j, (∑ i, c i * B i j) • ((f * h α) * (X j * X j + X j)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]
      ring
    rw [e]
    refine Cl.sum_mem fun j _ => Cl.smul_mem _ (hBool _ ?_ j)
    have h1 := totalDegree_mul f (h α)
    have h3 := hU f hf
    have h4 := hh α
    omega

end Multiplication

section Counterexample

/-- Without the three-term property the conclusion fails: for the three coordinate maps on
`(ZMod 2) ^ 3` the stacked map has rank three and every combination has rank at most one. -/
theorem coordinate_maps_no_rank_retention :
    ¬ ∃ c : Fin 3 → ZMod 2,
      finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi
          fun i => (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)))
        ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range
          (∑ i, c i • (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))) := by
  rintro ⟨c, hc⟩
  have h1 : finrank (ZMod 2) ↥(LinearMap.range
      (∑ i, c i • (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))) ≤ 1 := by
    refine (Submodule.finrank_le _).trans ?_
    simp
  have hid : (LinearMap.pi fun i => (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))
      = LinearMap.id := by
    ext u i
    simp
  rw [hid, LinearMap.range_id, finrank_top] at hc
  have h3 : finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by simp
  omega

end Counterexample

end PEqualNP.ProofComplexity.Helpers
