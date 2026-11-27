import PEqualNP.Defs.RiffleRank
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
Helpers for L-gct-095, L-gct-096 and L-gct-097: riffle rank (two blocks) of the tensor square
of the identity, `pairId X F a b c d = [a = b] * [c = d]`.

* `rank_fin_two`: over every commutative ring, `pairId (Fin 2)` is a sum of three riffle-basic
  functions (an explicit identity, checked on all 16 points; no division, valid in
  characteristic 2).
* `of_fintype`: a sum of riffle-basic functions over any finite index type `ι` has riffle rank
  at most `Fintype.card ι`.
* `rank_prod`: riffle rank is submultiplicative on `pairId` under products of index types.
* `rank_of_injective`: `pairId X` inherits any bound of `pairId Y` along an injection `X → Y`.
* `rank_fin_le_pow`: `n ≤ 2 ^ t` gives riffle rank at most `3 ^ t` for `pairId (Fin n)`.
-/

namespace PEqualNP.Gct.Riffle

open PEqualNP.RiffleRank

section

variable {F : Type} [CommRing F]

/-- Transport a riffle rank bound along an equality of the bound. -/
theorem rank_cast {X : Type} {r s : ℕ} {f : X → X → X → X → F} (h : r = s)
    (hf : RiffleRankLe r f) : RiffleRankLe s f := by
  subst h
  exact hf

/-- A sum over any finite index type of riffle-basic functions. -/
theorem of_fintype {X ι : Type} [Fintype ι] (f : X → X → X → X → F)
    (g : ι → X → X → X → X → F) (hg : ∀ i, IsRiffleBasic (g i))
    (hf : ∀ a b c d, f a b c d = ∑ i, g i a b c d) :
    RiffleRankLe (Fintype.card ι) f := by
  let e := Fintype.equivFin ι
  refine ⟨fun k => g (e.symm k), fun k => hg _, fun a b c d => ?_⟩
  rw [hf]
  exact (e.symm.sum_comp (fun i => g i a b c d)).symm

/-- The explicit three-term identity for `pairId (Fin 2)`. -/
theorem rank_fin_two : RiffleRankLe 3 (pairId (Fin 2) F) := by
  let A : Fin 3 → Fin 2 → F :=
    ![fun a => if a = 0 then 1 else 0, fun a => if a = 1 then 1 else 0, fun _ => 1]
  let C : Fin 3 → Fin 2 → Fin 2 → F :=
    ![fun b c => if c = b then 1 else 0, fun b c => if c = b then 0 else 1,
      fun _ c => if c = 1 then 1 else 0]
  let D : Fin 3 → Fin 2 → Fin 2 → F :=
    ![fun b d => if d = b then (if b = 0 then 1 else -1) else 0,
      fun b d => if d = b then 0 else (if b = 0 then -1 else 1),
      fun _ d => if d = 1 then 1 else 0]
  refine ⟨fun i a b c d => A i a * C i b c * D i b d,
    fun i => ⟨A i, C i, D i, fun _ _ _ _ => rfl⟩, fun a b c d => ?_⟩
  rw [Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [A, C, D, pairId]

/-- Product of riffle-basic functions on two index types is riffle-basic on the product. -/
theorem basic_mul {X Y : Type} {g : X → X → X → X → F} {h : Y → Y → Y → Y → F}
    (hg : IsRiffleBasic g) (hh : IsRiffleBasic h) :
    IsRiffleBasic (fun a b c d : X × Y => g a.1 b.1 c.1 d.1 * h a.2 b.2 c.2 d.2) := by
  obtain ⟨A, C, D, hg⟩ := hg
  obtain ⟨A', C', D', hh⟩ := hh
  exact ⟨fun a => A a.1 * A' a.2, fun b c => C b.1 c.1 * C' b.2 c.2,
    fun b d => D b.1 d.1 * D' b.2 d.2, fun a b c d => by
      show g a.1 b.1 c.1 d.1 * h a.2 b.2 c.2 d.2 = _
      rw [hg, hh]; ring⟩

/-- Riffle rank is submultiplicative under the product of index types. -/
theorem rank_mul {X Y : Type} {r s : ℕ} {f : X → X → X → X → F} {f' : Y → Y → Y → Y → F}
    (hf : RiffleRankLe r f) (hf' : RiffleRankLe s f') :
    RiffleRankLe (r * s) (fun a b c d : X × Y => f a.1 b.1 c.1 d.1 * f' a.2 b.2 c.2 d.2) := by
  obtain ⟨g, hg, hsum⟩ := hf
  obtain ⟨h, hh, hsum'⟩ := hf'
  have := of_fintype (fun a b c d : X × Y => f a.1 b.1 c.1 d.1 * f' a.2 b.2 c.2 d.2)
    (fun p : Fin r × Fin s => fun a b c d : X × Y =>
      g p.1 a.1 b.1 c.1 d.1 * h p.2 a.2 b.2 c.2 d.2)
    (fun p => basic_mul (hg p.1) (hh p.2))
    (fun a b c d => by
      rw [hsum, hsum', Finset.sum_mul_sum, Fintype.sum_prod_type])
  exact rank_cast (by simp) this

/-- `pairId` on a product is the product of the `pairId`s. -/
theorem pairId_prod {X Y : Type} [DecidableEq X] [DecidableEq Y] (a b c d : X × Y) :
    pairId (X × Y) F a b c d = pairId X F a.1 b.1 c.1 d.1 * pairId Y F a.2 b.2 c.2 d.2 := by
  unfold pairId
  by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;> by_cases h3 : c.1 = d.1 <;>
    by_cases h4 : c.2 = d.2 <;> simp [Prod.ext_iff, h1, h2, h3, h4]

/-- Submultiplicativity for `pairId`. -/
theorem rank_prod {X Y : Type} [DecidableEq X] [DecidableEq Y] {r s : ℕ}
    (hX : RiffleRankLe r (pairId X F)) (hY : RiffleRankLe s (pairId Y F)) :
    RiffleRankLe (r * s) (pairId (X × Y) F) := by
  have h := rank_mul hX hY
  have he : pairId (X × Y) F =
      (fun a b c d : X × Y => pairId X F a.1 b.1 c.1 d.1 * pairId Y F a.2 b.2 c.2 d.2) := by
    funext a b c d
    exact pairId_prod a b c d
  rw [he]
  exact h

/-- Restriction along a map of a riffle-basic function is riffle-basic. -/
theorem basic_comp {X Y : Type} (e : X → Y) {g : Y → Y → Y → Y → F} (hg : IsRiffleBasic g) :
    IsRiffleBasic (fun a b c d => g (e a) (e b) (e c) (e d)) := by
  obtain ⟨A, C, D, h⟩ := hg
  exact ⟨fun a => A (e a), fun b c => C (e b) (e c), fun b d => D (e b) (e d),
    fun a b c d => h _ _ _ _⟩

/-- A bound for `pairId Y` gives the same bound for `pairId X` along an injection `X → Y`. -/
theorem rank_of_injective {X Y : Type} [DecidableEq X] [DecidableEq Y] {r : ℕ} (e : X → Y)
    (he : Function.Injective e) (h : RiffleRankLe r (pairId Y F)) :
    RiffleRankLe r (pairId X F) := by
  obtain ⟨g, hg, hs⟩ := h
  refine ⟨fun i a b c d => g i (e a) (e b) (e c) (e d), fun i => basic_comp e (hg i),
    fun a b c d => ?_⟩
  rw [← hs]
  simp only [pairId, he.eq_iff]

/-- On a one-point type, `pairId` has riffle rank at most one. -/
theorem rank_fin_one : RiffleRankLe 1 (pairId (Fin 1) F) := by
  refine ⟨fun _ _ _ _ _ => 1, fun _ => ⟨fun _ => 1, fun _ _ => 1, fun _ _ => 1, by simp⟩,
    fun a b c d => ?_⟩
  simp [pairId, Subsingleton.elim a b, Subsingleton.elim c d]

/-- `pairId (Fin (2 ^ t))` has riffle rank at most `3 ^ t`. -/
theorem rank_fin_two_pow (t : ℕ) : RiffleRankLe (3 ^ t) (pairId (Fin (2 ^ t)) F) := by
  induction t with
  | zero => exact rank_fin_one
  | succ t ih =>
    have hp := rank_prod (rank_fin_two (F := F)) ih
    have hn : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
    have he : Function.Injective
        (fun x : Fin (2 ^ (t + 1)) => finProdFinEquiv.symm (Fin.cast hn x)) :=
      finProdFinEquiv.symm.injective.comp (Fin.cast_injective hn)
    exact rank_cast (by ring) (rank_of_injective _ he hp)

/-- `n ≤ 2 ^ t` gives riffle rank at most `3 ^ t` for `pairId (Fin n)`. -/
theorem rank_fin_le_pow {n t : ℕ} (h : n ≤ 2 ^ t) :
    RiffleRankLe (3 ^ t) (pairId (Fin n) F) :=
  rank_of_injective (Fin.castLE h) (Fin.castLE_injective h) (rank_fin_two_pow t)

end

end PEqualNP.Gct.Riffle
