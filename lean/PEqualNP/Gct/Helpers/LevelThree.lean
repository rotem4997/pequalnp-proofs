import PEqualNP.Defs
import PEqualNP.Gct.Helpers.BlockIsotropic

/-! Helper module, proofs only. A linear space of `3 × 3` complex matrices on which the
permanent stays `6` along the all ones matrix has dimension at most three.

Route. In Fourier coordinates for the cyclic shifts of rows and columns (`w` a root of
`w ^ 2 + w + 1`), a matrix `t` of entry sum zero is `fm w x` for eight numbers `x`, and
`perm (J + t) = 6 + 3 * c6 x` for an explicit cubic `c6`. The quadratic part of `c6` pairs the
eight coordinates in four hyperbolic pairs, and a space on which `c6` vanishes is totally
isotropic for it. An isotropic space meets trivially some coordinate space that takes one
coordinate from each pair (`exists_chart`); if its dimension were four it would be a graph over
that chart, given by a skew `4 × 4` array `s`, and the cubic part of `c6` would vanish on the
graph: twenty polynomial equations in the six entries of `s`. For each of the sixteen charts
these equations generate the unit ideal, by an explicit identity (`kern_0000` to `kern_1111`).
Every step is over the complex numbers. -/

namespace PEqualNP.Gct.Helpers.LevelThree

open Finset PEqualNP.Gct.Helpers.BlockIso

/-- The permanent at the all ones matrix, minus six and divided by three, in the eight Fourier
coordinates. -/
def c6 (p1 p2 r1 r2 a1 a2 b1 b2 : ℂ) : ℂ :=
  2 * (p1 ^ 3 + p2 ^ 3 + r1 ^ 3 + r2 ^ 3 + a1 ^ 3 + a2 ^ 3 + b1 ^ 3 + b2 ^ 3) -
    6 * (p1 * p2 + r1 * r2) + 3 * (a1 * a2 + b1 * b2) -
    6 * (r1 * a1 * b1 + r2 * b2 * a2 + p1 * a1 * b2 + p2 * b1 * a2) +
    3 * (p1 * b1 * r2 + p1 * r1 * a2 + p2 * r1 * b2 + p2 * a1 * r2)

/-- The matrix with Fourier coordinates `p1, .., b2` (entry sum zero). -/
def fm (w p1 p2 r1 r2 a1 a2 b1 b2 : ℂ) : Fin 3 × Fin 3 → ℂ := fun q =>
  ![![a1 + a2 + b1 + b2 + p1 + p2 + r1 + r2, a1*w + a2*(-w - 1) + b1*(-w - 1) + b2*w + p1*w +
        p2*(-w - 1) + r1 + r2, a1*(-w - 1) + a2*w + b1*w + b2*(-w - 1) + p1*(-w - 1) + p2*w + r1 +
        r2],
      ![a1*w + a2*(-w - 1) + b1*w + b2*(-w - 1) + p1 + p2 + r1*w + r2*(-w - 1), a1*(-w - 1) +
        a2*w + b1 + b2 + p1*w + p2*(-w - 1) + r1*w + r2*(-w - 1), a1 + a2 + b1*(-w - 1) + b2*w +
        p1*(-w - 1) + p2*w + r1*w + r2*(-w - 1)],
      ![a1*(-w - 1) + a2*w + b1*(-w - 1) + b2*w + p1 + p2 + r1*(-w - 1) + r2*w, a1 + a2 + b1*w +
        b2*(-w - 1) + p1*w + p2*(-w - 1) + r1*(-w - 1) + r2*w, a1*w + a2*(-w - 1) + b1 + b2 +
        p1*(-w - 1) + p2*w + r1*(-w - 1) + r2*w]] q.1 q.2

theorem fm_apply (w p1 p2 r1 r2 a1 a2 b1 b2 : ℂ) (i j : Fin 3) :
    fm w p1 p2 r1 r2 a1 a2 b1 b2 (i, j) =
    ![![a1 + a2 + b1 + b2 + p1 + p2 + r1 + r2, a1*w + a2*(-w - 1) + b1*(-w - 1) + b2*w + p1*w +
        p2*(-w - 1) + r1 + r2, a1*(-w - 1) + a2*w + b1*w + b2*(-w - 1) + p1*(-w - 1) + p2*w + r1 +
        r2],
      ![a1*w + a2*(-w - 1) + b1*w + b2*(-w - 1) + p1 + p2 + r1*w + r2*(-w - 1), a1*(-w - 1) +
        a2*w + b1 + b2 + p1*w + p2*(-w - 1) + r1*w + r2*(-w - 1), a1 + a2 + b1*(-w - 1) + b2*w +
        p1*(-w - 1) + p2*w + r1*w + r2*(-w - 1)],
      ![a1*(-w - 1) + a2*w + b1*(-w - 1) + b2*w + p1 + p2 + r1*(-w - 1) + r2*w, a1 + a2 + b1*w +
        b2*(-w - 1) + p1*w + p2*(-w - 1) + r1*(-w - 1) + r2*w, a1*w + a2*(-w - 1) + b1 + b2 +
        p1*(-w - 1) + p2*w + r1*(-w - 1) + r2*w]] i j := rfl

/-- The permanent along the all ones matrix in Fourier coordinates. -/
theorem perm_fm (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (p1 p2 r1 r2 a1 a2 b1 b2 : ℂ) :
    MvPolynomial.eval (fun q => 1 + fm w p1 p2 r1 r2 a1 a2 b1 b2 q) (PEqualNP.Gct.permPoly ℂ 3) =
      6 + 3 * c6 p1 p2 r1 r2 a1 a2 b1 b2 := by
  rw [PEqualNP.Gct.MethodCeiling.eval_permPoly, permanent_three]
  simp only [Matrix.of_apply, fm_apply, c6, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination
    (-6*a1^3 + 6*a1^2*a2 + 3*a1^2 + 6*a1*a2^2 - 6*a1*a2 - 6*a1*b1*p1 - 6*a1*b1*p2 + 18*a1*b1*r1 -
    6*a1*b1*r2 + 18*a1*b2*p1 - 6*a1*b2*p2 - 6*a1*b2*r1 - 6*a1*b2*r2 + 3*a1*p1*r1 + 3*a1*p1*r2 +
    3*a1*p2*r1 - 9*a1*p2*r2 - 6*a2^3 + 3*a2^2 - 6*a2*b1*p1 + 18*a2*b1*p2 - 6*a2*b1*r1 - 6*a2*b1*r2 -
    6*a2*b2*p1 - 6*a2*b2*p2 - 6*a2*b2*r1 + 18*a2*b2*r2 - 9*a2*p1*r1 + 3*a2*p1*r2 + 3*a2*p2*r1 +
    3*a2*p2*r2 - 6*b1^3 + 6*b1^2*b2 + 3*b1^2 + 6*b1*b2^2 - 6*b1*b2 + 3*b1*p1*r1 - 9*b1*p1*r2 +
    3*b1*p2*r1 + 3*b1*p2*r2 - 6*b2^3 + 3*b2^2 + 3*b2*p1*r1 + 3*b2*p1*r2 - 9*b2*p2*r1 + 3*b2*p2*r2 -
    6*p1^3 + 6*p1^2*p2 - 6*p1^2 + 6*p1*p2^2 + 12*p1*p2 - 6*p2^3 - 6*p2^2 - 6*r1^3 + 6*r1^2*r2 -
    6*r1^2 + 6*r1*r2^2 + 12*r1*r2 - 6*r2^3 - 6*r2^2) * hw

/-- A matrix of entry sum zero has Fourier coordinates. -/
theorem fm_inv (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (t : Fin 3 × Fin 3 → ℂ)
    (h0 : ∑ q, t q = 0) :
    fm w
      (t (0, 0)/9 + t (0, 1)*(-w - 1)/9 + t (0, 2)*w/9 + t (1, 0)/9 + t (1, 1)*(-w - 1)/9 +
        t (1, 2)*w/9 + t (2, 0)/9 + t (2, 1)*(-w - 1)/9 + t (2, 2)*w/9)
      (t (0, 0)/9 + t (0, 1)*w/9 + t (0, 2)*(-w - 1)/9 + t (1, 0)/9 + t (1, 1)*w/9 +
        t (1, 2)*(-w - 1)/9 + t (2, 0)/9 + t (2, 1)*w/9 + t (2, 2)*(-w - 1)/9)
      (t (0, 0)/9 + t (0, 1)/9 + t (0, 2)/9 + t (1, 0)*(-w - 1)/9 + t (1, 1)*(-w - 1)/9 +
        t (1, 2)*(-w - 1)/9 + t (2, 0)*w/9 + t (2, 1)*w/9 + t (2, 2)*w/9)
      (t (0, 0)/9 + t (0, 1)/9 + t (0, 2)/9 + t (1, 0)*w/9 + t (1, 1)*w/9 + t (1, 2)*w/9 +
        t (2, 0)*(-w - 1)/9 + t (2, 1)*(-w - 1)/9 + t (2, 2)*(-w - 1)/9)
      (t (0, 0)/9 + t (0, 1)*(-w - 1)/9 + t (0, 2)*w/9 + t (1, 0)*(-w - 1)/9 + t (1, 1)*w/9 +
        t (1, 2)/9 + t (2, 0)*w/9 + t (2, 1)/9 + t (2, 2)*(-w - 1)/9)
      (t (0, 0)/9 + t (0, 1)*w/9 + t (0, 2)*(-w - 1)/9 + t (1, 0)*w/9 + t (1, 1)*(-w - 1)/9 +
        t (1, 2)/9 + t (2, 0)*(-w - 1)/9 + t (2, 1)/9 + t (2, 2)*w/9)
      (t (0, 0)/9 + t (0, 1)*w/9 + t (0, 2)*(-w - 1)/9 + t (1, 0)*(-w - 1)/9 + t (1, 1)/9 +
        t (1, 2)*w/9 + t (2, 0)*w/9 + t (2, 1)*(-w - 1)/9 + t (2, 2)/9)
      (t (0, 0)/9 + t (0, 1)*(-w - 1)/9 + t (0, 2)*w/9 + t (1, 0)*w/9 + t (1, 1)/9 +
        t (1, 2)*(-w - 1)/9 + t (2, 0)*(-w - 1)/9 + t (2, 1)*w/9 + t (2, 2)/9) = t := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three] at h0
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, fm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · linear_combination (0) * hw + (-1/9) * h0
  · linear_combination (-2*t (0, 1)/3 + 2*t (0, 2)/3) * hw + (-1/9) * h0
  · linear_combination (2*t (0, 1)/3 - 2*t (0, 2)/3) * hw + (-1/9) * h0
  · linear_combination (-2*t (1, 0)/3 + 2*t (2, 0)/3) * hw + (-1/9) * h0
  · linear_combination (-2*t (1, 1)/3 + 2*t (2, 2)/3) * hw + (-1/9) * h0
  · linear_combination (-2*t (1, 2)/3 + 2*t (2, 1)/3) * hw + (-1/9) * h0
  · linear_combination (2*t (1, 0)/3 - 2*t (2, 0)/3) * hw + (-1/9) * h0
  · linear_combination (2*t (1, 2)/3 - 2*t (2, 1)/3) * hw + (-1/9) * h0
  · linear_combination (2*t (1, 1)/3 - 2*t (2, 2)/3) * hw + (-1/9) * h0

/-- The eight coordinates, in four pairs. -/
abbrev E : Type := Fin 4 × Bool → ℂ

/-- The cubic `c6` on the coordinate space. -/
def C6 (x : E) : ℂ :=
  c6 (x (0, false)) (x (0, true)) (x (1, false)) (x (1, true)) (x (2, false)) (x (2, true))
    (x (3, false)) (x (3, true))

/-- The point with given coordinates. -/
def mk8 (p1 p2 r1 r2 a1 a2 b1 b2 : ℂ) : E := fun q =>
  if q.2 then ![p2, r2, a2, b2] q.1 else ![p1, r1, a1, b1] q.1

/-- The Fourier parametrization of the matrices of entry sum zero, as a linear map. -/
noncomputable def fmap (w : ℂ) : E →ₗ[ℂ] (Fin 3 × Fin 3 → ℂ) where
  toFun x := fm w (x (0, false)) (x (0, true)) (x (1, false)) (x (1, true)) (x (2, false))
    (x (2, true)) (x (3, false)) (x (3, true))
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [fm_apply] <;> ring
  map_smul' c x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [fm_apply] <;> ring

theorem fmap_apply (w : ℂ) (x : E) :
    fmap w x = fm w (x (0, false)) (x (0, true)) (x (1, false)) (x (1, true)) (x (2, false))
      (x (2, true)) (x (3, false)) (x (3, true)) := rfl

theorem fmap_mk8 (w p1 p2 r1 r2 a1 a2 b1 b2 : ℂ) :
    fmap w (mk8 p1 p2 r1 r2 a1 a2 b1 b2) = fm w p1 p2 r1 r2 a1 a2 b1 b2 := rfl

/-- The weights of the four pairs in the quadratic part of `c6`, divided by three. -/
def mq : Fin 4 → ℂ := ![-2, -2, 1, 1]

theorem mq_ne_zero (i : Fin 4) : mq i ≠ 0 := by
  fin_cases i <;> simp [mq]

/-- The polar form of the quadratic part of `c6`, divided by six. -/
def bil (x y : E) : ℂ := ∑ i, mq i * (x (i, false) * y (i, true) + x (i, true) * y (i, false))

/-- A space on which `C6` vanishes is totally isotropic. -/
theorem bil_eq_zero (L : Submodule ℂ E) (h : ∀ x ∈ L, C6 x = 0) (x y : E) (hx : x ∈ L)
    (hy : y ∈ L) : bil x y = 0 := by
  have h1 := h _ (L.add_mem hx hy)
  have h2 := h _ (L.neg_mem (L.add_mem hx hy))
  have h3 := h _ (L.sub_mem hx hy)
  have h4 := h _ (L.neg_mem (L.sub_mem hx hy))
  simp only [C6, c6, Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at h1 h2 h3 h4
  simp only [bil, Fin.sum_univ_four, mq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (h1 + h2 - h3 - h4) / 12

/-- The polar form read in any chart. -/
theorem bil_chart (S : Fin 4 → Bool) (x y : E) :
    bil x y = ∑ i, mq i * (x (i, S i) * y (i, !S i) + x (i, !S i) * y (i, S i)) := by
  unfold bil
  refine sum_congr rfl fun i _ => ?_
  cases S i
  · simp only [Bool.not_false]
  · simp only [Bool.not_true]
    ring

/-- The coordinate space of a chart: the chosen coordinate of each pair vanishes. -/
def zs (S : Fin 4 → Bool) : Submodule ℂ E where
  carrier := {x | ∀ i, x (i, S i) = 0}
  add_mem' := by
    intro a b ha hb i
    have ha' : ∀ i, a (i, S i) = 0 := ha
    have hb' : ∀ i, b (i, S i) = 0 := hb
    simp [ha' i, hb' i]
  zero_mem' := fun i => rfl
  smul_mem' := by
    intro c a ha i
    have ha' : ∀ i, a (i, S i) = 0 := ha
    simp [ha' i]

theorem mem_zs (S : Fin 4 → Bool) (x : E) : x ∈ zs S ↔ ∀ i, x (i, S i) = 0 := Iff.rfl

theorem exists_chart_of (L : Submodule ℂ E) (hiso : ∀ x ∈ L, ∀ y ∈ L, bil x y = 0) :
    ∀ n : ℕ, ∀ S : Fin 4 → Bool, Module.finrank ℂ ↥(L ⊓ zs S) = n →
      ∃ S', L ⊓ zs S' = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hb : L ⊓ zs S = ⊥
    · exact ⟨S, hb⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hb
    have hyL : y ∈ L := hy.1
    have hyZ : ∀ i, y (i, S i) = 0 := hy.2
    obtain ⟨k, hk⟩ : ∃ k, y (k, !S k) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hy0
      funext ⟨i, b⟩
      by_cases hbS : b = S i
      · rw [hbS]; exact hyZ i
      · have hb' : b = !S i := by
          cases b <;> cases hS : S i <;> simp_all
        rw [hb']; exact hcon i
    have hlt : L ⊓ zs (Function.update S k (!S k)) < L ⊓ zs S := by
      refine lt_of_le_not_ge ?_ ?_
      · rintro x ⟨hxL, hxZ⟩
        have hxZ' : ∀ i, x (i, Function.update S k (!S k) i) = 0 := hxZ
        refine ⟨hxL, fun i => ?_⟩
        by_cases hik : i = k
        · subst hik
          have hB := hiso x hxL y hyL
          rw [bil_chart S, Finset.sum_eq_single i] at hB
          · rw [hyZ i, mul_zero, add_zero] at hB
            rcases mul_eq_zero.1 hB with h | h
            · exact absurd h (mq_ne_zero i)
            · rcases mul_eq_zero.1 h with h | h
              · exact h
              · exact absurd h hk
          · intro j _ hji
            have := hxZ' j
            rw [Function.update_of_ne hji] at this
            rw [this, hyZ j]
            ring
          · intro hi
            exact absurd (mem_univ i) hi
        · have := hxZ' i
          rwa [Function.update_of_ne hik] at this
      · intro hle
        have := (hle hy).2 k
        rw [Function.update_self] at this
        exact hk this
    exact ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl

/-- An isotropic space meets some chart space trivially. -/
theorem exists_chart (L : Submodule ℂ E) (hiso : ∀ x ∈ L, ∀ y ∈ L, bil x y = 0) :
    ∃ S : Fin 4 → Bool, L ⊓ zs S = ⊥ :=
  exists_chart_of L hiso _ (fun _ => false) rfl

/-- The point of the graph over the chart `S` given by the array `s`, with parameters `a`. -/
noncomputable def pt (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → ℂ) (a : Fin 4 → ℂ) : E :=
  fun q =>
  if q.2 = S q.1 then a q.1 else (∑ k, s q.1 k * a k) / mq q.1

theorem kern_0000 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (12804679412 : ℂ) = 0 := by
    linear_combination
      (-100940115*s12*s24 - 629623636*s12 - 1050640590*s13*s23 + 590437308*s13 - 1425019808*s14 -
      269173640*s23^2 + 1626707160*s23*s24 + 562790482*s23*s34 + 269173640*s24^2 -
      1063916678*s24*s34 - 1086324404) * hpooo + (-184384588*s12*s14 + 273738916*s12*s23 -
      261210507*s12*s24 + 777778360*s12*s34 - 267473014*s12 - 450477348*s13^2 + 300791454*s13*s23 +
      1868745780*s13*s24 - 53844702*s13*s34 - 801025168*s14*s23 + 1205903064*s14*s24 +
      3487568616*s14*s34 - 800718416*s14 + 554532532*s23*s24 + 517642096*s23*s34 - 474350814*s23 -
      283905362) * hopoo + (450477348*s12*s13 + 847759692*s12*s24 + 180380014*s12*s34 -
      267473014*s12 - 2406331632*s13*s23 + 2001298044*s13*s24 - 2579687752*s13*s34 - 50118140*s13 -
      2331065428*s14*s23 - 407417336*s14*s24 + 2497205568*s14*s34 - 269173640*s23^2 +
      517642096*s23*s34 - 1063916678*s24*s34 + 3886284736) * hoopo + (1677358296*s12*s23 -
      160270392*s12*s24 + 330121016*s12*s34 - 316014260*s13*s14 + 1411928436*s13*s23 +
      736668704*s13*s24 - 2528114080*s13*s34 - 50118140*s13 + 463799436*s14*s23 +
      338463700*s14*s24 + 2497205568*s14*s34 - 800718416*s14 - 269173640*s23^2 + 554532532*s23*s24 -
      1063916678*s24*s34 + 3886284736) * hooop + (92192294*s12*s14 + 267473014*s12 +
      225238674*s13^2 - 320277724*s13 + 800718416*s14 - 554532532*s23*s24 - 517642096*s23*s34 +
      237175407*s23) * hppoo + (-225238674*s12*s13 + 267473014*s12 + 50118140*s13 + 312150696*s14 +
      269173640*s23^2 - 536087314*s23*s24 - 517642096*s23*s34 + 1063916678*s24*s34) * hpopo +
      (181075311*s12 + 158007130*s13*s14 + 50118140*s13 + 800718416*s14 + 269173640*s23^2 -
      554532532*s23*s24 - 22574193*s23*s34 - 134586820*s24^2 + 1063916678*s24*s34) * hpoop +
      (-158007130*s13*s14) * hpoom + (225238674*s12*s13) * hpomo + (-92192294*s12*s14 -
      225238674*s13^2 - 237175407*s23) * hpmoo + (160270392*s12*s24 - 388889180*s12*s34 +
      267473014*s12 - 934372890*s13*s24 + 1289843876*s13*s34 + 400512584*s14*s23 +
      203708668*s14*s24 - 2497205568*s14*s34 - 517642096*s23*s34) * hoppo + (-136869458*s12*s23 +
      160270392*s12*s24 - 165060508*s12*s34 - 368334352*s13*s24 + 26922351*s13*s34 -
      231899718*s14*s23 - 602951532*s14*s24 - 2497205568*s14*s34 + 800718416*s14 -
      554532532*s23*s24) * hopop + (165060508*s12*s34 + 368334352*s13*s24 + 231899718*s14*s23) *
      hopom + (-1289843876*s13*s34 - 203708668*s14*s24) * hopmo + (-838679148*s12*s23 +
      160270392*s12*s24 - 90190007*s12*s34 - 1000649022*s13*s24 + 1264057040*s13*s34 +
      50118140*s13 + 1165532714*s14*s23 - 169231850*s14*s24 - 2497205568*s14*s34 + 269173640*s23^2 +
      1063916678*s24*s34) * hoopp + (838679148*s12*s23 - 1264057040*s13*s34 + 169231850*s14*s24) *
      hoopm + (90190007*s12*s34 + 1000649022*s13*s24 - 1165532714*s14*s23) * hoomp +
      (388889180*s12*s34 + 934372890*s13*s24 - 400512584*s14*s23) * hompo + (136869458*s12*s23 -
      26922351*s13*s34 + 602951532*s14*s24) * homop + (320277724*s13) * hmpoo + (-312150696*s14 +
      536087314*s23*s24) * hmopo + (-181075311*s12 + 22574193*s23*s34 + 134586820*s24^2) * hmoop +
      (-267473014*s12 + 517642096*s23*s34) * hpppo + (-800718416*s14 + 554532532*s23*s24) * hppop +
      (-50118140*s13 - 269173640*s23^2 - 1063916678*s24*s34) * hpopp + (-160270392*s12*s24 +
      2497205568*s14*s34) * hoppp
  norm_num at hd

theorem kern_0001 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (111195434608 : ℂ) = 0 := by
    linear_combination
      (-1943933968*s12*s13 + 1501969916*s12*s14 + 139938886*s12*s24 + 509339232*s12 -
      1779480776*s13*s23 + 6190956848*s13*s24 + 1744382272*s13*s34 - 1314753532*s13 +
      960259392*s14^2 + 1145913232*s14*s24 + 16494730432*s23*s34 + 19282327192*s24*s34 -
      7109113984*s34^2 - 1551196912) * hpooo + (-390763992*s12 - 1854199616*s13^2 +
      1740848288*s13*s14 + 1743487272*s13*s23 + 9175163232*s13*s34 + 960259392*s14^2 +
      7444916896*s14*s34 + 229950668*s23 - 1332958872*s24*s34 - 7686680768*s24 - 7109113984*s34^2 -
      3099016216) * hopoo + (1320784768*s12*s13 + 1492069112*s12*s14 - 1390637920*s12*s23 +
      388607200*s12*s34 + 509339232*s12 - 1924052768*s13^2 - 17680425680*s13*s23 +
      1744382272*s13*s34 + 960259392*s14^2 - 5652625696*s14*s23 + 1026160064*s14*s24 +
      7444916896*s14*s34 - 5588953824*s23*s34 - 444319624*s24^2 + 20246533504*s24*s34 +
      4402325888*s34 + 24792129728) * hoopo + (-3300268*s12^2 + 1412862680*s12*s14 -
      109716448*s12*s34 - 1924052768*s13^2 - 12348590192*s13*s23 - 939858800*s13*s24 -
      1036922960*s14*s23 - 4054657728*s14*s24 + 7444916896*s14*s34 + 3372233336*s14 -
      2426820856*s23*s24 - 22969123840*s23*s34 + 20246533504*s24*s34 - 7109113984*s34^2 +
      35455800704) * hooop + (-69969443*s12*s24 - 509339232*s12 - 34926576*s13^2 -
      1744382272*s13*s34 + 657376766*s13 - 960259392*s14^2 - 114975334*s23 + 7109113984*s34^2) *
      hppoo + (-660392384*s12*s13 - 1492069112*s12*s14 - 509339232*s12 + 3732527504*s13*s23 -
      3095478424*s13*s24 - 1744382272*s13*s34 - 960259392*s14^2 - 513080032*s14*s24 +
      2794476912*s23*s34 - 20246533504*s24*s34) * hpopo + (971966984*s12*s13 - 1492069112*s12*s14 +
      54858224*s12*s34 + 3732527504*s13*s23 + 469929400*s13*s24 + 518461480*s14*s23 -
      572956616*s14*s24 - 8247365216*s23*s34 - 20246533504*s24*s34 + 7109113984*s34^2) * hpoop +
      (-54858224*s12*s34 - 469929400*s13*s24 - 518461480*s14*s23) * hpoom + (660392384*s12*s13 +
      513080032*s14*s24 - 2794476912*s23*s34) * hpomo + (34926576*s13^2 + 114975334*s23) * hpmoo +
      (695318960*s12*s23 - 509339232*s12 + 1924052768*s13^2 - 870424144*s13*s14 -
      1744382272*s13*s34 - 960259392*s14^2 - 7444916896*s14*s34 + 222159812*s24^2 + 3843340384*s24 -
      2201162944*s34) * hoppo + (1650134*s12^2 + 450051612*s12 + 1924052768*s13^2 -
      3715390480*s13*s34 - 7444916896*s14*s34 - 1686116668*s14 + 1213410428*s23*s24 +
      7109113984*s34^2) * hopop + (-1650134*s12^2 + 1686116668*s14 - 1213410428*s23*s24) * hopom +
      (-695318960*s12*s23 - 222159812*s24^2 + 2201162944*s34) * hopmo + (-1492069112*s12*s14 -
      194303600*s12*s34 + 1924052768*s13^2 + 3732527504*s13*s23 + 2826312848*s14*s23 +
      2027328864*s14*s24 - 7444916896*s14*s34 + 11484561920*s23*s34 - 20246533504*s24*s34) * hoopp +
      (-2027328864*s14*s24 - 11484561920*s23*s34) * hoopm + (194303600*s12*s34 -
      2826312848*s14*s23) * hoomp + (870424144*s13*s14 - 3843340384*s24) * hompo + (-450051612*s12 +
      3715390480*s13*s34) * homop + (69969443*s12*s24 - 657376766*s13) * hmpoo +
      (3095478424*s13*s24) * hmopo + (-971966984*s12*s13 + 572956616*s14*s24 + 8247365216*s23*s34)
      * hmoop + (509339232*s12 + 1744382272*s13*s34 + 960259392*s14^2) * hpppo +
      (-7109113984*s34^2) * hppop + (1492069112*s12*s14 - 3732527504*s13*s23 +
      20246533504*s24*s34) * hpopp + (-1924052768*s13^2 + 7444916896*s14*s34) * hoppp
  norm_num at hd

theorem kern_0010 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (1950879163944 : ℂ) = 0 := by
    linear_combination
      (-181009399048*s12*s13 - 633621339508*s12*s14 - 230147985564*s12*s24 + 66995821498*s12*s34 -
      815766138516*s12 - 5805117872*s13*s14 - 49732880900*s13*s24 - 1039969222672*s13*s34 -
      144253225512*s14*s23 + 1082266152496*s14*s34 + 10226962528*s14 - 223459361200*s23^2 -
      1174883411440*s23*s24 - 1896868754072*s23*s34 + 139767738320*s24^2 - 189641644352*s34 +
      271009765944) * hpooo + (19120545440*s12*s14 - 230147985564*s12*s24 + 181009399048*s12*s34 -
      86729510018*s13*s14 - 139767738320*s13*s24 - 136319272350*s13*s34 + 714768063840*s14*s23 -
      292732101840*s14*s24 + 10226962528*s14 + 186131854470*s23*s24 - 602842007228*s23*s34 +
      112810759056*s23 + 22473458072*s24 + 271009765944) * hopoo + (-181009399048*s12*s13 -
      341245199844*s12*s14 + 365293113450*s12*s24 + 498338070446*s12*s34 - 5805117872*s13*s14 -
      621377057808*s13 - 42296929824*s14^2 - 492494205476*s14*s23 - 223459361200*s23^2 -
      55864840300*s23*s24 + 623580222616*s23*s34 + 22473458072*s24 - 189641644352*s34 +
      271009765944) * hoopo + (152381548854*s12*s13 - 686723028312*s12*s23 - 126890789472*s13*s14 +
      220891664064*s13*s23 + 643214256080*s14 - 167594520900*s23^2 + 941180185728*s23*s34 +
      22473458072*s24 - 453280376248*s34 + 568924933056) * hooop + (-9560272720*s12*s14 +
      177735083694*s12*s24 - 33497910749*s12*s34 + 5805117872*s13*s14 + 24866440450*s13*s24 +
      68159636175*s13*s34 + 72126612756*s14*s23 - 10226962528*s14 - 93065927235*s23*s24 +
      317599963112*s23*s34 - 271009765944) * hppoo + (181009399048*s12*s13 + 316810669754*s12*s14 +
      177735083694*s12*s24 - 249169035223*s12*s34 + 5805117872*s13*s14 + 519984611336*s13*s34 +
      246247102738*s14*s23 + 223459361200*s23^2 + 587441705720*s23*s24 + 317599963112*s23*s34 +
      189641644352*s34 - 271009765944) * hpopo + (181009399048*s12*s13 + 407883069258*s12 -
      110445832032*s13*s23 - 541133076248*s14*s34 - 10226962528*s14 + 223459361200*s23^2 -
      69883869160*s24^2 + 189641644352*s34) * hpoop + (110445832032*s13*s23) * hpoom +
      (249169035223*s12*s34 - 246247102738*s14*s23) * hpomo + (9560272720*s12*s14 -
      68159636175*s13*s34 + 93065927235*s23*s24) * hpmoo + (170622599922*s12*s14 +
      177735083694*s12*s24 - 90504699524*s12*s34 + 5805117872*s13*s14 + 69883869160*s13*s24 -
      357384031920*s14*s23 + 27932420150*s23*s24 + 317599963112*s23*s34 - 22473458072*s24 -
      271009765944) * hoppo + (-166695473951*s12*s13 + 146366050920*s14*s24 - 10226962528*s14 -
      27932420150*s23^2 - 56405379528*s23 - 22473458072*s24 + 131819365948*s34) * hopop +
      (166695473951*s12*s13 + 27932420150*s23^2 - 131819365948*s34) * hopom +
      (-170622599922*s12*s14 - 27932420150*s23*s24) * hopmo + (181009399048*s12*s13 +
      343361514156*s12*s23 + 310688528904*s13 + 21148464912*s14^2 - 316493646776*s14 +
      223459361200*s23^2 - 22473458072*s24 + 189641644352*s34) * hoopp + (-343361514156*s12*s23 +
      316493646776*s14) * hoopm + (-310688528904*s13 - 21148464912*s14^2) * hoomp +
      (90504699524*s12*s34 - 69883869160*s13*s24 + 357384031920*s14*s23) * hompo +
      (-146366050920*s14*s24 + 56405379528*s23) * homop + (33497910749*s12*s34 -
      24866440450*s13*s24 - 72126612756*s14*s23) * hmpoo + (-316810669754*s12*s14 -
      519984611336*s13*s34 - 587441705720*s23*s24) * hmopo + (-407883069258*s12 +
      541133076248*s14*s34 + 69883869160*s24^2) * hmoop + (-177735083694*s12*s24 -
      5805117872*s13*s14 - 317599963112*s23*s34 + 271009765944) * hpppo + (10226962528*s14) *
      hppop + (-181009399048*s12*s13 - 223459361200*s23^2 - 189641644352*s34) * hpopp +
      (22473458072*s24) * hoppp
  norm_num at hd

theorem kern_0011 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (69245537376 : ℂ) = 0 := by
    linear_combination
      (-1893883992*s12^2 - 7780209256*s12*s14 + 1447337476*s12*s24 + 1152589908*s13*s14 -
      1494026416*s13*s23 + 3749055632*s13*s24 + 21096017136*s13*s34 + 13455700880*s13 +
      8921524416*s14*s24 - 1662584048*s14 + 381871236*s23^2 - 4832412076*s23*s24 +
      1010087808*s34^2 - 21298316608) * hpooo + (4363875662*s12*s14 + 4928970376*s12*s23 -
      674915508*s12*s34 - 11691806704*s12 + 27566097664*s13^2 + 27589560224*s13*s14 +
      29685892248*s13*s34 - 29727051056*s14^2 + 757273202*s14*s23 + 381871236*s23^2 -
      2759928916*s23*s24 + 1345849824*s24*s34 - 3338517216*s34 + 25716461132) * hopoo +
      (-1893883992*s12^2 + 3320087024*s12*s14 + 4928970376*s12*s23 + 2363134260*s12*s24 +
      294492204*s12*s34 + 27566097664*s13^2 + 2058154976*s13*s14 - 1494026416*s13*s23 +
      469250268*s13*s24 + 21096017136*s13*s34 + 7330535508*s14*s23 - 17475327616*s14*s34 -
      1662584048*s14 + 3538718780*s23*s24 + 27542635104*s23*s34 - 18801284640*s23 -
      18142243680*s24^2 - 3338517216*s34 + 12677364920) * hoopo + (2154144314*s12^2 -
      378782928*s12*s14 + 4443740990*s12*s23 + 27566097664*s13^2 - 1494026416*s13*s23 -
      3030263424*s13*s34 - 6466557776*s14 - 16414522620*s23^2 - 4037549472*s23*s24 -
      39429076960*s24 + 16587264192*s34 + 18808495584) * hooop + (-3320087024*s12*s14 -
      723668738*s12*s24 + 337457754*s12*s34 - 576294954*s13*s14 - 21096017136*s13*s34 -
      378636601*s14*s23 - 381871236*s23^2 - 3538718780*s23*s24 - 854157560) * hppoo +
      (1893883992*s12^2 - 3320087024*s12*s14 - 1181567130*s12*s24 - 1029077488*s13*s14 +
      1494026416*s13*s23 - 1874527816*s13*s24 - 21096017136*s13*s34 + 1662584048*s14 -
      3538718780*s23*s24 - 13771317552*s23*s34 - 854157560) * hpopo + (1893883992*s12^2 +
      242614693*s12*s23 + 1494026416*s13*s23 - 6727850440*s13 - 4460762208*s14*s24 +
      1662584048*s14 - 381871236*s23^2 - 505043904*s34^2 - 9962890704*s34) * hpoop +
      (-242614693*s12*s23 + 9962890704*s34) * hpoom + (1181567130*s12*s24 + 1029077488*s13*s14 +
      13771317552*s23*s34) * hpomo + (-337457754*s12*s34 + 378636601*s14*s23) * hpmoo +
      (-3320087024*s12*s14 - 4928970376*s12*s23 - 147246102*s12*s34 - 27566097664*s13^2 -
      13794780112*s13*s14 - 234625134*s13*s24 - 21096017136*s13*s34 - 3665267754*s14*s23 -
      3538718780*s23*s24 + 3338517216*s34 - 854157560) * hoppo + (-2024014153*s12^2 -
      4928970376*s12*s23 + 5845903352*s12 - 27566097664*s13^2 + 14863525528*s14^2 + 2401986864*s14 -
      381871236*s23^2 - 672924912*s24*s34 + 3338517216*s34) * hopop + (2024014153*s12^2 -
      2401986864*s14) * hopom + (147246102*s12*s34 + 234625134*s13*s24 + 3665267754*s14*s23) *
      hopmo + (1893883992*s12^2 - 4928970376*s12*s23 - 27566097664*s13^2 + 1494026416*s13*s23 +
      8737663808*s14*s34 + 1662584048*s14 + 8398196928*s23^2 + 9400642320*s23 + 9071121840*s24^2 +
      19714538480*s24 + 3338517216*s34) * hoopp + (-8398196928*s23^2 - 19714538480*s24) * hoopm +
      (-8737663808*s14*s34 - 9400642320*s23 - 9071121840*s24^2) * hoomp + (13794780112*s13*s14) *
      hompo + (-5845903352*s12 - 14863525528*s14^2 + 672924912*s24*s34) * homop +
      (723668738*s12*s24 + 576294954*s13*s14) * hmpoo + (1874527816*s13*s24) * hmopo +
      (6727850440*s13 + 4460762208*s14*s24 + 505043904*s34^2) * hmoop + (3320087024*s12*s14 +
      21096017136*s13*s34 + 3538718780*s23*s24 + 854157560) * hpppo + (381871236*s23^2) * hppop +
      (-1893883992*s12^2 - 1494026416*s13*s23 - 1662584048*s14) * hpopp + (4928970376*s12*s23 +
      27566097664*s13^2 - 3338517216*s34) * hoppp
  norm_num at hd

theorem kern_0100 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (108552063040 : ℂ) = 0 := by
    linear_combination
      (-10610594976*s12^2 - 53922148848*s12*s13 + 6950981840*s12*s23 + 21830966120*s12*s34 -
      5387203744*s13*s23 - 65726854816*s13*s24 - 2803119712*s13 - 97635095040*s14*s24 +
      37295443968*s14*s34 + 207681362784*s14 - 95392822272*s23*s24 - 123240113632*s23 +
      211651922778*s24*s34 + 35535773312) * hpooo + (-55696572480*s12*s13 + 139975964388*s12*s23 -
      47751992034*s12*s24 + 57985623824*s12*s34 + 65726854816*s13^2 - 69203684192*s13*s14 +
      14976788200*s13*s24 + 23149083664*s14*s23 + 402894867216*s14*s34 - 232397807016*s23*s24 +
      403893830624*s23*s34 - 123240113632*s23 - 501180434560*s24*s34 + 142666188480*s34 +
      159314065760) * hopoo + (-11202069520*s12^2 + 182985175392*s12*s13 + 113099572888*s12*s14 -
      47751992034*s12*s24 - 264482942272*s13 - 114458131378*s14*s24 + 127710335520*s23*s24 -
      242102528672*s23 - 82518861632*s24^2 - 102310618272*s34 + 143712378944) * hoopo +
      (-10610594976*s12^2 + 61795704552*s12*s13 - 16904681912*s12*s23 - 47751992034*s12*s24 +
      190462693216*s12*s34 - 74314754506*s13*s24 - 2803119712*s13 - 144342157612*s14*s23 -
      97635095040*s14*s24 + 37295443968*s14*s34 - 179805465568*s23^2 + 270563181840*s23*s24 -
      250250386208*s24 + 142666188480*s34 - 284286186496) * hooop + (55696572480*s12*s13 -
      3475490920*s12*s23 - 28992811912*s12*s34 - 7488394100*s13*s24 - 11574541832*s14*s23 -
      37295443968*s14*s34 + 149006965488*s23*s24 + 123240113632*s23 - 105825961389*s24*s34) *
      hppoo + (10610594976*s12^2 + 2693601872*s13*s23 + 2803119712*s13 + 97635095040*s14*s24 -
      103840681392*s14 + 123240113632*s23 + 122488403376*s34) * hpopo + (10610594976*s12^2 +
      55696572480*s12*s13 + 8452340956*s12*s23 - 10915483060*s12*s34 + 32863427408*s13*s24 +
      2803119712*s13 + 97635095040*s14*s24 - 37295443968*s14*s34 + 149006965488*s23*s24) * hpoop +
      (-8452340956*s12*s23) * hpoom + (-122488403376*s34) * hpomo + (28992811912*s12*s34 +
      7488394100*s13*s24 + 11574541832*s14*s23) * hpmoo + (295737272*s12^2 + 47751992034*s12*s24 -
      32863427408*s13^2 + 130839911280*s13 + 8411518169*s14*s24 - 201946915312*s23*s34 +
      123240113632*s23 - 142666188480*s34) * hoppo + (55696572480*s12*s13 - 69987982194*s12*s23 +
      47751992034*s12*s24 - 95231346608*s12*s34 + 34601842096*s13*s14 + 37157377253*s13*s24 +
      72171078806*s14*s23 - 37295443968*s14*s34 + 149006965488*s23*s24 + 250590217280*s24*s34 -
      142666188480*s34) * hopop + (95231346608*s12*s34 - 37157377253*s13*s24 -
      72171078806*s14*s23) * hopom + (-295737272*s12^2 - 130839911280*s13 - 8411518169*s14*s24) *
      hopmo + (10610594976*s12^2 - 56549786444*s12*s14 + 47751992034*s12*s24 + 2803119712*s13 +
      97635095040*s14*s24 + 89902732784*s23^2 + 59431207520*s23 + 41259430816*s24^2 +
      125125193104*s24 - 142666188480*s34) * hoopp + (-89902732784*s23^2 - 125125193104*s24) *
      hoopm + (56549786444*s12*s14 - 59431207520*s23 - 41259430816*s24^2) * hoomp +
      (32863427408*s13^2 + 201946915312*s23*s34) * hompo + (69987982194*s12*s23 -
      34601842096*s13*s14 - 250590217280*s24*s34) * homop + (3475490920*s12*s23 +
      105825961389*s24*s34) * hmpoo + (-2693601872*s13*s23 + 103840681392*s14) * hmopo +
      (10915483060*s12*s34 - 32863427408*s13*s24) * hmoop + (-123240113632*s23) * hpppo +
      (-55696572480*s12*s13 + 37295443968*s14*s34 - 149006965488*s23*s24) * hppop +
      (-10610594976*s12^2 - 2803119712*s13 - 97635095040*s14*s24) * hpopp + (-47751992034*s12*s24 +
      142666188480*s34) * hoppp
  norm_num at hd

theorem kern_0101 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (8189516920 : ℂ) = 0 := by
    linear_combination
      (869590945*s12*s13 - 47254140*s12*s14 + 26071140*s12*s23 - 389218700*s13*s14 -
      156426840*s13*s24 + 4705405632*s14*s23 - 122040120*s14*s24 - 1697661576*s14*s34 +
      1002607808*s14 - 183083300*s24^2 + 2213375840*s34^2 + 34051430) * hpooo + (127792125*s12*s13 +
      159623860*s12 + 208569120*s13^2 - 943890580*s13*s14 - 992927500*s13*s34 - 4562462204*s14^2 +
      607410648*s14*s24 + 9316377768*s14*s34 + 896040600*s23 - 553538480*s24 + 2630514080*s34^2 +
      34051430) * hopoo + (345169180*s12*s13 - 4933527312*s12*s14 - 389218700*s13*s14 +
      265762640*s13*s34 + 837759210*s13 - 3226089456*s14^2 + 109172700*s14*s23 +
      19569078744*s14*s24 - 475364600*s23*s24 + 1251414720*s23*s34 + 3802916800*s24*s34 -
      459755280*s24 + 2213375840*s34^2 + 979003280) * hoopo + (2385741940*s12*s13 +
      1355177668*s12*s14 - 201888220*s12*s24 - 3307995040*s12*s34 - 1415116980*s13*s23 -
      436792000*s13*s24 + 265762640*s13*s34 - 3226089456*s14^2 + 7024079664*s14*s23 -
      6522866808*s14*s24 - 1697661576*s14*s34 - 52142280*s23^2 + 807552880*s24*s34 - 459755280*s24 +
      823677200*s34 + 3047652320) * hooop + (-13035570*s12*s23 + 389218700*s13*s14 +
      629345070*s13*s34 + 668186374*s14^2 + 1697661576*s14*s34 - 501303904*s14 + 91541650*s24^2 +
      46891600*s24 - 2213375840*s34^2) * hppoo + (-741798820*s12*s13 + 23627070*s12*s14 +
      389218700*s13*s14 - 54586350*s14*s23 - 2730417576*s14*s24 - 2213375840*s34^2) * hpopo +
      (-741798820*s12*s13 - 677588834*s12*s14 + 707558490*s13*s23 + 78213420*s13*s24 -
      2352702816*s14*s23 - 2730417576*s14*s24 + 1697661576*s14*s34 - 403776440*s24*s34) * hpoop +
      (677588834*s12*s14 - 707558490*s13*s23 + 403776440*s24*s34) * hpoom + (54586350*s14*s23) *
      hpomo + (-629345070*s13*s34 - 668186374*s14^2 - 46891600*s24) * hpmoo + (-79811930*s12 -
      104284560*s13^2 + 389218700*s13*s14 - 265762640*s13*s34 - 418879605*s13 + 3226089456*s14^2 -
      5507019672*s14*s34 + 237682300*s23*s24 + 459755280*s24 - 2213375840*s34^2) * hoppo +
      (100944110*s12*s24 + 277335940*s13*s14 - 265762640*s13*s34 + 3226089456*s14^2 +
      1697661576*s14*s34 + 26071140*s23^2 - 448020300*s23 + 459755280*s24 - 208569120*s34^2 -
      411838600*s34) * hopop + (-100944110*s12*s24 - 26071140*s23^2 + 411838600*s34) * hopom +
      (418879605*s13 - 237682300*s23*s24) * hopmo + (-741798820*s12*s13 + 2466763656*s12*s14 +
      1653997520*s12*s34 + 218396000*s13*s24 - 265762640*s13*s34 + 3226089456*s14^2 -
      3512039832*s14*s23 - 2730417576*s14*s24 - 1901458400*s24*s34 + 459755280*s24) * hoopp +
      (-1653997520*s12*s34 - 218396000*s13*s24 + 3512039832*s14*s23) * hoopm +
      (-2466763656*s12*s14 + 1901458400*s24*s34) * hoomp + (79811930*s12 + 104284560*s13^2 +
      5507019672*s14*s34) * hompo + (-277335940*s13*s14 + 448020300*s23 + 208569120*s34^2) * homop +
      (13035570*s12*s23 + 501303904*s14 - 91541650*s24^2) * hmpoo + (-23627070*s12*s14) * hmopo +
      (-78213420*s13*s24 + 2352702816*s14*s23) * hmoop + (-389218700*s13*s14 + 2213375840*s34^2) *
      hpppo + (-1697661576*s14*s34) * hppop + (741798820*s12*s13 + 2730417576*s14*s24) * hpopp +
      (265762640*s13*s34 - 3226089456*s14^2 - 459755280*s24) * hoppp
  norm_num at hd

theorem kern_0110 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (2817374734680 : ℂ) = 0 := by
    linear_combination
      (27505610124*s12*s13 - 185854457528*s12*s14 - 110497962426*s12*s23 + 40043364584*s12*s34 +
      122866320448*s12 - 27998333508*s13*s14 - 7365898464*s13*s24 + 72162218272*s13*s34 -
      224975445872*s13 - 154166033056*s14^2 + 132220423392*s14*s34 + 218688738624*s23^2 -
      235765335600*s24^2 - 112147107344*s24*s34 + 138311060000*s34 + 336449793756) * hpooo +
      (-65027870490*s12*s13 + 2577372060*s12*s23 - 479791556208*s12*s34 + 193734645312*s13*s14 -
      224975445872*s13 - 154166033056*s14^2 + 72222169280*s14*s23 + 162532050928*s14*s24 +
      53940799076*s23*s24 - 112147107344*s24*s34 + 347912442944*s24 + 172464253952*s34^2 +
      110299124784) * hopoo + (37691778162*s12^2 - 227552200932*s12*s14 - 676685192352*s12*s23 +
      465223210608*s12*s24 + 167389662528*s13*s14 - 1888548436112*s13 - 731147879616*s14^2 -
      90204837288*s14*s24 + 117711576328*s23 - 235765335600*s24^2 + 517392761856*s24*s34 +
      138311060000*s34 + 429739433472) * hoopo + (88272644016*s12*s13 - 185854457528*s12*s14 +
      698015381040*s12*s23 + 40043364584*s12*s34 - 372599204896*s13^2 - 313108186320*s13*s14 -
      68132932356*s13*s24 + 474232099320*s14*s23 + 162532050928*s14*s24 + 558321186080*s14*s34 +
      421417626848*s14 + 245852246432*s23*s24 + 2139282225408*s23*s34 - 235765335600*s24^2 -
      112147107344*s24*s34 + 138311060000*s34 + 532199015328) * hooop + (32513935245*s12*s13 -
      20021682292*s12*s34 - 132650076144*s13*s14 + 3682949232*s13*s24 + 224975445872*s13 +
      154166033056*s14^2 - 26970399538*s23*s24 + 112147107344*s24*s34) * hppoo +
      (-18845889081*s12^2 + 185854457528*s12*s14 - 61433160224*s12 - 36081109136*s13*s34 +
      224975445872*s13 + 154166033056*s14^2 + 126368444108*s14*s24 - 109344369312*s23^2 -
      58855788164*s23 + 235765335600*s24^2 - 138311060000*s34) * hpopo + (-13752805062*s12*s13 +
      185854457528*s12*s14 - 20021682292*s12*s34 - 132650076144*s13*s14 + 34066466178*s13*s24 -
      237116049660*s14*s23 - 66110211696*s14*s34 + 235765335600*s24^2 + 112147107344*s24*s34 -
      138311060000*s34) * hpoop + (20021682292*s12*s34 - 34066466178*s13*s24 +
      237116049660*s14*s23) * hpoom + (18845889081*s12^2 - 126368444108*s14*s24 + 58855788164*s23)
      * hpomo + (-32513935245*s12*s13 + 26970399538*s23*s24) * hpmoo + (20848871702*s12*s14 +
      224975445872*s13 + 154166033056*s14^2 - 162532050928*s14*s24 - 173956221472*s24 -
      86232126976*s34^2) * hoppo + (-44136322008*s12*s13 + 239895778104*s12*s34 -
      132650076144*s13*s14 - 36111084640*s14*s23 - 162532050928*s14*s24 - 279160593040*s14*s34 -
      122926123216*s23*s24 + 112147107344*s24*s34) * hopop + (44136322008*s12*s13 +
      279160593040*s14*s34 + 122926123216*s23*s24) * hopom + (-20848871702*s12*s14) * hopmo +
      (185854457528*s12*s14 - 232611605304*s12*s24 + 186299602448*s13^2 + 831786495120*s13 +
      288490923280*s14^2 - 162532050928*s14*s24 - 210708813424*s14 - 1069641112704*s23*s34 +
      235765335600*s24^2 - 138311060000*s34) * hoopp + (-186299602448*s13^2 + 210708813424*s14 +
      1069641112704*s23*s34) * hoopm + (232611605304*s12*s24 - 831786495120*s13 -
      288490923280*s14^2) * hoomp + (173956221472*s24 + 86232126976*s34^2) * hompo +
      (-239895778104*s12*s34 + 36111084640*s14*s23) * homop + (20021682292*s12*s34 -
      3682949232*s13*s24) * hmpoo + (61433160224*s12 + 36081109136*s13*s34 + 109344369312*s23^2) *
      hmopo + (13752805062*s12*s13 + 66110211696*s14*s34) * hmoop + (-224975445872*s13 -
      154166033056*s14^2) * hpppo + (132650076144*s13*s14 - 112147107344*s24*s34) * hppop +
      (-185854457528*s12*s14 - 235765335600*s24^2 + 138311060000*s34) * hpopp +
      (162532050928*s14*s24) * hoppp
  norm_num at hd

theorem kern_0111 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        a1 ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (1392708219400 : ℂ) = 0 := by
    linear_combination
      (1464396084*s12*s23 + 53778740634*s12 - 34444979784*s13 - 13405701258*s14*s24 +
      5861422854*s14 - 65937484116*s23^2 - 23504754384*s23*s24 + 55274062446*s24^2 +
      46833041340*s24*s34 + 8005774464*s34^2 - 32031670252) * hpooo + (-97893198*s12*s13 -
      20055700386*s12*s23 - 90440630136*s13*s34 + 27343206432*s13 - 18968441004*s14^2 +
      44933816592*s14*s23 - 68988077460*s14*s24 - 147713046048*s14*s34 + 6640015212*s23^2 +
      15552191304*s23*s24 + 46833041340*s24*s34 - 32114763900*s24 + 8005774464*s34^2 -
      74653510928) * hopoo + (9170080614*s12^2 - 63094943736*s12*s23 - 124131329856*s12*s24 +
      12888457632*s12*s34 - 49562018640*s13*s14 + 391572792*s13*s24 - 239146970400*s13*s34 +
      27343206432*s13 - 5569178400*s14*s23 - 368172302076*s14*s24 + 396496149120*s14*s34 -
      33640766028*s14 + 15552191304*s23*s24 + 51499818306*s23 + 51521373252*s24^2 +
      8005774464*s34^2 + 432711243616) * hoopo + (25081524792*s12*s14 - 153565349256*s12*s23 -
      2360394594*s12*s24 + 68319378144*s12*s34 - 117224048448*s13*s24 - 239146970400*s13*s34 -
      46500546528*s14*s23 - 471742740828*s14*s24 + 26965454256*s14*s34 - 33640766028*s14 +
      6640015212*s23^2 + 51521373252*s24^2 + 46833041340*s24*s34 + 444719905312) * hooop +
      (48946599*s12*s13 - 27343206432*s13 + 9484220502*s14^2 - 19751094441*s14 - 6640015212*s23^2 -
      15552191304*s23*s24 - 1876344597*s24^2 - 46833041340*s24*s34 + 16057381950*s24 -
      8005774464*s34^2) * hppoo + (-4585040307*s12^2 - 26889370317*s12 + 24781009320*s13*s14 -
      27343206432*s13 + 33640766028*s14 + 36288749664*s23^2 - 15552191304*s23*s24 -
      25749909153*s23 - 51521373252*s24^2 - 8005774464*s34^2) * hpopo + (-12540762396*s12*s14 +
      30894093108*s13 + 33640766028*s14 - 6640015212*s23^2 + 19528472844*s23*s24 -
      51521373252*s24^2 - 46833041340*s24*s34) * hpoop + (12540762396*s12*s14) * hpoom +
      (4585040307*s12^2 - 24781009320*s13*s14 + 25749909153*s23) * hpomo + (-48946599*s12*s13 -
      9484220502*s14^2 - 16057381950*s24) * hpmoo + (49030338312*s12*s23 - 6444228816*s12*s34 -
      195786396*s13*s24 + 239146970400*s13*s34 - 27343206432*s13 + 2784589200*s14*s23 +
      123745766796*s14*s24 + 73856523024*s14*s34 - 15552191304*s23*s24 - 8005774464*s34^2 -
      12398643008) * hoppo + (49030338312*s12*s23 + 1180197297*s12*s24 + 239146970400*s13*s34 -
      22466908296*s14*s23 + 123745766796*s14*s24 - 13482727128*s14*s34 - 6640015212*s23^2 -
      46833041340*s24*s34 - 12398643008) * hopop + (-1180197297*s12*s24 + 13482727128*s14*s34) *
      hopom + (6444228816*s12*s34 + 195786396*s13*s24 - 2784589200*s14*s23) * hopmo +
      (49030338312*s12*s23 + 62065664928*s12*s24 - 34159689072*s12*s34 + 58612024224*s13*s24 +
      239146970400*s13*s34 + 23250273264*s14*s23 + 123745766796*s14*s24 - 198248074560*s14*s34 +
      33640766028*s14 - 51521373252*s24^2 - 12398643008) * hoopp + (34159689072*s12*s34 -
      58612024224*s13*s24 - 23250273264*s14*s23) * hoopm + (-62065664928*s12*s24 +
      198248074560*s14*s34) * hoomp + (-73856523024*s14*s34) * hompo + (22466908296*s14*s23) *
      homop + (19751094441*s14 + 1876344597*s24^2) * hmpoo + (26889370317*s12 - 36288749664*s23^2)
      * hmopo + (-30894093108*s13 - 19528472844*s23*s24) * hmoop + (27343206432*s13 +
      15552191304*s23*s24 + 8005774464*s34^2) * hpppo + (6640015212*s23^2 + 46833041340*s24*s34) *
      hppop + (-33640766028*s14 + 51521373252*s24^2) * hpopp + (-49030338312*s12*s23 -
      239146970400*s13*s34 - 123745766796*s14*s24 + 12398643008) * hoppp
  norm_num at hd

theorem kern_1000 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (1392708219400 : ℂ) = 0 := by
    linear_combination
      (1464396084*s12*s23 + 53778740634*s12 - 34444979784*s13 - 13405701258*s14*s24 +
      5861422854*s14 - 65937484116*s23^2 - 23504754384*s23*s24 + 55274062446*s24^2 +
      46833041340*s24*s34 + 8005774464*s34^2 - 32031670252) * hpooo + (-97893198*s12*s13 -
      20055700386*s12*s23 - 90440630136*s13*s34 + 27343206432*s13 - 18968441004*s14^2 +
      44933816592*s14*s23 - 68988077460*s14*s24 - 147713046048*s14*s34 + 6640015212*s23^2 +
      15552191304*s23*s24 + 46833041340*s24*s34 - 32114763900*s24 + 8005774464*s34^2 -
      74653510928) * hopoo + (9170080614*s12^2 - 63094943736*s12*s23 - 124131329856*s12*s24 +
      12888457632*s12*s34 - 49562018640*s13*s14 + 391572792*s13*s24 - 239146970400*s13*s34 +
      27343206432*s13 - 5569178400*s14*s23 - 368172302076*s14*s24 + 396496149120*s14*s34 -
      33640766028*s14 + 15552191304*s23*s24 + 51499818306*s23 + 51521373252*s24^2 +
      8005774464*s34^2 + 432711243616) * hoopo + (25081524792*s12*s14 - 153565349256*s12*s23 -
      2360394594*s12*s24 + 68319378144*s12*s34 - 117224048448*s13*s24 - 239146970400*s13*s34 -
      46500546528*s14*s23 - 471742740828*s14*s24 + 26965454256*s14*s34 - 33640766028*s14 +
      6640015212*s23^2 + 51521373252*s24^2 + 46833041340*s24*s34 + 444719905312) * hooop +
      (48946599*s12*s13 - 27343206432*s13 + 9484220502*s14^2 - 19751094441*s14 - 6640015212*s23^2 -
      15552191304*s23*s24 - 1876344597*s24^2 - 46833041340*s24*s34 + 16057381950*s24 -
      8005774464*s34^2) * hppoo + (-4585040307*s12^2 - 26889370317*s12 + 24781009320*s13*s14 -
      27343206432*s13 + 33640766028*s14 + 36288749664*s23^2 - 15552191304*s23*s24 -
      25749909153*s23 - 51521373252*s24^2 - 8005774464*s34^2) * hpopo + (-12540762396*s12*s14 +
      30894093108*s13 + 33640766028*s14 - 6640015212*s23^2 + 19528472844*s23*s24 -
      51521373252*s24^2 - 46833041340*s24*s34) * hpoop + (12540762396*s12*s14) * hpoom +
      (4585040307*s12^2 - 24781009320*s13*s14 + 25749909153*s23) * hpomo + (-48946599*s12*s13 -
      9484220502*s14^2 - 16057381950*s24) * hpmoo + (49030338312*s12*s23 - 6444228816*s12*s34 -
      195786396*s13*s24 + 239146970400*s13*s34 - 27343206432*s13 + 2784589200*s14*s23 +
      123745766796*s14*s24 + 73856523024*s14*s34 - 15552191304*s23*s24 - 8005774464*s34^2 -
      12398643008) * hoppo + (49030338312*s12*s23 + 1180197297*s12*s24 + 239146970400*s13*s34 -
      22466908296*s14*s23 + 123745766796*s14*s24 - 13482727128*s14*s34 - 6640015212*s23^2 -
      46833041340*s24*s34 - 12398643008) * hopop + (-1180197297*s12*s24 + 13482727128*s14*s34) *
      hopom + (6444228816*s12*s34 + 195786396*s13*s24 - 2784589200*s14*s23) * hopmo +
      (49030338312*s12*s23 + 62065664928*s12*s24 - 34159689072*s12*s34 + 58612024224*s13*s24 +
      239146970400*s13*s34 + 23250273264*s14*s23 + 123745766796*s14*s24 - 198248074560*s14*s34 +
      33640766028*s14 - 51521373252*s24^2 - 12398643008) * hoopp + (34159689072*s12*s34 -
      58612024224*s13*s24 - 23250273264*s14*s23) * hoopm + (-62065664928*s12*s24 +
      198248074560*s14*s34) * hoomp + (-73856523024*s14*s34) * hompo + (22466908296*s14*s23) *
      homop + (19751094441*s14 + 1876344597*s24^2) * hmpoo + (26889370317*s12 - 36288749664*s23^2)
      * hmopo + (-30894093108*s13 - 19528472844*s23*s24) * hmoop + (27343206432*s13 +
      15552191304*s23*s24 + 8005774464*s34^2) * hpppo + (6640015212*s23^2 + 46833041340*s24*s34) *
      hppop + (-33640766028*s14 + 51521373252*s24^2) * hpopp + (-49030338312*s12*s23 -
      239146970400*s13*s34 - 123745766796*s14*s24 + 12398643008) * hoppp
  norm_num at hd

theorem kern_1001 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (2817374734680 : ℂ) = 0 := by
    linear_combination
      (27505610124*s12*s13 - 185854457528*s12*s14 - 110497962426*s12*s23 + 40043364584*s12*s34 +
      122866320448*s12 - 27998333508*s13*s14 - 7365898464*s13*s24 + 72162218272*s13*s34 -
      224975445872*s13 - 154166033056*s14^2 + 132220423392*s14*s34 + 218688738624*s23^2 -
      235765335600*s24^2 - 112147107344*s24*s34 + 138311060000*s34 + 336449793756) * hpooo +
      (-65027870490*s12*s13 + 2577372060*s12*s23 - 479791556208*s12*s34 + 193734645312*s13*s14 -
      224975445872*s13 - 154166033056*s14^2 + 72222169280*s14*s23 + 162532050928*s14*s24 +
      53940799076*s23*s24 - 112147107344*s24*s34 + 347912442944*s24 + 172464253952*s34^2 +
      110299124784) * hopoo + (37691778162*s12^2 - 227552200932*s12*s14 - 676685192352*s12*s23 +
      465223210608*s12*s24 + 167389662528*s13*s14 - 1888548436112*s13 - 731147879616*s14^2 -
      90204837288*s14*s24 + 117711576328*s23 - 235765335600*s24^2 + 517392761856*s24*s34 +
      138311060000*s34 + 429739433472) * hoopo + (88272644016*s12*s13 - 185854457528*s12*s14 +
      698015381040*s12*s23 + 40043364584*s12*s34 - 372599204896*s13^2 - 313108186320*s13*s14 -
      68132932356*s13*s24 + 474232099320*s14*s23 + 162532050928*s14*s24 + 558321186080*s14*s34 +
      421417626848*s14 + 245852246432*s23*s24 + 2139282225408*s23*s34 - 235765335600*s24^2 -
      112147107344*s24*s34 + 138311060000*s34 + 532199015328) * hooop + (32513935245*s12*s13 -
      20021682292*s12*s34 - 132650076144*s13*s14 + 3682949232*s13*s24 + 224975445872*s13 +
      154166033056*s14^2 - 26970399538*s23*s24 + 112147107344*s24*s34) * hppoo +
      (-18845889081*s12^2 + 185854457528*s12*s14 - 61433160224*s12 - 36081109136*s13*s34 +
      224975445872*s13 + 154166033056*s14^2 + 126368444108*s14*s24 - 109344369312*s23^2 -
      58855788164*s23 + 235765335600*s24^2 - 138311060000*s34) * hpopo + (-13752805062*s12*s13 +
      185854457528*s12*s14 - 20021682292*s12*s34 - 132650076144*s13*s14 + 34066466178*s13*s24 -
      237116049660*s14*s23 - 66110211696*s14*s34 + 235765335600*s24^2 + 112147107344*s24*s34 -
      138311060000*s34) * hpoop + (20021682292*s12*s34 - 34066466178*s13*s24 +
      237116049660*s14*s23) * hpoom + (18845889081*s12^2 - 126368444108*s14*s24 + 58855788164*s23)
      * hpomo + (-32513935245*s12*s13 + 26970399538*s23*s24) * hpmoo + (20848871702*s12*s14 +
      224975445872*s13 + 154166033056*s14^2 - 162532050928*s14*s24 - 173956221472*s24 -
      86232126976*s34^2) * hoppo + (-44136322008*s12*s13 + 239895778104*s12*s34 -
      132650076144*s13*s14 - 36111084640*s14*s23 - 162532050928*s14*s24 - 279160593040*s14*s34 -
      122926123216*s23*s24 + 112147107344*s24*s34) * hopop + (44136322008*s12*s13 +
      279160593040*s14*s34 + 122926123216*s23*s24) * hopom + (-20848871702*s12*s14) * hopmo +
      (185854457528*s12*s14 - 232611605304*s12*s24 + 186299602448*s13^2 + 831786495120*s13 +
      288490923280*s14^2 - 162532050928*s14*s24 - 210708813424*s14 - 1069641112704*s23*s34 +
      235765335600*s24^2 - 138311060000*s34) * hoopp + (-186299602448*s13^2 + 210708813424*s14 +
      1069641112704*s23*s34) * hoopm + (232611605304*s12*s24 - 831786495120*s13 -
      288490923280*s14^2) * hoomp + (173956221472*s24 + 86232126976*s34^2) * hompo +
      (-239895778104*s12*s34 + 36111084640*s14*s23) * homop + (20021682292*s12*s34 -
      3682949232*s13*s24) * hmpoo + (61433160224*s12 + 36081109136*s13*s34 + 109344369312*s23^2) *
      hmopo + (13752805062*s12*s13 + 66110211696*s14*s34) * hmoop + (-224975445872*s13 -
      154166033056*s14^2) * hpppo + (132650076144*s13*s14 - 112147107344*s24*s34) * hppop +
      (-185854457528*s12*s14 - 235765335600*s24^2 + 138311060000*s34) * hpopp +
      (162532050928*s14*s24) * hoppp
  norm_num at hd

theorem kern_1010 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (8189516920 : ℂ) = 0 := by
    linear_combination
      (869590945*s12*s13 - 47254140*s12*s14 + 26071140*s12*s23 - 389218700*s13*s14 -
      156426840*s13*s24 + 4705405632*s14*s23 - 122040120*s14*s24 - 1697661576*s14*s34 +
      1002607808*s14 - 183083300*s24^2 + 2213375840*s34^2 + 34051430) * hpooo + (127792125*s12*s13 +
      159623860*s12 + 208569120*s13^2 - 943890580*s13*s14 - 992927500*s13*s34 - 4562462204*s14^2 +
      607410648*s14*s24 + 9316377768*s14*s34 + 896040600*s23 - 553538480*s24 + 2630514080*s34^2 +
      34051430) * hopoo + (345169180*s12*s13 - 4933527312*s12*s14 - 389218700*s13*s14 +
      265762640*s13*s34 + 837759210*s13 - 3226089456*s14^2 + 109172700*s14*s23 +
      19569078744*s14*s24 - 475364600*s23*s24 + 1251414720*s23*s34 + 3802916800*s24*s34 -
      459755280*s24 + 2213375840*s34^2 + 979003280) * hoopo + (2385741940*s12*s13 +
      1355177668*s12*s14 - 201888220*s12*s24 - 3307995040*s12*s34 - 1415116980*s13*s23 -
      436792000*s13*s24 + 265762640*s13*s34 - 3226089456*s14^2 + 7024079664*s14*s23 -
      6522866808*s14*s24 - 1697661576*s14*s34 - 52142280*s23^2 + 807552880*s24*s34 - 459755280*s24 +
      823677200*s34 + 3047652320) * hooop + (-13035570*s12*s23 + 389218700*s13*s14 +
      629345070*s13*s34 + 668186374*s14^2 + 1697661576*s14*s34 - 501303904*s14 + 91541650*s24^2 +
      46891600*s24 - 2213375840*s34^2) * hppoo + (-741798820*s12*s13 + 23627070*s12*s14 +
      389218700*s13*s14 - 54586350*s14*s23 - 2730417576*s14*s24 - 2213375840*s34^2) * hpopo +
      (-741798820*s12*s13 - 677588834*s12*s14 + 707558490*s13*s23 + 78213420*s13*s24 -
      2352702816*s14*s23 - 2730417576*s14*s24 + 1697661576*s14*s34 - 403776440*s24*s34) * hpoop +
      (677588834*s12*s14 - 707558490*s13*s23 + 403776440*s24*s34) * hpoom + (54586350*s14*s23) *
      hpomo + (-629345070*s13*s34 - 668186374*s14^2 - 46891600*s24) * hpmoo + (-79811930*s12 -
      104284560*s13^2 + 389218700*s13*s14 - 265762640*s13*s34 - 418879605*s13 + 3226089456*s14^2 -
      5507019672*s14*s34 + 237682300*s23*s24 + 459755280*s24 - 2213375840*s34^2) * hoppo +
      (100944110*s12*s24 + 277335940*s13*s14 - 265762640*s13*s34 + 3226089456*s14^2 +
      1697661576*s14*s34 + 26071140*s23^2 - 448020300*s23 + 459755280*s24 - 208569120*s34^2 -
      411838600*s34) * hopop + (-100944110*s12*s24 - 26071140*s23^2 + 411838600*s34) * hopom +
      (418879605*s13 - 237682300*s23*s24) * hopmo + (-741798820*s12*s13 + 2466763656*s12*s14 +
      1653997520*s12*s34 + 218396000*s13*s24 - 265762640*s13*s34 + 3226089456*s14^2 -
      3512039832*s14*s23 - 2730417576*s14*s24 - 1901458400*s24*s34 + 459755280*s24) * hoopp +
      (-1653997520*s12*s34 - 218396000*s13*s24 + 3512039832*s14*s23) * hoopm +
      (-2466763656*s12*s14 + 1901458400*s24*s34) * hoomp + (79811930*s12 + 104284560*s13^2 +
      5507019672*s14*s34) * hompo + (-277335940*s13*s14 + 448020300*s23 + 208569120*s34^2) * homop +
      (13035570*s12*s23 + 501303904*s14 - 91541650*s24^2) * hmpoo + (-23627070*s12*s14) * hmopo +
      (-78213420*s13*s24 + 2352702816*s14*s23) * hmoop + (-389218700*s13*s14 + 2213375840*s34^2) *
      hpppo + (-1697661576*s14*s34) * hppop + (741798820*s12*s13 + 2730417576*s14*s24) * hpopp +
      (265762640*s13*s34 - 3226089456*s14^2 - 459755280*s24) * hoppp
  norm_num at hd

theorem kern_1011 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 a2 ((-s12 * a1 + s23 * a3 + s24 *
        a4) / (-2)) ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (108552063040 : ℂ) = 0 := by
    linear_combination
      (-10610594976*s12^2 - 53922148848*s12*s13 + 6950981840*s12*s23 + 21830966120*s12*s34 -
      5387203744*s13*s23 - 65726854816*s13*s24 - 2803119712*s13 - 97635095040*s14*s24 +
      37295443968*s14*s34 + 207681362784*s14 - 95392822272*s23*s24 - 123240113632*s23 +
      211651922778*s24*s34 + 35535773312) * hpooo + (-55696572480*s12*s13 + 139975964388*s12*s23 -
      47751992034*s12*s24 + 57985623824*s12*s34 + 65726854816*s13^2 - 69203684192*s13*s14 +
      14976788200*s13*s24 + 23149083664*s14*s23 + 402894867216*s14*s34 - 232397807016*s23*s24 +
      403893830624*s23*s34 - 123240113632*s23 - 501180434560*s24*s34 + 142666188480*s34 +
      159314065760) * hopoo + (-11202069520*s12^2 + 182985175392*s12*s13 + 113099572888*s12*s14 -
      47751992034*s12*s24 - 264482942272*s13 - 114458131378*s14*s24 + 127710335520*s23*s24 -
      242102528672*s23 - 82518861632*s24^2 - 102310618272*s34 + 143712378944) * hoopo +
      (-10610594976*s12^2 + 61795704552*s12*s13 - 16904681912*s12*s23 - 47751992034*s12*s24 +
      190462693216*s12*s34 - 74314754506*s13*s24 - 2803119712*s13 - 144342157612*s14*s23 -
      97635095040*s14*s24 + 37295443968*s14*s34 - 179805465568*s23^2 + 270563181840*s23*s24 -
      250250386208*s24 + 142666188480*s34 - 284286186496) * hooop + (55696572480*s12*s13 -
      3475490920*s12*s23 - 28992811912*s12*s34 - 7488394100*s13*s24 - 11574541832*s14*s23 -
      37295443968*s14*s34 + 149006965488*s23*s24 + 123240113632*s23 - 105825961389*s24*s34) *
      hppoo + (10610594976*s12^2 + 2693601872*s13*s23 + 2803119712*s13 + 97635095040*s14*s24 -
      103840681392*s14 + 123240113632*s23 + 122488403376*s34) * hpopo + (10610594976*s12^2 +
      55696572480*s12*s13 + 8452340956*s12*s23 - 10915483060*s12*s34 + 32863427408*s13*s24 +
      2803119712*s13 + 97635095040*s14*s24 - 37295443968*s14*s34 + 149006965488*s23*s24) * hpoop +
      (-8452340956*s12*s23) * hpoom + (-122488403376*s34) * hpomo + (28992811912*s12*s34 +
      7488394100*s13*s24 + 11574541832*s14*s23) * hpmoo + (295737272*s12^2 + 47751992034*s12*s24 -
      32863427408*s13^2 + 130839911280*s13 + 8411518169*s14*s24 - 201946915312*s23*s34 +
      123240113632*s23 - 142666188480*s34) * hoppo + (55696572480*s12*s13 - 69987982194*s12*s23 +
      47751992034*s12*s24 - 95231346608*s12*s34 + 34601842096*s13*s14 + 37157377253*s13*s24 +
      72171078806*s14*s23 - 37295443968*s14*s34 + 149006965488*s23*s24 + 250590217280*s24*s34 -
      142666188480*s34) * hopop + (95231346608*s12*s34 - 37157377253*s13*s24 -
      72171078806*s14*s23) * hopom + (-295737272*s12^2 - 130839911280*s13 - 8411518169*s14*s24) *
      hopmo + (10610594976*s12^2 - 56549786444*s12*s14 + 47751992034*s12*s24 + 2803119712*s13 +
      97635095040*s14*s24 + 89902732784*s23^2 + 59431207520*s23 + 41259430816*s24^2 +
      125125193104*s24 - 142666188480*s34) * hoopp + (-89902732784*s23^2 - 125125193104*s24) *
      hoopm + (56549786444*s12*s14 - 59431207520*s23 - 41259430816*s24^2) * hoomp +
      (32863427408*s13^2 + 201946915312*s23*s34) * hompo + (69987982194*s12*s23 -
      34601842096*s13*s14 - 250590217280*s24*s34) * homop + (3475490920*s12*s23 +
      105825961389*s24*s34) * hmpoo + (-2693601872*s13*s23 + 103840681392*s14) * hmopo +
      (10915483060*s12*s34 - 32863427408*s13*s24) * hmoop + (-123240113632*s23) * hpppo +
      (-55696572480*s12*s13 + 37295443968*s14*s34 - 149006965488*s23*s24) * hppop +
      (-10610594976*s12^2 - 2803119712*s13 - 97635095040*s14*s24) * hpopp + (-47751992034*s12*s24 +
      142666188480*s34) * hoppp
  norm_num at hd

theorem kern_1100 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (69245537376 : ℂ) = 0 := by
    linear_combination
      (-1893883992*s12^2 - 7780209256*s12*s14 + 1447337476*s12*s24 + 1152589908*s13*s14 -
      1494026416*s13*s23 + 3749055632*s13*s24 + 21096017136*s13*s34 + 13455700880*s13 +
      8921524416*s14*s24 - 1662584048*s14 + 381871236*s23^2 - 4832412076*s23*s24 +
      1010087808*s34^2 - 21298316608) * hpooo + (4363875662*s12*s14 + 4928970376*s12*s23 -
      674915508*s12*s34 - 11691806704*s12 + 27566097664*s13^2 + 27589560224*s13*s14 +
      29685892248*s13*s34 - 29727051056*s14^2 + 757273202*s14*s23 + 381871236*s23^2 -
      2759928916*s23*s24 + 1345849824*s24*s34 - 3338517216*s34 + 25716461132) * hopoo +
      (-1893883992*s12^2 + 3320087024*s12*s14 + 4928970376*s12*s23 + 2363134260*s12*s24 +
      294492204*s12*s34 + 27566097664*s13^2 + 2058154976*s13*s14 - 1494026416*s13*s23 +
      469250268*s13*s24 + 21096017136*s13*s34 + 7330535508*s14*s23 - 17475327616*s14*s34 -
      1662584048*s14 + 3538718780*s23*s24 + 27542635104*s23*s34 - 18801284640*s23 -
      18142243680*s24^2 - 3338517216*s34 + 12677364920) * hoopo + (2154144314*s12^2 -
      378782928*s12*s14 + 4443740990*s12*s23 + 27566097664*s13^2 - 1494026416*s13*s23 -
      3030263424*s13*s34 - 6466557776*s14 - 16414522620*s23^2 - 4037549472*s23*s24 -
      39429076960*s24 + 16587264192*s34 + 18808495584) * hooop + (-3320087024*s12*s14 -
      723668738*s12*s24 + 337457754*s12*s34 - 576294954*s13*s14 - 21096017136*s13*s34 -
      378636601*s14*s23 - 381871236*s23^2 - 3538718780*s23*s24 - 854157560) * hppoo +
      (1893883992*s12^2 - 3320087024*s12*s14 - 1181567130*s12*s24 - 1029077488*s13*s14 +
      1494026416*s13*s23 - 1874527816*s13*s24 - 21096017136*s13*s34 + 1662584048*s14 -
      3538718780*s23*s24 - 13771317552*s23*s34 - 854157560) * hpopo + (1893883992*s12^2 +
      242614693*s12*s23 + 1494026416*s13*s23 - 6727850440*s13 - 4460762208*s14*s24 +
      1662584048*s14 - 381871236*s23^2 - 505043904*s34^2 - 9962890704*s34) * hpoop +
      (-242614693*s12*s23 + 9962890704*s34) * hpoom + (1181567130*s12*s24 + 1029077488*s13*s14 +
      13771317552*s23*s34) * hpomo + (-337457754*s12*s34 + 378636601*s14*s23) * hpmoo +
      (-3320087024*s12*s14 - 4928970376*s12*s23 - 147246102*s12*s34 - 27566097664*s13^2 -
      13794780112*s13*s14 - 234625134*s13*s24 - 21096017136*s13*s34 - 3665267754*s14*s23 -
      3538718780*s23*s24 + 3338517216*s34 - 854157560) * hoppo + (-2024014153*s12^2 -
      4928970376*s12*s23 + 5845903352*s12 - 27566097664*s13^2 + 14863525528*s14^2 + 2401986864*s14 -
      381871236*s23^2 - 672924912*s24*s34 + 3338517216*s34) * hopop + (2024014153*s12^2 -
      2401986864*s14) * hopom + (147246102*s12*s34 + 234625134*s13*s24 + 3665267754*s14*s23) *
      hopmo + (1893883992*s12^2 - 4928970376*s12*s23 - 27566097664*s13^2 + 1494026416*s13*s23 +
      8737663808*s14*s34 + 1662584048*s14 + 8398196928*s23^2 + 9400642320*s23 + 9071121840*s24^2 +
      19714538480*s24 + 3338517216*s34) * hoopp + (-8398196928*s23^2 - 19714538480*s24) * hoopm +
      (-8737663808*s14*s34 - 9400642320*s23 - 9071121840*s24^2) * hoomp + (13794780112*s13*s14) *
      hompo + (-5845903352*s12 - 14863525528*s14^2 + 672924912*s24*s34) * homop +
      (723668738*s12*s24 + 576294954*s13*s14) * hmpoo + (1874527816*s13*s24) * hmopo +
      (6727850440*s13 + 4460762208*s14*s24 + 505043904*s34^2) * hmoop + (3320087024*s12*s14 +
      21096017136*s13*s34 + 3538718780*s23*s24 + 854157560) * hpppo + (381871236*s23^2) * hppop +
      (-1893883992*s12^2 - 1494026416*s13*s23 - 1662584048*s14) * hpopp + (4928970376*s12*s23 +
      27566097664*s13^2 - 3338517216*s34) * hoppp
  norm_num at hd

theorem kern_1101 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 a3 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (1950879163944 : ℂ) = 0 := by
    linear_combination
      (-181009399048*s12*s13 - 633621339508*s12*s14 - 230147985564*s12*s24 + 66995821498*s12*s34 -
      815766138516*s12 - 5805117872*s13*s14 - 49732880900*s13*s24 - 1039969222672*s13*s34 -
      144253225512*s14*s23 + 1082266152496*s14*s34 + 10226962528*s14 - 223459361200*s23^2 -
      1174883411440*s23*s24 - 1896868754072*s23*s34 + 139767738320*s24^2 - 189641644352*s34 +
      271009765944) * hpooo + (19120545440*s12*s14 - 230147985564*s12*s24 + 181009399048*s12*s34 -
      86729510018*s13*s14 - 139767738320*s13*s24 - 136319272350*s13*s34 + 714768063840*s14*s23 -
      292732101840*s14*s24 + 10226962528*s14 + 186131854470*s23*s24 - 602842007228*s23*s34 +
      112810759056*s23 + 22473458072*s24 + 271009765944) * hopoo + (-181009399048*s12*s13 -
      341245199844*s12*s14 + 365293113450*s12*s24 + 498338070446*s12*s34 - 5805117872*s13*s14 -
      621377057808*s13 - 42296929824*s14^2 - 492494205476*s14*s23 - 223459361200*s23^2 -
      55864840300*s23*s24 + 623580222616*s23*s34 + 22473458072*s24 - 189641644352*s34 +
      271009765944) * hoopo + (152381548854*s12*s13 - 686723028312*s12*s23 - 126890789472*s13*s14 +
      220891664064*s13*s23 + 643214256080*s14 - 167594520900*s23^2 + 941180185728*s23*s34 +
      22473458072*s24 - 453280376248*s34 + 568924933056) * hooop + (-9560272720*s12*s14 +
      177735083694*s12*s24 - 33497910749*s12*s34 + 5805117872*s13*s14 + 24866440450*s13*s24 +
      68159636175*s13*s34 + 72126612756*s14*s23 - 10226962528*s14 - 93065927235*s23*s24 +
      317599963112*s23*s34 - 271009765944) * hppoo + (181009399048*s12*s13 + 316810669754*s12*s14 +
      177735083694*s12*s24 - 249169035223*s12*s34 + 5805117872*s13*s14 + 519984611336*s13*s34 +
      246247102738*s14*s23 + 223459361200*s23^2 + 587441705720*s23*s24 + 317599963112*s23*s34 +
      189641644352*s34 - 271009765944) * hpopo + (181009399048*s12*s13 + 407883069258*s12 -
      110445832032*s13*s23 - 541133076248*s14*s34 - 10226962528*s14 + 223459361200*s23^2 -
      69883869160*s24^2 + 189641644352*s34) * hpoop + (110445832032*s13*s23) * hpoom +
      (249169035223*s12*s34 - 246247102738*s14*s23) * hpomo + (9560272720*s12*s14 -
      68159636175*s13*s34 + 93065927235*s23*s24) * hpmoo + (170622599922*s12*s14 +
      177735083694*s12*s24 - 90504699524*s12*s34 + 5805117872*s13*s14 + 69883869160*s13*s24 -
      357384031920*s14*s23 + 27932420150*s23*s24 + 317599963112*s23*s34 - 22473458072*s24 -
      271009765944) * hoppo + (-166695473951*s12*s13 + 146366050920*s14*s24 - 10226962528*s14 -
      27932420150*s23^2 - 56405379528*s23 - 22473458072*s24 + 131819365948*s34) * hopop +
      (166695473951*s12*s13 + 27932420150*s23^2 - 131819365948*s34) * hopom +
      (-170622599922*s12*s14 - 27932420150*s23*s24) * hopmo + (181009399048*s12*s13 +
      343361514156*s12*s23 + 310688528904*s13 + 21148464912*s14^2 - 316493646776*s14 +
      223459361200*s23^2 - 22473458072*s24 + 189641644352*s34) * hoopp + (-343361514156*s12*s23 +
      316493646776*s14) * hoopm + (-310688528904*s13 - 21148464912*s14^2) * hoomp +
      (90504699524*s12*s34 - 69883869160*s13*s24 + 357384031920*s14*s23) * hompo +
      (-146366050920*s14*s24 + 56405379528*s23) * homop + (33497910749*s12*s34 -
      24866440450*s13*s24 - 72126612756*s14*s23) * hmpoo + (-316810669754*s12*s14 -
      519984611336*s13*s34 - 587441705720*s23*s24) * hmopo + (-407883069258*s12 +
      541133076248*s14*s34 + 69883869160*s24^2) * hmoop + (-177735083694*s12*s24 -
      5805117872*s13*s14 - 317599963112*s23*s34 + 271009765944) * hpppo + (10226962528*s14) *
      hppop + (-181009399048*s12*s13 - 223459361200*s23^2 - 189641644352*s34) * hpopp +
      (22473458072*s24) * hoppp
  norm_num at hd

theorem kern_1110 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 a4 ((-s14 * a1 + -s24 *
        a2 + -s34 * a3) / 1) = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (111195434608 : ℂ) = 0 := by
    linear_combination
      (-1943933968*s12*s13 + 1501969916*s12*s14 + 139938886*s12*s24 + 509339232*s12 -
      1779480776*s13*s23 + 6190956848*s13*s24 + 1744382272*s13*s34 - 1314753532*s13 +
      960259392*s14^2 + 1145913232*s14*s24 + 16494730432*s23*s34 + 19282327192*s24*s34 -
      7109113984*s34^2 - 1551196912) * hpooo + (-390763992*s12 - 1854199616*s13^2 +
      1740848288*s13*s14 + 1743487272*s13*s23 + 9175163232*s13*s34 + 960259392*s14^2 +
      7444916896*s14*s34 + 229950668*s23 - 1332958872*s24*s34 - 7686680768*s24 - 7109113984*s34^2 -
      3099016216) * hopoo + (1320784768*s12*s13 + 1492069112*s12*s14 - 1390637920*s12*s23 +
      388607200*s12*s34 + 509339232*s12 - 1924052768*s13^2 - 17680425680*s13*s23 +
      1744382272*s13*s34 + 960259392*s14^2 - 5652625696*s14*s23 + 1026160064*s14*s24 +
      7444916896*s14*s34 - 5588953824*s23*s34 - 444319624*s24^2 + 20246533504*s24*s34 +
      4402325888*s34 + 24792129728) * hoopo + (-3300268*s12^2 + 1412862680*s12*s14 -
      109716448*s12*s34 - 1924052768*s13^2 - 12348590192*s13*s23 - 939858800*s13*s24 -
      1036922960*s14*s23 - 4054657728*s14*s24 + 7444916896*s14*s34 + 3372233336*s14 -
      2426820856*s23*s24 - 22969123840*s23*s34 + 20246533504*s24*s34 - 7109113984*s34^2 +
      35455800704) * hooop + (-69969443*s12*s24 - 509339232*s12 - 34926576*s13^2 -
      1744382272*s13*s34 + 657376766*s13 - 960259392*s14^2 - 114975334*s23 + 7109113984*s34^2) *
      hppoo + (-660392384*s12*s13 - 1492069112*s12*s14 - 509339232*s12 + 3732527504*s13*s23 -
      3095478424*s13*s24 - 1744382272*s13*s34 - 960259392*s14^2 - 513080032*s14*s24 +
      2794476912*s23*s34 - 20246533504*s24*s34) * hpopo + (971966984*s12*s13 - 1492069112*s12*s14 +
      54858224*s12*s34 + 3732527504*s13*s23 + 469929400*s13*s24 + 518461480*s14*s23 -
      572956616*s14*s24 - 8247365216*s23*s34 - 20246533504*s24*s34 + 7109113984*s34^2) * hpoop +
      (-54858224*s12*s34 - 469929400*s13*s24 - 518461480*s14*s23) * hpoom + (660392384*s12*s13 +
      513080032*s14*s24 - 2794476912*s23*s34) * hpomo + (34926576*s13^2 + 114975334*s23) * hpmoo +
      (695318960*s12*s23 - 509339232*s12 + 1924052768*s13^2 - 870424144*s13*s14 -
      1744382272*s13*s34 - 960259392*s14^2 - 7444916896*s14*s34 + 222159812*s24^2 + 3843340384*s24 -
      2201162944*s34) * hoppo + (1650134*s12^2 + 450051612*s12 + 1924052768*s13^2 -
      3715390480*s13*s34 - 7444916896*s14*s34 - 1686116668*s14 + 1213410428*s23*s24 +
      7109113984*s34^2) * hopop + (-1650134*s12^2 + 1686116668*s14 - 1213410428*s23*s24) * hopom +
      (-695318960*s12*s23 - 222159812*s24^2 + 2201162944*s34) * hopmo + (-1492069112*s12*s14 -
      194303600*s12*s34 + 1924052768*s13^2 + 3732527504*s13*s23 + 2826312848*s14*s23 +
      2027328864*s14*s24 - 7444916896*s14*s34 + 11484561920*s23*s34 - 20246533504*s24*s34) * hoopp +
      (-2027328864*s14*s24 - 11484561920*s23*s34) * hoopm + (194303600*s12*s34 -
      2826312848*s14*s23) * hoomp + (870424144*s13*s14 - 3843340384*s24) * hompo + (-450051612*s12 +
      3715390480*s13*s34) * homop + (69969443*s12*s24 - 657376766*s13) * hmpoo +
      (3095478424*s13*s24) * hmopo + (-971966984*s12*s13 + 572956616*s14*s24 + 8247365216*s23*s34)
      * hmoop + (509339232*s12 + 1744382272*s13*s34 + 960259392*s14^2) * hpppo +
      (-7109113984*s34^2) * hppop + (1492069112*s12*s14 - 3732527504*s13*s23 +
      20246533504*s24*s34) * hpopp + (-1924052768*s13^2 + 7444916896*s14*s34) * hoppp
  norm_num at hd

theorem kern_1111 (s12 s13 s14 s23 s24 s34 : ℂ)
    (h : ∀ a1 a2 a3 a4 : ℂ, c6
        ((s12 * a2 + s13 * a3 + s14 * a4) / (-2)) a1 ((-s12 * a1 + s23 * a3 + s24 * a4)
        / (-2)) a2 ((-s13 * a1 + -s23 * a2 + s34 * a4) / 1) a3 ((-s14 * a1 + -s24 * a2 +
        -s34 * a3) / 1) a4 = 0) :
    False := by
  simp only [c6] at h
  have hpooo := h 1 0 0 0
  have hopoo := h 0 1 0 0
  have hoopo := h 0 0 1 0
  have hooop := h 0 0 0 1
  have hppoo := h 1 1 0 0
  have hpopo := h 1 0 1 0
  have hpoop := h 1 0 0 1
  have hpoom := h 1 0 0 (-1)
  have hpomo := h 1 0 (-1) 0
  have hpmoo := h 1 (-1) 0 0
  have hoppo := h 0 1 1 0
  have hopop := h 0 1 0 1
  have hopom := h 0 1 0 (-1)
  have hopmo := h 0 1 (-1) 0
  have hoopp := h 0 0 1 1
  have hoopm := h 0 0 1 (-1)
  have hoomp := h 0 0 (-1) 1
  have hompo := h 0 (-1) 1 0
  have homop := h 0 (-1) 0 1
  have hmpoo := h (-1) 1 0 0
  have hmopo := h (-1) 0 1 0
  have hmoop := h (-1) 0 0 1
  have hpppo := h 1 1 1 0
  have hppop := h 1 1 0 1
  have hpopp := h 1 0 1 1
  have hoppp := h 0 1 1 1
  have hd : (12804679412 : ℂ) = 0 := by
    linear_combination
      (-100940115*s12*s24 - 629623636*s12 - 1050640590*s13*s23 + 590437308*s13 - 1425019808*s14 -
      269173640*s23^2 + 1626707160*s23*s24 + 562790482*s23*s34 + 269173640*s24^2 -
      1063916678*s24*s34 - 1086324404) * hpooo + (-184384588*s12*s14 + 273738916*s12*s23 -
      261210507*s12*s24 + 777778360*s12*s34 - 267473014*s12 - 450477348*s13^2 + 300791454*s13*s23 +
      1868745780*s13*s24 - 53844702*s13*s34 - 801025168*s14*s23 + 1205903064*s14*s24 +
      3487568616*s14*s34 - 800718416*s14 + 554532532*s23*s24 + 517642096*s23*s34 - 474350814*s23 -
      283905362) * hopoo + (450477348*s12*s13 + 847759692*s12*s24 + 180380014*s12*s34 -
      267473014*s12 - 2406331632*s13*s23 + 2001298044*s13*s24 - 2579687752*s13*s34 - 50118140*s13 -
      2331065428*s14*s23 - 407417336*s14*s24 + 2497205568*s14*s34 - 269173640*s23^2 +
      517642096*s23*s34 - 1063916678*s24*s34 + 3886284736) * hoopo + (1677358296*s12*s23 -
      160270392*s12*s24 + 330121016*s12*s34 - 316014260*s13*s14 + 1411928436*s13*s23 +
      736668704*s13*s24 - 2528114080*s13*s34 - 50118140*s13 + 463799436*s14*s23 +
      338463700*s14*s24 + 2497205568*s14*s34 - 800718416*s14 - 269173640*s23^2 + 554532532*s23*s24 -
      1063916678*s24*s34 + 3886284736) * hooop + (92192294*s12*s14 + 267473014*s12 +
      225238674*s13^2 - 320277724*s13 + 800718416*s14 - 554532532*s23*s24 - 517642096*s23*s34 +
      237175407*s23) * hppoo + (-225238674*s12*s13 + 267473014*s12 + 50118140*s13 + 312150696*s14 +
      269173640*s23^2 - 536087314*s23*s24 - 517642096*s23*s34 + 1063916678*s24*s34) * hpopo +
      (181075311*s12 + 158007130*s13*s14 + 50118140*s13 + 800718416*s14 + 269173640*s23^2 -
      554532532*s23*s24 - 22574193*s23*s34 - 134586820*s24^2 + 1063916678*s24*s34) * hpoop +
      (-158007130*s13*s14) * hpoom + (225238674*s12*s13) * hpomo + (-92192294*s12*s14 -
      225238674*s13^2 - 237175407*s23) * hpmoo + (160270392*s12*s24 - 388889180*s12*s34 +
      267473014*s12 - 934372890*s13*s24 + 1289843876*s13*s34 + 400512584*s14*s23 +
      203708668*s14*s24 - 2497205568*s14*s34 - 517642096*s23*s34) * hoppo + (-136869458*s12*s23 +
      160270392*s12*s24 - 165060508*s12*s34 - 368334352*s13*s24 + 26922351*s13*s34 -
      231899718*s14*s23 - 602951532*s14*s24 - 2497205568*s14*s34 + 800718416*s14 -
      554532532*s23*s24) * hopop + (165060508*s12*s34 + 368334352*s13*s24 + 231899718*s14*s23) *
      hopom + (-1289843876*s13*s34 - 203708668*s14*s24) * hopmo + (-838679148*s12*s23 +
      160270392*s12*s24 - 90190007*s12*s34 - 1000649022*s13*s24 + 1264057040*s13*s34 +
      50118140*s13 + 1165532714*s14*s23 - 169231850*s14*s24 - 2497205568*s14*s34 + 269173640*s23^2 +
      1063916678*s24*s34) * hoopp + (838679148*s12*s23 - 1264057040*s13*s34 + 169231850*s14*s24) *
      hoopm + (90190007*s12*s34 + 1000649022*s13*s24 - 1165532714*s14*s23) * hoomp +
      (388889180*s12*s34 + 934372890*s13*s24 - 400512584*s14*s23) * hompo + (136869458*s12*s23 -
      26922351*s13*s34 + 602951532*s14*s24) * homop + (320277724*s13) * hmpoo + (-312150696*s14 +
      536087314*s23*s24) * hmopo + (-181075311*s12 + 22574193*s23*s34 + 134586820*s24^2) * hmoop +
      (-267473014*s12 + 517642096*s23*s34) * hpppo + (-800718416*s14 + 554532532*s23*s24) * hppop +
      (-50118140*s13 - 269173640*s23^2 - 1063916678*s24*s34) * hpopp + (-160270392*s12*s24 +
      2497205568*s14*s34) * hoppp
  norm_num at hd

/-- No chart carries a graph on which `C6` vanishes. -/
theorem no_chart (S : Fin 4 → Bool) (s : Fin 4 → Fin 4 → ℂ) (hs : ∀ i k, s i k = -s k i)
    (h : ∀ a : Fin 4 → ℂ, C6 (pt S s a) = 0) : False := by
  have d0 : s 0 0 = 0 := by linear_combination (1 / 2 : ℂ) * hs 0 0
  have d1 : s 1 1 = 0 := by linear_combination (1 / 2 : ℂ) * hs 1 1
  have d2 : s 2 2 = 0 := by linear_combination (1 / 2 : ℂ) * hs 2 2
  have d3 : s 3 3 = 0 := by linear_combination (1 / 2 : ℂ) * hs 3 3
  have e10 := hs 1 0
  have e20 := hs 2 0
  have e30 := hs 3 0
  have e21 := hs 2 1
  have e31 := hs 3 1
  have e32 := hs 3 2
  rcases h0 : S 0 with _ | _ <;> rcases h1 : S 1 with _ | _ <;> rcases h2 : S 2 with _ | _ <;>
    rcases h3 : S 3 with _ | _
  · exact kern_0000 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_0001 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_0010 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_0011 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_0100 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_0101 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_0110 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_0111 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1000 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1001 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1010 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1011 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1100 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1101 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1110 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha
  · exact kern_1111 (s 0 1) (s 0 2) (s 0 3) (s 1 2) (s 1 3) (s 2 3) fun a1 a2 a3 a4 => by
      have ha := h ![a1, a2, a3, a4]
      simp [C6, pt, h0, h1, h2, h3, Fin.sum_univ_four, mq, d0, d1, d2, d3, e10, e20, e30, e21, e31,
        e32] at ha
      simp only [c6] at ha ⊢
      linear_combination ha

/-- A space of coordinate vectors on which `C6` vanishes has dimension at most three. -/
theorem finrank_le_three (L : Submodule ℂ E) (h : ∀ x ∈ L, C6 x = 0) :
    Module.finrank ℂ L ≤ 3 := by
  by_contra hcon
  have hiso : ∀ x ∈ L, ∀ y ∈ L, bil x y = 0 := fun x hx y hy => bil_eq_zero L h x y hx hy
  obtain ⟨S, hS⟩ := exists_chart L hiso
  let Φ : L →ₗ[ℂ] (Fin 4 → ℂ) :=
    { toFun := fun x i => x.1 (i, S i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦ : ∀ (x : L) (i : Fin 4), Φ x i = x.1 (i, S i) := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : x.1 ∈ L ⊓ zs S := ⟨x.2, fun i => congrFun hx i⟩
    rw [hS] at hx0
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 hx0)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have h44 : Module.finrank ℂ (Fin 4 → ℂ) = 4 := by simp
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).1 hinj
  choose v hv using fun j : Fin 4 => hsurj (Pi.single j 1)
  have hv' : ∀ j i, (v j).1 (i, S i) = if i = j then 1 else 0 := by
    intro j i
    rw [← hΦ, hv, Pi.single_apply]
  have hskew : ∀ i k, mq i * (v k).1 (i, !S i) = -(mq k * (v i).1 (k, !S k)) := by
    intro i k
    have hB := hiso _ (v i).2 _ (v k).2
    rw [bil_chart S] at hB
    simp only [hv', ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, mul_add,
      sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at hB
    linear_combination hB
  refine no_chart S (fun i k => mq i * (v k).1 (i, !S i)) hskew fun a => ?_
  have hmem : (∑ j, a j • (v j).1) ∈ L := L.sum_mem fun j _ => L.smul_mem _ (v j).2
  have hpt : pt S (fun i k => mq i * (v k).1 (i, !S i)) a = ∑ j, a j • (v j).1 := by
    funext ⟨i, b⟩
    simp only [pt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hbS : b = S i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hbS), hbS]
      simp [hv']
    · have hb' : b = !S i := by
        cases b <;> cases hS : S i <;> simp_all
      rw [ite_eq_right_of_eq_false _ _ (eq_false hbS), hb', div_eq_iff (mq_ne_zero i),
        Finset.sum_mul]
      exact sum_congr rfl fun k _ => by ring
  rw [hpt]
  exact h _ hmem

/-- A primitive cube root of unity. -/
theorem exists_omega : ∃ w : ℂ, w ^ 2 + w + 1 = 0 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  exact ⟨(-1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2, by
    linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * hI - h3) / 4⟩

/-- On a space where the permanent stays `6` along the all ones matrix, the entry sum
vanishes. -/
theorem sum_eq_zero (L : Submodule ℂ (Fin 3 × Fin 3 → ℂ))
    (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 3) = 6)
    (t : Fin 3 × Fin 3 → ℂ) (ht : t ∈ L) : ∑ q, t q = 0 := by
  have h1 := h _ ht
  have h2 := h _ (L.neg_mem ht)
  have h3 := h _ (L.smul_mem 2 ht)
  have h4 := h _ (L.smul_mem (-2) ht)
  simp only [PEqualNP.Gct.MethodCeiling.eval_permPoly, permanent_three, Matrix.of_apply,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
  linear_combination (8 * (h1 - h2) - (h3 - h4)) / 24

/-- Level spaces at `n = 3` have dimension at most three. -/
theorem level_three_le : ∀ L : Submodule ℂ (Fin 3 × Fin 3 → ℂ),
    (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 3) = 6) →
      Module.finrank ℂ L ≤ 3 := by
  intro L h
  obtain ⟨w, hw⟩ := exists_omega
  have hle : L ≤ LinearMap.range (fmap w) := fun t ht =>
    ⟨_, (fmap_mk8 w _ _ _ _ _ _ _ _).trans (fm_inv w hw t (sum_eq_zero L h t ht))⟩
  have h1 : (L.comap (fmap w)).map (fmap w) = L := Submodule.map_comap_eq_of_le hle
  have h2 := Submodule.finrank_map_le (fmap w) (L.comap (fmap w))
  have h3 := finrank_le_three (L.comap (fmap w)) fun x hx => by
    have hx' := h _ (Submodule.mem_comap.1 hx)
    rw [fmap_apply, perm_fm w hw] at hx'
    unfold C6
    linear_combination hx' / 3
  rw [h1] at h2
  omega

end PEqualNP.Gct.Helpers.LevelThree
