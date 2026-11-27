import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
namespace PEqualNP.Outside.L_gct_234
namespace SparseCubes
open Polynomial
open scoped BigOperators

noncomputable section


def euler (z : ℝ) (P : ℝ[X]) : ℝ[X] := X * derivative P - C z * P

def moment (z r : ℝ) : ℕ → ℝ[X] → ℝ
  | 0, P => P.eval r
  | n+1, P => moment z r n (euler z P)

theorem euler_add (z : ℝ) (P Q : ℝ[X]) : euler z (P+Q) = euler z P + euler z Q := by
  simp only [euler, map_add, mul_add]
  ring

theorem euler_C_mul (z t : ℝ) (P : ℝ[X]) : euler z (C t * P) = C t * euler z P := by
  simp only [euler, derivative_C_mul]
  ring

theorem moment_add (z r : ℝ) (n : ℕ) (P Q : ℝ[X]) :
    moment z r n (P+Q) = moment z r n P + moment z r n Q := by
  induction n generalizing P Q with
  | zero => simp [moment]
  | succ n ih => simp only [moment, euler_add, ih]

theorem moment_C_mul (z r : ℝ) (n : ℕ) (t : ℝ) (P : ℝ[X]) :
    moment z r n (C t * P) = t * moment z r n P := by
  induction n generalizing P with
  | zero => simp [moment]
  | succ n ih => simp only [moment, euler_C_mul, ih]

theorem moment_zero (z r : ℝ) (n : ℕ) : moment z r n 0 = 0 := by
  simpa using moment_C_mul z r n 0 0

theorem moment_sum {ι : Type*} (z r : ℝ) (n : ℕ) (I : Finset ι) (P : ι → ℝ[X]) :
    moment z r n (∑ i ∈ I, P i) = ∑ i ∈ I, moment z r n (P i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [moment_zero]
  | insert i I hi ih => simp [hi, moment_add, ih]

theorem euler_term (z t : ℝ) (k : ℕ) :
    euler z (C t * X^k) = C ((k:ℝ)-z) * (C t * X^k) := by
  cases k with
  | zero => simp [euler]
  | succ k =>
    rw [euler, derivative_C_mul_X_pow]
    simp only [Nat.add_one_sub_one, pow_succ,
      Nat.cast_succ, map_sub, map_add, map_mul, map_one]
    ring

theorem moment_term (z r t : ℝ) (k n : ℕ) :
    moment z r n (C t * X^k) = t * r^k * ((k:ℝ)-z)^n := by
  induction n with
  | zero => simp [moment]
  | succ n ih => rw [moment, euler_term, moment_C_mul, ih, pow_succ]; ring

theorem moment_eq_zero_of_dvd {P : ℝ[X]} (z r : ℝ) (n : ℕ)
    (h : (X - C r)^(n+1) ∣ P) : moment z r n P = 0 := by
  induction n generalizing P with
  | zero =>
    have h' : X - C r ∣ P := by simpa using h
    simpa [moment, Polynomial.IsRoot] using (dvd_iff_isRoot.mp h')
  | succ n ih =>
    apply ih
    apply dvd_sub
    · apply dvd_mul_of_dvd_right
      simpa using pow_sub_one_dvd_derivative_of_pow_dvd h
    · apply dvd_mul_of_dvd_right
      exact (pow_dvd_pow (X - C r) (by omega : n+1 ≤ n+1+1)).trans h

theorem moment_eq_zero_of_lt_rootMultiplicity (z r : ℝ) (P : ℝ[X]) {n : ℕ}
    (h : n < P.rootMultiplicity r) : moment z r n P = 0 :=
  moment_eq_zero_of_dvd z r n
    ((pow_dvd_pow (X-C r) h).trans (P.pow_rootMultiplicity_dvd r))

theorem moment_eq_support_sum (z r : ℝ) (n : ℕ) (P : ℝ[X]) :
    moment z r n P = ∑ k ∈ P.support, P.coeff k * r^k * ((k:ℝ)-z)^n := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  simp only [moment_sum, moment_term]


theorem eq_zero_of_moments (z r : ℝ) (hr : r ≠ 0) (P : ℝ[X])
    (h : ∀ n < P.support.card, moment z r n P = 0) : P = 0 := by
  classical
  let e := P.support.equivFin.symm
  let f (i : Fin P.support.card) : ℝ := ((e i).1:ℝ) - z
  let v (i : Fin P.support.card) : ℝ := P.coeff (e i).1 * r^(e i).1
  have hf : Function.Injective f := by
    intro i j hij
    have hcast : ((e i).1 : ℝ) = ((e j).1 : ℝ) := sub_left_inj.mp hij
    apply e.injective
    apply Subtype.ext
    exact_mod_cast hcast
  have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf (by
    intro i
    have ha := h i i.isLt
    rw [moment_eq_support_sum, ← Finset.sum_attach] at ha
    rwa [show (∑ j, v j * f j ^ (i:ℕ)) = _ from
      Equiv.sum_comp e (fun k => P.coeff k.1 * r^k.1 * ((k.1:ℝ)-z)^(i:ℕ))])
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro k
  by_cases hk : k ∈ P.support
  · have he := congrFun hv (e.symm ⟨k,hk⟩)
    simpa [v, hr] using he
  · simpa using (Polynomial.notMem_support_iff.mp hk)

theorem rootMultiplicity_lt_support_card (r : ℝ) (hr : r ≠ 0) (P : ℝ[X]) (hP : P ≠ 0) :
    P.rootMultiplicity r < P.support.card := by
  by_contra! h
  exact hP (eq_zero_of_moments 0 r hr P (fun n hn =>
    moment_eq_zero_of_lt_rootMultiplicity 0 r P (lt_of_lt_of_le hn h)))

end
end SparseCubes

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

abbrev Arm := ℕ × ℕ × ℝ × ℝ
abbrev Arm.left (g : Arm) := g.1
abbrev Arm.right (g : Arm) := g.2.1
abbrev Arm.A (g : Arm) := g.2.2.1
abbrev Arm.B (g : Arm) := g.2.2.2

def Arm.poly (g : Arm) : ℝ[X] := C g.A * X^g.left + C g.B * X^g.right

theorem exists_arm_of_support_le_two (P : ℝ[X]) (h : P.support.card ≤ 2) :
    ∃ g : Arm, g.poly = P := by
  rcases (show P.support.card = 0 ∨ P.support.card = 1 ∨ P.support.card = 2 by omega) with h0|h1|h2
  · have hz : P = 0 := by simpa using h0
    exact ⟨⟨0,0,0,0⟩, by simp [Arm.poly,Arm.A,Arm.B,Arm.left,Arm.right, hz]⟩
  · obtain ⟨k,hk⟩ := Finset.card_eq_one.mp h1
    refine ⟨⟨k,0,P.coeff k,0⟩, ?_⟩
    simpa [Arm.poly,Arm.A,Arm.B,Arm.left,Arm.right,hk] using P.as_sum_support_C_mul_X_pow.symm
  · obtain ⟨k,l,hkl,hkl'⟩ := Finset.card_eq_two.mp h2
    refine ⟨⟨k,l,P.coeff k,P.coeff l⟩, ?_⟩
    simpa [Arm.poly,Arm.A,Arm.B,Arm.left,Arm.right,hkl',hkl] using P.as_sum_support_C_mul_X_pow.symm

theorem arm_cube (g : Arm) : g.poly^3 =
    C (g.A^3) * X^(g.left+g.left+g.left) +
    C (3*g.A^2*g.B) * X^(g.left+g.left+g.right) +
    C (3*g.A*g.B^2) * X^(g.left+g.right+g.right) +
    C (g.B^3) * X^(g.right+g.right+g.right) := by
  simp only [Arm.poly,Arm.A,Arm.B,Arm.left,Arm.right, pow_add, map_mul, map_pow, map_ofNat]
  ring


def cubeFour (A B a b : ℝ) (n : ℕ) : ℝ :=
    A^3 * (3*a)^n + 3*A^2*B*(2*a+b)^n + 3*A*B^2*(a+2*b)^n + B^3*(3*b)^n

def Arm.leftMass (g : Arm) (r : ℝ) : ℝ := g.A*r^g.left
def Arm.rightMass (g : Arm) (r : ℝ) : ℝ := g.B*r^g.right

theorem moment_arm_cube (g : Arm) (r t : ℝ) (n : ℕ) :
    moment (3*t) r n (g.poly^3) =
    cubeFour (g.leftMass r) (g.rightMass r) ((g.left:ℝ)-t) ((g.right:ℝ)-t) n := by
  rw [arm_cube]
  simp only [moment_add, moment_term]
  simp only [cubeFour, Arm.leftMass, Arm.rightMass, pow_add,
    Nat.cast_add]
  ring

theorem support_add_card_le (P Q : ℝ[X]) :
    (P+Q).support.card ≤ P.support.card + Q.support.card :=
  (Finset.card_le_card Polynomial.support_add).trans (Finset.card_union_le _ _)

theorem support_one_term (a : ℝ) (k : ℕ) : (C a * X^k).support.card ≤ 1 := by
  simpa using Finset.card_le_card (Polynomial.support_C_mul_X_pow_subset k a)

theorem support_cube_le_four (g : Arm) : (g.poly^3).support.card ≤ 4 := by
  rw [arm_cube]
  calc
    _ ≤ _ := support_add_card_le _ _
    _ ≤ _ := Nat.add_le_add_right (support_add_card_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (support_add_card_le _ _) _) _
    _ ≤ 4 := by
      have h := support_one_term
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h _ _) (h _ _)) (h _ _)) (h _ _)

theorem support_C_mul_card_le (a : ℝ) (P : ℝ[X]) : (C a*P).support.card ≤ P.support.card := by
  apply Finset.card_le_card
  intro k hk
  contrapose! hk
  apply Polynomial.notMem_support_iff.mpr
  rw [Polynomial.coeff_C_mul, Polynomial.notMem_support_iff.mp hk, mul_zero]

theorem support_small_cube (P : ℝ[X]) (h : P.support.card ≤ 1) : (P^3).support.card ≤ 1 := by
  rcases (show P.support.card = 0 ∨ P.support.card = 1 by omega) with h0|h1
  · have hz : P = 0 := by simpa using h0
    simp [hz]
  · obtain ⟨k,hk⟩ := Finset.card_eq_one.mp h1
    have hP : P = monomial k (P.coeff k) := by simpa [hk] using P.as_sum_support
    conv_lhs => rw [hP, monomial_pow]
    simpa using Finset.card_le_card (Polynomial.support_monomial_subset (k*3) (P.coeff k^3))


theorem bound_of_one_small_input (s : Fin 3 → ℝ) (g : Fin 3 → ℝ[X])
    (hg : ∀ i, (g i).support.card ≤ 2) (hs : ∃ i, (g i).support.card ≤ 1)
    (hP : (∑ i, C (s i) * g i ^ 3) ≠ 0) (r : ℝ) (hr : 0 < r) :
    rootMultiplicity r (∑ i, C (s i) * g i ^ 3) ≤ 9 := by
  have each (i : Fin 3) : (C (s i)*g i^3).support.card ≤ 4 := by
    obtain ⟨a,ha⟩ := exists_arm_of_support_le_two (g i) (hg i)
    exact (support_C_mul_card_le _ _).trans (ha ▸ support_cube_le_four a)
  obtain ⟨i,hi⟩ := hs
  have small := (support_C_mul_card_le (s i) (g i ^ 3)).trans (support_small_cube (g i) hi)
  have card : (∑ j, C (s j) * g j^3).support.card ≤ 9 := by
    rw [Fin.sum_univ_three]
    have hab := support_add_card_le (C (s 0)*g 0^3) (C (s 1)*g 1^3)
    have hall := support_add_card_le (C (s 0)*g 0^3+C (s 1)*g 1^3) (C (s 2)*g 2^3)
    have h0 := each 0
    have h1 := each 1
    have h2 := each 2
    fin_cases i <;> dsimp at small <;> omega
  exact (rootMultiplicity_lt_support_card r hr.ne' _ hP).le.trans card

end
end SparseCubes

namespace SparseCubes.Chart


def rawMoment (x v s : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 3*x
  | 2 => 9*x^2+3*v
  | 3 => 27*x^3+27*x*v+3*v*s
  | n+4 =>
    let t := 2*x+s
    let p := x^2+x*s-v
    let a := 3*t
    let o := 9*p
    let i := 2*t^2+p
    2*a*rawMoment x v s (n+3) - (a^2+o+i)*rawMoment x v s (n+2) +
      a*(o+i)*rawMoment x v s (n+1) - o*i*rawMoment x v s n

end SparseCubes.Chart

namespace SparseCubes
noncomputable section


theorem cubeFour_step (A B a b : ℝ) (n : ℕ) :
    cubeFour A B a b (n+4) =
      2*(3*(a+b))*cubeFour A B a b (n+3) -
      ((3*(a+b))^2 + 9*(a*b) + (2*(a+b)^2+a*b))*cubeFour A B a b (n+2) +
      (3*(a+b))*(9*(a*b)+(2*(a+b)^2+a*b))*cubeFour A B a b (n+1) -
      (9*(a*b))*(2*(a+b)^2+a*b)*cubeFour A B a b n := by
  simp only [cubeFour, pow_add]
  ring


theorem normalized_cubeFour (A a b : ℝ) (n : ℕ) :
    cubeFour A (1-A) a b n = Chart.rawMoment (A*a+(1-A)*b)
      (A*(1-A)*(a-b)^2) (a+b-2*(A*a+(1-A)*b)) n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => simp only [cubeFour, Chart.rawMoment]; ring
    | n+4 =>
      rw [cubeFour_step, Chart.rawMoment]
      simp only [show 2*(A*a+(1-A)*b)+(a+b-2*(A*a+(1-A)*b)) = a+b by ring,
        show (A*a+(1-A)*b)^2 + (A*a+(1-A)*b)*(a+b-2*(A*a+(1-A)*b)) -
          A*(1-A)*(a-b)^2 = a*b by ring]
      rw [ih (n+3) (by omega), ih (n+2) (by omega), ih (n+1) (by omega), ih n (by omega)]

theorem cubeFour_scale (k A B a b : ℝ) (n : ℕ) :
    cubeFour (k*A) (k*B) a b n = k^3*cubeFour A B a b n := by
  unfold cubeFour
  ring


def Arm.variance (g : Arm) (r : ℝ) : ℝ :=
  let t := g.leftMass r / (g.leftMass r + g.rightMass r)
  t*(1-t)*((g.left:ℝ)-g.right)^2

def Arm.mean (g : Arm) (r : ℝ) : ℝ :=
  let t := g.leftMass r / (g.leftMass r + g.rightMass r)
  t*g.left+(1-t)*g.right

def Arm.skew (g : Arm) (r : ℝ) : ℝ := (g.left:ℝ)+g.right-2*g.mean r

theorem arm_normalized (g : Arm) (r t : ℝ) (n : ℕ)
    (hne : g.leftMass r + g.rightMass r ≠ 0) :
    moment (3*t) r n (g.poly^3) =
      (g.leftMass r + g.rightMass r)^3 *
      Chart.rawMoment (g.mean r-t) (g.variance r) (g.skew r) n := by
  let L := g.leftMass r
  let R := g.rightMass r
  let a := L/(L+R)
  have hL : (L+R)*a=L := by dsimp [a,L,R]; field_simp
  have hR : (L+R)*(1-a)=R := by linear_combination -hL
  rw [moment_arm_cube]
  calc
    _ = cubeFour ((L+R)*a) ((L+R)*(1-a)) ((g.left:ℝ)-t) ((g.right:ℝ)-t) n := by rw [hL,hR]
    _ = _ := by
      rw [cubeFour_scale, normalized_cubeFour]
      apply congrArg ((L+R)^3 * ·)
      congr 1 <;> dsimp [Arm.mean, Arm.skew, Arm.variance, a, L, R] <;> ring

end
end SparseCubes

namespace SparseCubes

theorem mixtureWeights (u v w : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hs : u+v+w=0) :
    ∃ p : ℝ, p ≠ 0 ∧ 1-p ≠ 0 ∧
      ∀ a b c : ℝ, u*a+v*b+w*c = 0 → p*a+(1-p)*b=c := by
  refine ⟨-u/w, div_ne_zero (neg_ne_zero.mpr hu) hw, ?_, ?_⟩
  · intro h
    field_simp at h
    apply hv
    linarith
  · intro a b c h
    field_simp
    linear_combination -h + b*hs


theorem three_nodes (m x : Fin 3 → ℝ) (hm : ∀ i, m i ≠ 0)
    (hm0 : m 0+m 1+m 2=0) (hm1 : m 0*x 0+m 1*x 1+m 2*x 2=0) :
    (∀ i, x i = x 0) ∨ Function.Injective x := by
  have h01 (h : x 0=x 1) : x 2=x 0 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (hm 2)
    rw [← h] at hm1
    linear_combination hm1 - x 0*hm0
  have h02 (h : x 0=x 2) : x 1=x 0 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (hm 1)
    rw [← h] at hm1
    linear_combination hm1 - x 0*hm0
  have h12 (h : x 1=x 2) : x 0=x 1 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (hm 0)
    rw [← h] at hm1
    linear_combination hm1 - x 1*hm0
  by_cases a : x 0=x 1
  · exact Or.inl (by intro i; fin_cases i <;> first | rfl | exact a.symm | exact h01 a)
  by_cases b : x 0=x 2
  · exact (a (h02 b).symm).elim
  by_cases c : x 1=x 2
  · exact (a (h12 c)).elim
  right
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact (a hij).elim | exact (a hij.symm).elim | exact (b hij).elim | exact (b hij.symm).elim | exact (c hij).elim | exact (c hij.symm).elim

end SparseCubes

namespace SparseCubes


def centeredCubeMoment : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, _ => 0
  | 2, _, v => 3*v
  | 3, s, v => 3*s*v
  | 4, s, v => 3*v*(s^2 + 7*v)
  | 5, s, v => 3*s*v*(s^2 + 22*v)
  | 6, s, v => 3*v*(s^4 + 53*s^2*v + 61*v^2)
  | 7, s, v => 3*s*v*(s^4 + 116*s^2*v + 367*v^2)
  | 8, s, v => 3*v*(s^6 + 243*s^4*v + 1518*s^2*v^2 + 547*v^3)
  | 9, s, v => 3*s*v*(s^6 + 498*s^4*v + 5394*s^2*v^2 + 4924*v^3)
  | _, _, _ => 0


noncomputable def uniformCubeMoment : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, m, _ => m
  | 2, m, v => m^2+v
  | 3, m, v => m^3+3*m*v
  | 4, m, v => m^4+6*m^2*v+13*v^2/5
  | 5, m, v => m^5+10*m^3*v+13*m*v^2
  | 6, m, v => m^6+15*m^4*v+39*m^2*v^2+205*v^3/21
  | _, _, _ => 0

set_option maxHeartbeats 4000000 in

theorem oneVanish_excludes (h d v m b : ℝ) (hd : d ≠ 0) (hv : v ≠ 0)
    (H : ∀ n : ℕ, n ≤ 6 → centeredCubeMoment (n+3) (h+d) v -
      centeredCubeMoment (n+3) (h-d) v =
      v*d*((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*uniformCubeMoment n m b) : False := by
  have eqn (n : ℕ) (hn : n ≤ 6) := H n hn
  have H1 := eqn 1 (by decide)
  have H2 := eqn 2 (by decide)
  have H3 := eqn 3 (by decide)
  have H4 := eqn 4 (by decide)
  have H6 := eqn 6 (by decide)
  norm_num [centeredCubeMoment,uniformCubeMoment] at H1 H2 H3 H4 H6
  have recover {x : ℝ} (hx : v*d*x=0) : x=0 :=
    (mul_eq_zero.mp hx).resolve_left (mul_ne_zero hv hd)
  have hm : m=h/2 := by
    apply sub_eq_zero.mp
    apply recover
    linear_combination -H1/24
  subst m
  have hb : b=(d^2+3*h^2+22*v)/10-(h/2)^2 := by
    apply sub_eq_zero.mp
    apply recover
    linear_combination -H2/60
  subst b
  have h3 : h*(d^2+40*v)=0 := by apply recover; linear_combination H3/6
  have hh : h=0 := by
    rcases mul_eq_zero.mp h3 with h0|h0
    · exact h0
    · have vv : v= -d^2/40 := by linarith
      subst v
      have h4 : 18549*d^4+14720*d^2*h^2+400*h^4=0 := by
        apply recover
        linear_combination -(5000:ℝ)/3 * H4
      have hpos : 0 < 18549*d^4+14720*d^2*h^2+400*h^4 := by
        have hd4 : 0 < d^4 := by positivity
        positivity
      linarith
  subst h
  let u := v/d^2
  have hu : v=u*d^2 := by dsimp [u]; field_simp
  rw [hu] at H4 H6
  have dropPower (n : ℕ) (z : ℝ) (hz : v*d*d^n*z=0) : z=0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero hv hd) (pow_ne_zero _ hd))
  have ce : 816*u^2-844*u-1=0 := by
    apply dropPower 4
    rw [hu]
    linear_combination -(50:ℝ)/27 * H4
  have cf : -1-2466*u-23352*u^2+21152*u^3=0 := by
    apply dropPower 6
    rw [hu]
    linear_combination -(25:ℝ)/27 * H6
  have impossible : (1:ℝ)=0 := by
    linear_combination ((272665144*u^2-301217806*u-31440989)/20553750)*ce +
      ((10887239-10518852*u)/20553750)*cf
  norm_num at impossible

end SparseCubes


namespace SparseCubes


theorem uniformCubeMatch_affine (p m₁ m₂ m₃ v₁ v₂ v₃ a b : ℝ)
    (H : ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n m₁ v₁ +
       (1-p)*uniformCubeMoment n m₂ v₂ = uniformCubeMoment n m₃ v₃) :
    ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n (a*m₁+b) (a^2*v₁) +
       (1-p)*uniformCubeMoment n (a*m₂+b) (a^2*v₂) =
       uniformCubeMoment n (a*m₃+b) (a^2*v₃) := by
  have h1 := H 1 (by decide)
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  have h4 := H 4 (by decide)
  have h5 := H 5 (by decide)
  have h6 := H 6 (by decide)
  simp [uniformCubeMoment] at h1 h2 h3 h4 h5 h6
  intro n hn
  interval_cases n <;> simp only [uniformCubeMoment]
  · ring
  · linear_combination 1*a^1*b^0*h1
  · linear_combination 2*a^1*b^1*h1 + 1*a^2*b^0*h2
  · linear_combination 3*a^1*b^2*h1 + 3*a^2*b^1*h2 + 1*a^3*b^0*h3
  · linear_combination 4*a^1*b^3*h1 + 6*a^2*b^2*h2 + 4*a^3*b^1*h3 + 1*a^4*b^0*h4
  · linear_combination 5*a^1*b^4*h1 + 10*a^2*b^3*h2 + 10*a^3*b^2*h3 + 5*a^4*b^1*h4 + 1*a^5*b^0*h5
  · linear_combination 6*a^1*b^5*h1 + 15*a^2*b^4*h2 + 20*a^3*b^3*h3 + 15*a^4*b^2*h4 + 6*a^5*b^1*h5 + 1*a^6*b^0*h6

private theorem uniform_normalized_excludes (p v₁ v₂ v₃ : ℝ) (hp : p ≠ 0) (hq : 1-p ≠ 0)
    (H : ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n (1-p) v₁ +
       (1-p)*uniformCubeMoment n (-p) v₂ = uniformCubeMoment n 0 v₃) : False := by
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  have h4 := H 4 (by decide)
  have h5 := H 5 (by decide)
  have h6 := H 6 (by decide)
  norm_num [uniformCubeMoment] at h2 h3 h4 h5 h6
  have cancel {z : ℝ} (e : p*(1-p)*z=0) : z=0 :=
    (mul_eq_zero.mp e).resolve_left (mul_ne_zero hp hq)
  have v1e : v₁=v₂+(2*p-1)/3 := by
    apply sub_eq_zero.mp
    apply cancel
    linear_combination h3/3
  subst v₁
  have v3e : v₃ = v₂ + p*(2*p-1)/3+p*(1-p) := by linear_combination -h2
  subst v₃
  have v2e : v₂=(8*p^2-11*p+8)/9 := by
    apply sub_eq_zero.mp
    apply cancel
    linear_combination (5:ℝ)/4*h4
  subst v₂
  have prodzero : (p-2)*(p+1)*(2*p-1)=0 := by
    apply cancel
    linear_combination (27:ℝ)/4*h5
  rcases mul_eq_zero.mp prodzero with hh | hh
  · rcases mul_eq_zero.mp hh with hh | hh
    · have pp : p=2 := by linarith
      rw [pp] at h6; norm_num at h6
    · have pp : p= -1 := by linarith
      rw [pp] at h6; norm_num at h6
  · have pp : p=1/2 := by linarith
    rw [pp] at h6; norm_num at h6


theorem threeVanish_mixture (p m₁ m₂ m₃ v₁ v₂ v₃ : ℝ) (hp : p ≠ 0) (hq : 1-p ≠ 0)
    (H : ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n m₁ v₁ +
       (1-p)*uniformCubeMoment n m₂ v₂ = uniformCubeMoment n m₃ v₃) :
    m₁=m₃ ∧ m₂=m₃ ∧ v₁=v₃ ∧ v₂=v₃ := by
  have h1 := H 1 (by decide)
  simp [uniformCubeMoment] at h1
  by_cases he : m₁=m₂
  · subst m₁
    have hm : m₂=m₃ := by linear_combination h1
    rw [← hm] at H ⊢
    have U := uniformCubeMatch_affine p m₂ m₂ m₂ v₁ v₂ v₃ 1 (-m₂) H
    have h2 := U 2 (by decide)
    have h4 := U 4 (by decide)
    norm_num [uniformCubeMoment] at h2 h4
    have ve : v₃=p*v₁+(1-p)*v₂ := by linear_combination -h2
    subst v₃
    have sq0 : p*(1-p)*(v₁-v₂)^2=0 := by linear_combination (5:ℝ)/13*h4
    have vv : v₁=v₂ := by
      have sq := (mul_eq_zero.mp sq0).resolve_left (mul_ne_zero hp hq)
      nlinarith [sq_nonneg (v₁-v₂)]
    subst v₁
    exact ⟨rfl,rfl,by ring,by ring⟩
  · have hd : m₁-m₂≠0 := sub_ne_zero.mpr he
    let a := (m₁-m₂)⁻¹
    have am₁ : a*m₁ + -(a*m₃) = 1-p := by dsimp [a]; field_simp; linear_combination h1
    have am₂ : a*m₂ + -(a*m₃) = -p := by dsimp [a]; field_simp; linear_combination h1
    have U := uniformCubeMatch_affine p m₁ m₂ m₃ v₁ v₂ v₃ a (-(a*m₃)) H
    simp only [am₁,am₂,add_neg_cancel] at U
    exact (uniform_normalized_excludes p _ _ _ hp hq U).elim

end SparseCubes


namespace SparseCubes

private def sixthObstruction (p z : ℝ) :=
  783*p^2*z^2 - 783*p^2*z + 196*p^2 + 782*p*z^3 - 1956*p*z^2 +
  782*p*z + 196*z^4 - 783*z^3 + 783*z^2

private theorem sixthObstruction_ne (p z : ℝ) (hz : z≠0) (hz' : 1-z≠0) :
    sixthObstruction p z ≠ 0 := by
  intro he
  have hi : 4*(783*z^2-783*z+196)*sixthObstruction p z =
      (2*(783*z^2-783*z+196)*p + 782*z^3-1956*z^2+782*z)^2 +
      2348*z^2*(1-z)^2*(z^2-z+1) := by unfold sixthObstruction; ring
  have hpos : 0 < z^2-z+1 := by nlinarith [sq_nonneg (z-1/2)]
  have hterm : 0 < 2348*z^2*(1-z)^2*(z^2-z+1) := by positivity
  rw [he, mul_zero] at hi
  nlinarith [sq_nonneg (2*(783*z^2-783*z+196)*p + 782*z^3-1956*z^2+782*z)]

set_option maxHeartbeats 8000000 in
private theorem equalMean_normalized_excludes (p z t V : ℝ)
    (hp : p≠0) (hq : 1-p≠0) (hz : z≠0) (hz' : 1-z≠0) (hv : V≠0)
    (H : ∀ n : ℕ, n≤6 → p*centeredCubeMoment n (t+1-z) (V*z/p) +
      (1-p)*centeredCubeMoment n (t-z) (V*(1-z)/(1-p)) = centeredCubeMoment n t V) : False := by
  have zero (n : ℕ) (hn : n≤6) := sub_eq_zero.mpr (H n hn)
  have h4 : p*(1-p)*z*(1-z)+7*V*(z-p)^2=0 := by
    calc
      _ = (p*(1-p)/(3*V)) * (p*centeredCubeMoment 4 (t+1-z) (V*z/p) +
        (1-p)*centeredCubeMoment 4 (t-z) (V*(1-z)/(1-p))-centeredCubeMoment 4 t V) := by
          simp only [centeredCubeMoment]; field_simp; ring
      _ = 0 := by rw [zero 4 (by decide),mul_zero]
  have diff : z-p≠0 := by
    intro he
    rw [he] at h4
    have hnon : p*(1-p)*z*(1-z)≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hp hq) hz) hz'
    exact hnon (by simpa using h4)
  have vval : V= -(p*(1-p)*z*(1-z))/(7*(z-p)^2) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ diff))).2
    linear_combination h4
  have h5 : p*t+14*p*z-7*p-t*z+8*z^2-15*z=0 := by
    calc
      _ = (7*(z-p)/(3*V*z*(1-z))) * (p*centeredCubeMoment 5 (t+1-z) (V*z/p) +
        (1-p)*centeredCubeMoment 5 (t-z) (V*(1-z)/(1-p))-centeredCubeMoment 5 t V) := by
          rw [vval]; simp only [centeredCubeMoment]; field_simp [hp,hq,hz,hz',diff]; ring
      _ = 0 := by rw [zero 5 (by decide),mul_zero]
  have tval : t=(14*p*z-7*p+8*z^2-15*z)/(z-p) := by
    apply (eq_div_iff diff).2
    linear_combination -h5
  apply sixthObstruction_ne p z hz hz'
  calc
    _ = (-49*(z-p)^2/(36*V*z*(1-z))) * (p*centeredCubeMoment 6 (t+1-z) (V*z/p) +
       (1-p)*centeredCubeMoment 6 (t-z) (V*(1-z)/(1-p))-centeredCubeMoment 6 t V) := by
        rw [vval,tval]; simp only [centeredCubeMoment,sixthObstruction]
        field_simp [hp,hq,hz,hz',diff]; ring
    _ = 0 := by rw [zero 6 (by decide),mul_zero]

theorem centeredCubeMoment_scale (n : ℕ) (hn : n≤6) (s v a : ℝ) :
    centeredCubeMoment n (a*s) (a^2*v) = a^n*centeredCubeMoment n s v := by
  interval_cases n <;> simp only [centeredCubeMoment] <;> ring

set_option maxHeartbeats 2000000 in

theorem equalMean_mixture (p s₁ s₂ s₃ v₁ v₂ v₃ : ℝ)
    (hp : p≠0) (hq : 1-p≠0) (hv1 : v₁≠0) (hv2 : v₂≠0) (hv3 : v₃≠0)
    (H : ∀ n : ℕ, n≤6 → p*centeredCubeMoment n s₁ v₁ +
      (1-p)*centeredCubeMoment n s₂ v₂ = centeredCubeMoment n s₃ v₃) :
    s₁=s₃ ∧ s₂=s₃ ∧ v₁=v₃ ∧ v₂=v₃ := by
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  have h4 := H 4 (by decide)
  simp only [centeredCubeMoment] at h2 h3 h4
  have v3 : v₃=p*v₁+(1-p)*v₂ := by linear_combination -h2/3
  by_cases he : s₁=s₂
  · subst s₁
    have hs : (s₂-s₃)*v₃=0 := by linear_combination h3/3-s₂*h2/3
    have same := sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hv3)
    subst s₂
    rw [v3] at h4
    have sv : p*(1-p)*(v₁-v₂)^2=0 := by linear_combination h4/21
    have dif := (mul_eq_zero.mp sv).resolve_left (mul_ne_zero hp hq)
    have vv : v₁=v₂ := by nlinarith [sq_nonneg (v₁-v₂)]
    subst v₁
    have vv3 : v₂=v₃ := by linear_combination -v3
    exact ⟨rfl,rfl,vv3,vv3⟩
  · have hd : s₁-s₂≠0 := sub_ne_zero.mpr he
    let a := (s₁-s₂)⁻¹
    let z := p*v₁/v₃
    let t := a*s₃
    let V := a^2*v₃
    have ha : a≠0 := inv_ne_zero hd
    have hz : z≠0 := div_ne_zero (mul_ne_zero hp hv1) hv3
    have wz : 1-z=(1-p)*v₂/v₃ := by dsimp [z]; field_simp; linear_combination v3
    have hz' : 1-z≠0 := by rw [wz]; exact div_ne_zero (mul_ne_zero hq hv2) hv3
    have hV : V≠0 := mul_ne_zero (pow_ne_zero _ ha) hv3
    have am1 : t+1-z=a*s₁ := by
      dsimp [t,a,z]; field_simp; linear_combination -h3/3 + s₂*h2/3
    have am2 : t-z=a*s₂ := by
      dsimp [t,a,z]; field_simp; linear_combination -h3/3 + s₂*h2/3
    have av1 : V*z/p=a^2*v₁ := by dsimp [V,z]; field_simp
    have av2 : V*(1-z)/(1-p)=a^2*v₂ := by rw [wz]; dsimp [V]; field_simp
    apply (equalMean_normalized_excludes p z t V hp hq hz hz' hV ?_).elim
    intro n hn
    rw [am1, am2, av1, av2]
    change _ = centeredCubeMoment n (a*s₃) (a^2*v₃)
    rw [centeredCubeMoment_scale n hn, centeredCubeMoment_scale n hn, centeredCubeMoment_scale n hn]
    linear_combination a^n * H n hn

end SparseCubes

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

def Arm.value (g : Arm) (r : ℝ) : ℝ := g.leftMass r + g.rightMass r
def Arm.Genuine (g : Arm) : Prop := g.A ≠ 0 ∧ g.B ≠ 0 ∧ g.left ≠ g.right

theorem genuine_arm (P : ℝ[X]) (h : P.support.card = 2) :
    ∃ g : Arm, g.poly = P ∧ g.Genuine := by
  obtain ⟨k,l,hkl,hs⟩ := Finset.card_eq_two.mp h
  refine ⟨⟨k,l,P.coeff k,P.coeff l⟩, ?_, ?_⟩
  · simpa [Arm.poly,hs,hkl] using P.as_sum_support_C_mul_X_pow.symm
  · exact ⟨Polynomial.mem_support_iff.mp (by simp [hs]),
      Polynomial.mem_support_iff.mp (by simp [hs]), hkl⟩

theorem Arm.variance_ne (g : Arm) (r : ℝ) (hr : r ≠ 0) (hg : g.Genuine)
    (hval : g.value r ≠ 0) : g.variance r ≠ 0 := by
  have hL : g.leftMass r ≠ 0 := mul_ne_zero hg.1 (pow_ne_zero _ hr)
  have hR : g.rightMass r ≠ 0 := mul_ne_zero hg.2.1 (pow_ne_zero _ hr)
  have hn : (g.left:ℝ) ≠ g.right := by exact_mod_cast hg.2.2
  have hsum : g.leftMass r + g.rightMass r ≠ 0 := hval
  have ha : 1 - g.leftMass r/(g.leftMass r+g.rightMass r) ≠ 0 := by
    rw [← div_self hsum, ← sub_div]
    simpa using div_ne_zero hR hsum
  exact mul_ne_zero (mul_ne_zero (div_ne_zero hL hsum) ha) (pow_ne_zero _ (sub_ne_zero.mpr hn))

def total (s : Fin 3 → ℝ) (g : Fin 3 → Arm) : ℝ[X] :=
    ∑ i, C (s i) * (g i).poly^3

def LowMoments (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) : Prop :=
    ∀ n < 10, ∀ t : ℝ, (∑ i, s i * moment (3*t) r n ((g i).poly^3)) = 0

theorem low_of_ten (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ)
    (h : 10 ≤ (total s g).rootMultiplicity r) : LowMoments s g r := by
  intro n hn t
  simpa only [total, moment_sum, moment_C_mul] using
    moment_eq_zero_of_lt_rootMultiplicity (3*t) r (total s g) (lt_of_lt_of_le hn h)

theorem low_perm (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (h : LowMoments s g r)
    (e : Equiv.Perm (Fin 3)) : LowMoments (s ∘ e) (g ∘ e) r := by
  intro n hn t
  exact (Equiv.sum_comp e (fun i => s i * moment (3*t) r n ((g i).poly^3))).trans (h n hn t)

theorem total_perm (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (e : Equiv.Perm (Fin 3)) :
    total (s ∘ e) (g ∘ e) = total s g :=
  Equiv.sum_comp e (fun i => C (s i) * (g i).poly^3)


theorem normalized_low (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ)
    (hn : ∀ i, (g i).value r ≠ 0) (h : LowMoments s g r) (t : ℝ) (n : ℕ) (hlt : n < 10) :
    (∑ i, (s i * ((g i).value r)^3) *
      Chart.rawMoment ((g i).mean r-t) ((g i).variance r) ((g i).skew r) n) = 0 := by
  convert h n hlt t using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [arm_normalized _ _ _ _ (hn i)]
  simp only [Arm.value, mul_assoc]

theorem centered_raw (s v : ℝ) (n : ℕ) (hn : n ≤ 6) :
    Chart.rawMoment 0 v s n = centeredCubeMoment n s v := by
  interval_cases n <;> norm_num [Chart.rawMoment, centeredCubeMoment] <;> ring


theorem same_mean_zero (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hn : ∀ i, (g i).value r ≠ 0)
    (he : ∀ i, (g i).mean r = (g 0).mean r) (hl : LowMoments s g r) : total s g = 0 := by
  let m := fun i => s i * ((g i).value r)^3
  let V := fun i => (g i).variance r
  let S := fun i => (g i).skew r
  have hm (i) : m i ≠ 0 := mul_ne_zero (hs i) (pow_ne_zero _ (hn i))
  have hv (i) := Arm.variance_ne (g i) r hr (hg i) (hn i)
  have hraw (n : ℕ) (hlt : n < 10) :
      m 0 * Chart.rawMoment 0 (V 0) (S 0) n + m 1 * Chart.rawMoment 0 (V 1) (S 1) n +
      m 2 * Chart.rawMoment 0 (V 2) (S 2) n = 0 := by
    simpa only [Fin.sum_univ_three, he, sub_self, m, V, S] using
      normalized_low s g r hn hl ((g 0).mean r) n hlt
  have hm0 : m 0 + m 1 + m 2 = 0 := by simpa [Chart.rawMoment] using hraw 0 (by decide)
  obtain ⟨p,hp,hq,hmix⟩ := mixtureWeights _ _ _ (hm 0) (hm 1) (hm 2) hm0
  obtain ⟨hS0,hS1,hV0,hV1⟩ := equalMean_mixture p (S 0) (S 1) (S 2) (V 0) (V 1) (V 2)
    hp hq (hv 0) (hv 1) (hv 2) (by
      intro n hn'
      apply hmix
      simpa only [← centered_raw _ _ n hn'] using hraw n (by omega))
  apply eq_zero_of_moments (3*(g 0).mean r) r hr
  intro n _
  simp only [total, moment_sum, moment_C_mul]
  simp only [Fin.sum_univ_three]
  rw [arm_normalized _ _ _ _ (hn 0), arm_normalized _ _ _ _ (hn 1),
      arm_normalized _ _ _ _ (hn 2), he 1, he 2, sub_self]
  simp only [← mul_assoc]
  change m 0 * ((Chart.rawMoment 0 (V 0) (S 0) n)) +
    m 1 * (Chart.rawMoment 0 (V 1) (S 1) n) + m 2 * (Chart.rawMoment 0 (V 2) (S 2) n) = 0
  rw [hS0,hS1,hV0,hV1,← add_mul,← add_mul,hm0,zero_mul]

end
end SparseCubes

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section


theorem nonvanishing_cases (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hn : ∀ i, (g i).value r ≠ 0)
    (hl : LowMoments s g r) :
    total s g = 0 ∨ ∃ m x v u : Fin 3 → ℝ,
      (∀ i, m i ≠ 0) ∧ Function.Injective x ∧ (∀ i, v i ≠ 0) ∧
      (∑ i, x i) = 0 ∧ ∀ n < 10, ∑ i, m i * Chart.rawMoment (x i) (v i) (u i) n = 0 := by
  let t : ℝ := ((g 0).mean r+(g 1).mean r+(g 2).mean r)/3
  let x : Fin 3 → ℝ := fun i => (g i).mean r-t
  let m : Fin 3 → ℝ := fun i => s i*((g i).value r)^3
  let v : Fin 3 → ℝ := fun i => (g i).variance r
  let u : Fin 3 → ℝ := fun i => (g i).skew r
  have hm (i) : m i ≠ 0 := mul_ne_zero (hs i) (pow_ne_zero _ (hn i))
  have H (n : ℕ) (hn' : n<10) : ∑ i, m i * Chart.rawMoment (x i) (v i) (u i) n = 0 :=
    normalized_low s g r hn hl t n hn'
  have h0 : m 0+m 1+m 2=0 := by simpa only [Fin.sum_univ_three, Chart.rawMoment,mul_one] using H 0 (by decide)
  have h1 : m 0*x 0+m 1*x 1+m 2*x 2=0 := by
    have h := H 1 (by decide)
    simp only [Fin.sum_univ_three, Chart.rawMoment] at h
    linarith only [h]
  rcases three_nodes m x hm h0 h1 with he|hd
  · left
    apply same_mean_zero s g r hr hs hg hn _ hl
    intro i
    exact sub_left_inj.mp (he i)
  · right
    refine ⟨m,x,v,u,hm,hd,fun i => Arm.variance_ne _ _ hr (hg i) (hn i),?_,H⟩
    simp only [Fin.sum_univ_three,x,t]
    ring

end
end SparseCubes

namespace SparseCubes
open Polynomial
noncomputable section


def Arm.vanWeight (g : Arm) (r : ℝ) := (g.leftMass r*((g.left:ℝ)-g.right))^3
def Arm.vanMean (g : Arm) : ℝ := 3*((g.left:ℝ)+g.right)/2
def Arm.vanVariance (g : Arm) : ℝ := ((g.left:ℝ)-g.right)^2/4

theorem centeredCubeMoment_raw (n : ℕ) (hn : n≤9) (s v : ℝ) :
    Chart.rawMoment 0 v s n = centeredCubeMoment n s v := by
  interval_cases n <;> norm_num [Chart.rawMoment,centeredCubeMoment] <;> ring

theorem arm_vanMoment (g : Arm) (r t : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) (hn : n≤6) :
    moment (3*t) r (n+3) (g.poly^3) = g.vanWeight r*
      (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3))*uniformCubeMoment n (g.vanMean-3*t) g.vanVariance := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  rw [moment_arm_cube,hr]
  interval_cases n <;> norm_num [cubeFour,Arm.vanWeight,Arm.vanMean,Arm.vanVariance,uniformCubeMoment] <;> ring

theorem arm_vanMoment_low (g : Arm) (r t : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) (hn : n<3) : moment (3*t) r n (g.poly^3)=0 := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  rw [moment_arm_cube,hr]
  interval_cases n <;> simp [cubeFour] <;> ring

private def vanishingSequence (m v : ℝ) : ℕ → ℝ
  | 0 | 1 | 2 => 0
  | 3 => 6
  | n+4 =>
    let s := 2*m/3
    let p := (m/3)^2-v
    let k := 3*s
    let o := 9*p
    let i := 2*s^2+p
    2*k*vanishingSequence m v (n+3) - (k^2+o+i)*vanishingSequence m v (n+2) +
      k*(o+i)*vanishingSequence m v (n+1) - o*i*vanishingSequence m v n

private theorem vanishingSequence_four (A a b : ℝ) (n : ℕ) :
    cubeFour A (-A) a b n = (A*(a-b))^3*vanishingSequence (3*(a+b)/2) ((a-b)^2/4) n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => simp [cubeFour,vanishingSequence]; ring
    | n+4 =>
      rw [cubeFour_step,vanishingSequence]
      rw [ih (n+3) (by omega),ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      ring

private theorem arm_vanMoment_all (g : Arm) (r : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) : moment 0 r n (g.poly^3) =
      g.vanWeight r * vanishingSequence g.vanMean g.vanVariance n := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  simpa [hr,vanishingSequence_four,Arm.vanWeight,Arm.vanMean,Arm.vanVariance]
    using moment_arm_cube g r 0 n


theorem allVanishing_arms (a b c : Arm) (u v w r : ℝ)
    (ha : a.leftMass r+a.rightMass r=0) (hb : b.leftMass r+b.rightMass r=0)
    (hc : c.leftMass r+c.rightMass r=0)
    (hu : u*a.vanWeight r≠0) (hv : v*b.vanWeight r≠0) (hw : w*c.vanWeight r≠0)
    (H : ∀ n : ℕ, n<10 → ∀ t : ℝ, u*moment (3*t) r n (a.poly^3) +
        v*moment (3*t) r n (b.poly^3) + w*moment (3*t) r n (c.poly^3)=0) :
    ∀ n : ℕ, u*moment 0 r n (a.poly^3) + v*moment 0 r n (b.poly^3) +
      w*moment 0 r n (c.poly^3)=0 := by
  have U (n : ℕ) (hn : n≤6) :
      (u*a.vanWeight r)*uniformCubeMoment n a.vanMean a.vanVariance +
      (v*b.vanWeight r)*uniformCubeMoment n b.vanMean b.vanVariance +
      (w*c.vanWeight r)*uniformCubeMoment n c.vanMean c.vanVariance=0 := by
    have e := H (n+3) (by omega) 0
    rw [arm_vanMoment a r 0 ha n hn,arm_vanMoment b r 0 hb n hn,arm_vanMoment c r 0 hc n hn] at e
    simp only [mul_zero,sub_zero] at e
    have hfac : (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3))≠0 := by positivity
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination e
  have sumw := U 0 (by decide)
  simp only [uniformCubeMoment,mul_one] at sumw
  obtain ⟨p,hp,hq,hm⟩ := mixtureWeights _ _ _ hu hv hw sumw
  obtain ⟨haM,hbM,haV,hbV⟩ := threeVanish_mixture p _ _ _ _ _ _ hp hq (fun n hn => hm _ _ _ (U n hn))
  intro n
  rw [arm_vanMoment_all _ _ ha,arm_vanMoment_all _ _ hb,arm_vanMoment_all _ _ hc,haM,hbM,haV,hbV]
  linear_combination vanishingSequence c.vanMean c.vanVariance n * sumw


theorem oneVanishing_arms (a b c : Arm) (u v w r : ℝ)
    (ha : a.leftMass r+a.rightMass r≠0) (hb : b.leftMass r+b.rightMass r≠0)
    (hc : c.leftMass r+c.rightMass r=0)
    (hu : u≠0) (hv : v≠0) (hw : w*c.vanWeight r≠0) (hvar : a.variance r≠0)
    (H : ∀ n : ℕ, n<10 → ∀ t : ℝ, u*moment (3*t) r n (a.poly^3) +
        v*moment (3*t) r n (b.poly^3) + w*moment (3*t) r n (c.poly^3)=0) : False := by
  let A := u*(a.leftMass r + a.rightMass r)^3
  let B := v*(b.leftMass r + b.rightMass r)^3
  let C := w*c.vanWeight r
  have hA : A≠0 := mul_ne_zero hu (pow_ne_zero _ ha)
  have hB : B≠0 := mul_ne_zero hv (pow_ne_zero _ hb)
  have raw (n : ℕ) (hn : n<10) (t : ℝ) :
      A*Chart.rawMoment (a.mean r-t) (a.variance r) (a.skew r) n +
      B*Chart.rawMoment (b.mean r-t) (b.variance r) (b.skew r) n +
      w*moment (3*t) r n (c.poly^3)=0 := by
    have e := H n hn t
    rw [arm_normalized a r t n ha,arm_normalized b r t n hb] at e
    dsimp [A,B]; linear_combination e
  have h0 := raw 0 (by decide) 0
  rw [arm_vanMoment_low _ _ _ hc _ (by decide)] at h0
  simp only [Chart.rawMoment, mul_one,mul_zero,add_zero] at h0
  have Bval : B= -A := by linarith
  have h1 := raw 1 (by decide) 0
  rw [arm_vanMoment_low _ _ _ hc _ (by decide),Bval] at h1
  simp only [Chart.rawMoment, sub_zero,mul_zero,add_zero] at h1
  have sameMean : b.mean r=a.mean r := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hA
    linear_combination -h1/3
  have centered (n : ℕ) (hn : n<10) :
      A*centeredCubeMoment n (a.skew r) (a.variance r) -
      A*centeredCubeMoment n (b.skew r) (b.variance r) +
      w*moment (3*a.mean r) r n (c.poly^3)=0 := by
    have e := raw n hn (a.mean r)
    rw [Bval,sameMean] at e
    simp only [sub_self,centeredCubeMoment_raw n (by omega)] at e
    linear_combination e
  have h2 := centered 2 (by decide)
  rw [arm_vanMoment_low _ _ _ hc _ (by decide)] at h2
  simp only [centeredCubeMoment,mul_zero,add_zero] at h2
  have sameVar : b.variance r=a.variance r := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hA
    linear_combination -h2/3
  let h := (a.skew r+b.skew r)/2
  let d := (a.skew r-b.skew r)/2
  have sa : h+d=a.skew r := by dsimp [h,d]; ring
  have sb : h-d=b.skew r := by dsimp [h,d]; ring
  have e3 := centered 3 (by decide)
  rw [arm_vanMoment _ _ _ hc 0 (by decide),sameVar] at e3
  norm_num [centeredCubeMoment,uniformCubeMoment] at e3
  have relation : C = -A*(a.variance r)*d := by dsimp [C,d]; linear_combination e3/6
  have hd : d≠0 := by
    intro h0
    exact hw (show C=0 by rw [relation,h0,mul_zero])
  apply oneVanish_excludes h d (a.variance r) (c.vanMean-3*a.mean r) c.vanVariance hd hvar
  intro n hn
  have e := centered (n+3) (by omega)
  rw [arm_vanMoment _ _ _ hc n hn,sameVar] at e
  rw [sa,sb]
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_left hA
  dsimp [C] at relation
  linear_combination e -
    (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*uniformCubeMoment n (c.vanMean-3*a.mean r) c.vanVariance)*relation

end
end SparseCubes

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

theorem Arm.vanWeight_ne (g : Arm) (r : ℝ) (hr : r ≠ 0) (hg : g.Genuine) :
    g.vanWeight r ≠ 0 := by
  have hne : (g.left:ℝ) ≠ g.right := by exact_mod_cast hg.2.2
  exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero hg.1 (pow_ne_zero _ hr)) (sub_ne_zero.mpr hne))

theorem arm_eval (g : Arm) (r : ℝ) : g.poly.eval r = g.value r := by
  simp [Arm.poly, Arm.value, Arm.leftMass, Arm.rightMass]

theorem zero_of_third_vanishes (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hz : (g 2).value r = 0)
    (hl : LowMoments s g r) : total s g = 0 := by
  have hv (i) := mul_ne_zero (hs i) (Arm.vanWeight_ne (g i) r hr (hg i))
  have hsum (n : ℕ) (hn : n<10) (t : ℝ) := hl n hn t
  simp only [Fin.sum_univ_three] at hsum
  have hval := hsum 0 (by decide) 0
  simp only [moment, eval_pow, arm_eval, hz, zero_pow (by decide : 3 ≠ 0), mul_zero,add_zero] at hval
  by_cases h0 : (g 0).value r = 0
  · have h1 : (g 1).value r = 0 := by
      simpa [h0, hs 1] using hval
    have H := allVanishing_arms _ _ _ _ _ _ r h0 h1 hz (hv 0) (hv 1) (hv 2) hsum
    apply eq_zero_of_moments 0 r hr
    intro n _
    simp only [total, moment_sum, moment_C_mul]
    simpa only [Fin.sum_univ_three] using H n
  · have h1 : (g 1).value r ≠ 0 := by
      intro h1
      simpa [h1,hs 0,h0] using hval
    exact (oneVanishing_arms _ _ _ _ _ _ r h0 h1 hz (hs 0) (hs 1) (hv 2)
      (Arm.variance_ne _ _ hr (hg 0) h0) hsum).elim

theorem zero_of_any_vanishes (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hz : ∃ i, (g i).value r = 0)
    (hl : LowMoments s g r) : total s g = 0 := by
  obtain ⟨i, hi⟩ := hz
  let e := Equiv.swap i (2 : Fin 3)
  rw [← total_perm s g e]
  apply zero_of_third_vanishes (s ∘ e) (g ∘ e) r hr (fun j => hs _) (fun j => hg _)
  · simpa [e,Function.comp_def] using hi
  · exact low_perm s g r hl e

end
end SparseCubes

namespace SparseCubes.Chart


abbrev Rep := ℝ × ℝ × ℝ
abbrev Rep.u (r : Rep) := r.1
abbrev Rep.l (r : Rep) := r.2.1
abbrev Rep.k (r : Rep) := r.2.2

namespace Rep

def eval (b z : ℝ) (r : Rep) : ℝ := r.u+r.l*z+r.k*(z^2-b)
def add (r t : Rep) : Rep := ⟨r.u+t.u,r.l+t.l,r.k+t.k⟩
def scale (a : ℝ) (r : Rep) : Rep := ⟨a*r.u,a*r.l,a*r.k⟩
def mul (b c : ℝ) (r t : Rep) : Rep :=
  ⟨r.u*t.u+b*r.l*t.l+c*(r.l*t.k+r.k*t.l),
   r.u*t.l+r.l*t.u+c*r.k*t.k,
   r.u*t.k+r.k*t.u+r.l*t.l-b*r.k*t.k⟩

theorem eval_add (b z : ℝ) (r t : Rep) :
    (r.add t).eval b z = r.eval b z + t.eval b z := by
  simp only [eval,add]; ring

theorem eval_scale (b z a : ℝ) (r : Rep) :
    (r.scale a).eval b z = a*r.eval b z := by
  simp only [eval,scale]; ring

theorem eval_mul (b c z : ℝ) (hz : z^3=b*z+c) (r t : Rep) :
    (mul b c r t).eval b z = r.eval b z * t.eval b z := by
  simp only [eval,mul]
  linear_combination -(r.l*t.k+r.k*t.l+z*r.k*t.k)*hz

end Rep


def mass (m f : Fin 3 → ℝ) := ∑ i, m i * f i

theorem mass_rep (m x : Fin 3 → ℝ) (b : ℝ) (r : Rep)
    (h0 : mass m (fun _ => 1)=0) (h1 : mass m x=0) :
    mass m (fun i => r.eval b (x i)) = r.k*mass m (fun i => (x i)^2-b) := by
  simp only [mass, Fin.sum_univ_three, Rep.eval, mul_one] at *
  linear_combination r.u*h0+r.l*h1

theorem mass_quadratic_ne (m x : Fin 3 → ℝ) (b : ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (h0 : mass m (fun _ => 1)=0) (h1 : mass m x=0) :
    mass m (fun i => (x i)^2-b) ≠ 0 := by
  intro h2
  have hc : m 2 * (x 2-x 0) * (x 2-x 1) = 0 := by
    simp only [mass, Fin.sum_univ_three, mul_one] at *
    linear_combination h2 - (x 0+x 1)*h1 + (b+x 0*x 1)*h0
  exact (mul_ne_zero (mul_ne_zero hm (sub_ne_zero.mpr (hx.ne (by decide))))
    (sub_ne_zero.mpr (hx.ne (by decide)))) hc

theorem affine_of_mass_zero (m x f : Fin 3 → ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (h0 : mass m (fun _ => 1)=0)
    (h1 : mass m x=0) (hf : mass m f=0) :
    ∃ a t : ℝ, ∀ i, f i = a+t*x i := by
  let t := (f 1-f 0)/(x 1-x 0)
  let a := f 0-t*x 0
  have h10 : x 1-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have ha : f 0 = a+t*x 0 := by dsimp [a]; ring
  have hb : f 1 = a+t*x 1 := by
    dsimp [a,t]
    field_simp
    ring
  refine ⟨a,t,?_⟩
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · have hh : m 2 * (f 2 - (a+t*x 2)) = 0 := by
      simp only [mass, Fin.sum_univ_three, mul_one] at h0 h1 hf
      linear_combination hf-a*h0-t*h1-m 0*ha-m 1*hb
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hm)

theorem interpolate (m x f : Fin 3 → ℝ) (b : ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (h0 : mass m (fun _ => 1)=0)
    (h1 : mass m x=0) : ∃ r : Rep, ∀ i, f i = r.eval b (x i) := by
  let K := fun i => (x i)^2-b
  let q := mass m f / mass m K
  have hk : mass m K ≠ 0 := mass_quadratic_ne m x b hm hx h0 h1
  have hq : q * mass m K = mass m f := div_mul_cancel₀ _ hk
  have hsub : mass m (fun i => f i-q*K i) = 0 := by
    simp only [mass, Fin.sum_univ_three] at hq ⊢
    linear_combination -hq
  obtain ⟨a,t,hr⟩ := affine_of_mass_zero m x _ hm hx h0 h1 hsub
  refine ⟨⟨a,t,q⟩,fun i => ?_⟩
  simpa only [Rep.eval,← add_assoc] using (sub_eq_iff_eq_add.mp (hr i))

def coeffB (x : Fin 3 → ℝ) := -(x 0*x 1+x 0*x 2+x 1*x 2)
def coeffC (x : Fin 3 → ℝ) := x 0*x 1*x 2

theorem mean_cubic (x : Fin 3 → ℝ) (h : ∑ i, x i = 0) (i : Fin 3) :
    (x i)^3 = coeffB x*x i+coeffC x := by
  simp only [Fin.sum_univ_three] at h
  unfold coeffB coeffC
  fin_cases i
  · change (x 0)^3 = -(x 0*x 1+x 0*x 2+x 1*x 2)*x 0+x 0*x 1*x 2
    linear_combination (x 0)^2*h
  · change (x 1)^3 = -(x 0*x 1+x 0*x 2+x 1*x 2)*x 1+x 0*x 1*x 2
    linear_combination (x 1)^2*h
  · change (x 2)^3 = -(x 0*x 1+x 0*x 2+x 1*x 2)*x 2+x 0*x 1*x 2
    linear_combination (x 2)^2*h

theorem discriminant_ne (x : Fin 3 → ℝ) (hx : Function.Injective x) (h : ∑ i, x i = 0) :
    4*(coeffB x)^3-27*(coeffC x)^2 ≠ 0 := by
  have hz : x 2 = -x 0-x 1 := by simp only [Fin.sum_univ_three] at h; linarith
  have hd : 4*(coeffB x)^3-27*(coeffC x)^2 =
      ((x 0-x 1)*(x 0-x 2)*(x 1-x 2))^2 := by
    simp only [coeffB,coeffC,hz]; ring
  rw [hd]
  exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hx.ne (by decide)))
    (sub_ne_zero.mpr (hx.ne (by decide)))) (sub_ne_zero.mpr (hx.ne (by decide))))

end SparseCubes.Chart
namespace SparseCubes.Chart

def variance (b d e z : ℝ) := 3*(d+e*z-(z^2-b))
def skew (b d e j w z : ℝ) := (d+b)*w+e*(j+9)+j*z+w*(z^2-b)


theorem chart_parameters (m x v s : Fin 3 → ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (hc : ∑ i, x i = 0)
    (h0 : mass m (fun _ => 1)=0) (h1 : mass m x=0)
    (h2 : mass m (fun i => rawMoment (x i) (v i) (s i) 2)=0)
    (h3 : mass m (fun i => rawMoment (x i) (v i) (s i) 3)=0) :
    ∃ d e j w : ℝ, (∀ i, v i = variance (coeffB x) d e (x i)) ∧
      ∀ i, s i = skew (coeffB x) d e j w (x i) := by
  let b := coeffB x
  let c := coeffC x
  obtain ⟨vr,hv⟩ := interpolate m x v b hm hx h0 h1
  obtain ⟨sr,hs⟩ := interpolate m x s b hm hx h0 h1
  have hk := mass_quadratic_ne m x b hm hx h0 h1
  let r2 : Rep := ⟨9*b+3*vr.u,3*vr.l,9+3*vr.k⟩
  have he2 (i) : rawMoment (x i) (v i) (s i) 2 = r2.eval b (x i) := by
    rw [rawMoment,hv i]; simp only [r2,Rep.eval]; ring
  simp_rw [he2] at h2
  rw [mass_rep m x b r2 h0 h1] at h2
  have hvk : vr.k = -3 := by
    have := (mul_eq_zero.mp h2).resolve_right hk
    change 9+3*vr.k = 0 at this
    linarith
  let d := vr.u/3
  let e := vr.l/3
  let V : Rep := ⟨3*d,3*e,-3⟩
  let X : Rep := ⟨0,1,0⟩
  have hve (i) : v i = V.eval b (x i) := by
    rw [hv i]; simp only [V,Rep.eval,d,e,hvk]; ring
  let r3 := Rep.add (Rep.scale 27 (Rep.mul b c (Rep.mul b c X X) X))
    (Rep.add (Rep.scale 27 (Rep.mul b c X V)) (Rep.scale 3 (Rep.mul b c V sr)))
  have he3 (i) : rawMoment (x i) (v i) (s i) 3 = r3.eval b (x i) := by
    have hroot : (x i)^3=b*x i+c := mean_cubic x hc i
    rw [rawMoment,hve i,hs i]
    simp only [r3,Rep.eval_add,Rep.eval_scale,Rep.eval_mul _ _ _ hroot]
    simp only [X,Rep.eval]
    ring
  simp_rw [he3] at h3
  rw [mass_rep m x b r3 h0 h1] at h3
  have hsr := (mul_eq_zero.mp h3).resolve_right hk
  have hu : sr.u = (d+b)*sr.k+e*(sr.l+9) := by
    simp only [r3, Rep.add, Rep.scale, Rep.mul, X, V] at hsr
    linear_combination (-1/9:ℝ)*hsr
  refine ⟨d,e,sr.l,sr.k,?_,?_⟩
  · intro i
    rw [hve i]; simp only [V,Rep.eval,variance,b]; ring
  · intro i
    rw [hs i]; simp only [Rep.eval,hu,skew,b]

theorem rawMoment_scale (t x v s : ℝ) (n : ℕ) :
    rawMoment (t*x) (t^2*v) (t*s) n = t^n*rawMoment x v s n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => simp only [rawMoment]; ring
    | n+4 =>
      simp only [rawMoment]
      rw [ih (n+3) (by omega),ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      simp only [pow_add]
      ring

theorem variance_scale (t b d e z : ℝ) :
    variance (t^2*b) (t^2*d) (t*e) (t*z) = t^2 * variance b d e z := by
  unfold variance; ring

theorem skew_scale_to_one (w b d e j z : ℝ) :
    skew (w^2*b) (w^2*d) (w*e) j 1 (w*z) = w * skew b d e j w z := by
  unfold skew; ring

end SparseCubes.Chart

noncomputable section

namespace SparseCubes.Certificate


abbrev Tower : Nat → Type
  | 0 => Int
  | n+1 => List (Tower n)

def value {α : Type} (f : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | h :: t => f h + x * value f x t

def interp : (n : Nat) → Tower n → (Nat → ℝ) → ℝ
  | 0, z, _ => (z : ℝ)
  | n+1, z, v => value (fun a => interp n a (fun k => v (k+1))) (v 0) z

def plusList {α : Type} (plus : α → α → α) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => plus x y :: plusList plus xs ys

theorem value_plusList {α : Type} (f : α → ℝ) (x : ℝ) (plus : α → α → α)
    (h : ∀ a b, f (plus a b) = f a + f b) (xs ys : List α) :
    value f x (plusList plus xs ys) = value f x xs + value f x ys := by
  induction xs generalizing ys with
  | nil => simp [value, plusList]
  | cons a as ih =>
    cases ys with
    | nil => simp [value, plusList]
    | cons b bs =>
      simp only [plusList, value, h, ih]
      ring

def pzero : (n : Nat) → Tower n
  | 0 => 0
  | _+1 => []

def add : (n : Nat) → Tower n → Tower n → Tower n
  | 0, a, b => a+b
  | n+1, a, b => plusList (add n) a b

theorem interp_zero (n : Nat) (v : Nat → ℝ) : interp n (pzero n) v = 0 := by
  cases n <;> simp [interp, pzero, value]

theorem interp_add (n : Nat) (a b : Tower n) (v : Nat → ℝ) :
    interp n (add n a b) v = interp n a v + interp n b v := by
  induction n generalizing v with
  | zero => simp [interp, add]
  | succ n ih => exact value_plusList (fun a => interp n a (fun k => v (k+1))) (v 0) (add n) (fun _ _ => ih _ _ _) _ _

def isZero : (n : Nat) → Tower n → Bool
  | 0, z => z == 0
  | n+1, zs => zs.all (isZero n)

theorem interp_of_isZero (n : Nat) (a : Tower n) (v : Nat → ℝ)
    (h : isZero n a = true) : interp n a v = 0 := by
  induction n generalizing v with
  | zero =>
    have ha : a = (0 : Int) := by simpa [isZero] using h
    simp [ha, interp]
  | succ n ih =>
    change value _ _ a = 0
    change a.all (isZero n) = true at h
    induction a with
    | nil => rfl
    | cons a as ht =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp [value, ih _ _ h.1, ht h.2]

def timesList {α : Type} (plus mul : α → α → α) (zero : α)
    (isZ : α → Bool) (bs : List α) : List α → List α
  | [] => []
  | a :: as =>
    let tail := zero :: timesList plus mul zero isZ bs as
    if isZ a then tail else plusList plus (bs.map (mul a)) tail

theorem value_mapped {α : Type} (f : α → ℝ) (x : ℝ) (mul : α → α → α)
    (h : ∀ a b, f (mul a b) = f a * f b) (a : α) (bs : List α) :
    value f x (bs.map (mul a)) = f a * value f x bs := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    simp only [List.map_cons, value, h, ih]
    ring

theorem value_timesList {α : Type} (f : α → ℝ) (x : ℝ)
    (plus mul : α → α → α) (z : α) (iz : α → Bool)
    (hp : ∀ a b, f (plus a b) = f a + f b)
    (hm : ∀ a b, f (mul a b) = f a * f b)
    (hz : f z = 0) (hi : ∀ a, iz a = true → f a = 0)
    (as bs : List α) :
    value f x (timesList plus mul z iz bs as) = value f x as * value f x bs := by
  induction as with
  | nil => simp [timesList, value]
  | cons a as ih =>
    rw [timesList]
    split
    · rename_i h
      simp [value, hi a h, hz, ih]
      ring
    · rw [value_plusList _ _ _ hp, value_mapped _ _ _ hm]
      simp only [value, hz, zero_add, ih]
      ring

def mul : (n : Nat) → Tower n → Tower n → Tower n
  | 0, a, b => a*b
  | n+1, a, b => timesList (add n) (mul n) (pzero n) (isZero n) b a

theorem interp_mul (n : Nat) (a b : Tower n) (v : Nat → ℝ) :
    interp n (mul n a b) v = interp n a v * interp n b v := by
  induction n generalizing v with
  | zero => simp [interp, mul]
  | succ n ih =>
    exact value_timesList (fun a => interp n a (fun k => v (k+1))) (v 0) (add n) (mul n) (pzero n) (isZero n) (fun _ _ => interp_add _ _ _ _)
      (fun _ _ => ih _ _ _) (interp_zero _ _) (fun _ h => interp_of_isZero _ _ _ h) _ _

def point (b c d e j : ℝ) : Nat → ℝ
  | 0 => b
  | 1 => c
  | 2 => d
  | 3 => e
  | _ => j

end SparseCubes.Certificate

end

namespace SparseCubes.Certificate

def chartH (b c d e j : ℝ) : ℝ :=
  ((c*(c*((d*(d*(d*(-27)))) + (c*(((e*(e*(e*(-27)))) + (d*(e*(-81)))) + (c*27)))))) + (b*((c*(c*((d*((e*(e*27)) + (d*(-27)))) + (c*(e*(-54)))))) + (b*((c*(c*(e*(e*27)))) + (b*(((d*(d*(d*4))) + (c*(((e*(e*(e*4))) + (d*(e*12))) + (c*(-4))))) + (b*(((d*((e*(e*(-4))) + (d*4))) + (c*(e*8))) + (b*(e*(e*(-4)))))))))))))

def w0G0 (b c d e j : ℝ) : ℝ :=
  (((e*(e*(48 + (j*(12 + j))))) + (d*(12 + (j*(12 + j))))) + (b*(-12)))

def w0G1 (b c d e j : ℝ) : ℝ :=
  ((((e*(e*(e*(1080 + (j*(336 + (j*(42 + (j*2))))))))) + (d*(e*(252 + (j*(360 + (j*(57 + (j*3))))))))) + (c*(72 + (j*(-24 + (j*(-15 + (j*(-1))))))))) + (b*(e*(-324 + (j*(24 + (j*(15 + j))))))))

def w0G2 (b c d e j : ℝ) : ℝ :=
  ((((e*(e*(e*(e*(19440 + (j*(7236 + (j*(1131 + (j*(90 + (j*3)))))))))))) + (d*((e*(e*(8208 + (j*(9180 + (j*(1911 + (j*(162 + (j*6)))))))))) + (d*(1188 + (j*(1188 + (j*159)))))))) + (c*(e*(3024 + (j*(-756 + (j*(-621 + (j*(-72 + (j*(-3)))))))))))) + (b*(((e*(e*(-5184 + (j*(1296 + (j*(756 + (j*(90 + (j*4)))))))))) + (d*(-432 + (j*(540 + (j*(135 + (j*(18 + j))))))))) + (b*(-468)))))

def w0G3 (b c d e j : ℝ) : ℝ :=
  ((((e*(e*(e*(e*(e*(332424 + (j*(145800 + (j*(26892 + (j*(2724 + (j*(156 + (j*4))))))))))))))) + (d*((e*(e*(e*(260496 + (j*(237276 + (j*(58275 + (j*(6279 + (j*(354 + (j*10))))))))))))) + (d*(e*(57672 + (j*(72576 + (j*(16074 + (j*1044))))))))))) + (c*((e*(e*(69336 + (j*(-31104 + (j*(-21042 + (j*(-3018 + (j*(-177 + (j*(-5))))))))))))) + (d*(j*(-12204 + (j*(-5733 + (j*(-507 + (j*(21 + j)))))))))))) + (b*((((e*(e*(e*(-53352 + (j*(54252 + (j*(28035 + (j*(4341 + (j*(306 + (j*10))))))))))))) + (d*(e*(-23976 + (j*(34884 + (j*(13671 + (j*(2019 + (j*(129 + (j*5))))))))))))) + (c*(6912 + (j*(468 + (j*(-945 + (j*(-189 + (j*(-21 + (j*(-1))))))))))))) + (b*(e*(-24624 + (j*(-468 + (j*(945 + (j*(189 + (j*(21 + j))))))))))))))

def w0G4 (b c d e j : ℝ) : ℝ :=
  ((((e*(e*(e*(e*(e*(e*(5668704 + (j*(2913084 + (j*(627669 + (j*(74844 + (j*(5454 + (j*(240 + (j*5)))))))))))))))))) + (d*((e*(e*(e*(e*(7584516 + (j*(6318972 + (j*(1771389 + (j*(232812 + (j*(16236 + (j*(660 + (j*15)))))))))))))))) + (d*((e*(e*(2154600 + (j*(2988576 + (j*(886356 + (j*(103788 + (j*4374)))))))))) + (d*(79272 + (j*(79272 + (j*13662)))))))))) + (c*(((e*(e*(e*(1111536 + (j*(-1316520 + (j*(-729270 + (j*(-119628 + (j*(-8217 + (j*(-270 + (j*(-5)))))))))))))))) + (d*(e*(51840 + (j*(-826848 + (j*(-478980 + (j*(-72288 + (j*(-2286 + (j*(174 + (j*6))))))))))))))) + (c*(-24192 + (j*(6912 + (j*(20736 + (j*(6840 + (j*(477 + (j*(-24 + (j*(-1))))))))))))))))) + (b*((((e*(e*(e*(e*(293004 + (j*(2052432 + (j*(979128 + (j*(179172 + (j*(15993 + (j*(780 + (j*20)))))))))))))))) + (d*((e*(e*(-649296 + (j*(1611576 + (j*(821070 + (j*(153792 + (j*(12879 + (j*(510 + (j*15)))))))))))))) + (d*(30456 + (j*(99792 + (j*(40068 + (j*(8352 + (j*729)))))))))))) + (c*(e*(452736 + (j*(37152 + (j*(-93636 + (j*(-27288 + (j*(-3042 + (j*(-126 + (j*(-4)))))))))))))))) + (b*(((e*(e*(-865080 + (j*(-30456 + (j*(78570 + (j*(21960 + (j*(2817 + (j*(174 + (j*6)))))))))))))) + (d*(-38664 + (j*(13608 + (j*(5670 + (j*(1512 + (j*(252 + (j*(24 + j))))))))))))) + (b*(-14040)))))))


def w1T0 : Tower 5 := [[[[[], [], [48, 12, 1]], [[12, 12, 1], [12, 2]], [[1]]], [[[-12, -2], [1]]]], [[[[-12], [12, 2]], [[1]]]]]

def w1G0 (b c d e j : ℝ) : ℝ := interp 5 w1T0 (point b c d e j)

def w1T1 : Tower 5 := [[[[[],[],[],[1080,336,42,2]],[[],[252,360,57,3],[336,84,6]],[[24,30,3],[42,6]],[[2]]],[[[72,-24,-15,-1],[-312,-54,-3],[27,3]],[[-15,-3],[3]]],[[[-1]]]],[[[[],[-324,24,15,1],[336,84,6]],[[24,30,3],[57,9]],[[3]]],[[[-15,-3],[2]]]],[[[[],[15,3]],[[1]]]]]

def w1G1 (b c d e j : ℝ) : ℝ := interp 5 w1T1 (point b c d e j)

def w1T2 : Tower 5 := [[[[[],[],[],[],[19440,7236,1131,90,3]],[[],[],[8208,9180,1911,162,6],[7236,2262,270,12]],[[1188,1188,159],[1944,1560,216,12],[1131,270,18]],[[135,54,6],[90,12]],[[3]]],[[[],[3024,-756,-621,-72,-3],[-6480,-1020,-54],[486,108,6]],[[-1188,-318],[-534,-54],[108,12]],[[],[6]]],[[[24,-54,-6],[-18]],[[-3]]]],[[[[],[],[-5184,1296,756,90,4],[7236,2262,270,12]],[[-432,540,135,18,1],[2484,1830,270,16],[1776,432,30]],[[270,108,12],[162,24]],[[6]]],[[[-540,-270,-54,-4],[-534,-54],[72,8]],[[-18,-4],[8]]],[[[-2]]]],[[[[-468],[540,270,54,4],[645,162,12]],[[135,54,6],[90,16]],[[4]]],[[[-18,-4],[3]]]],[[[[],[18,4]],[[1]]]]]

def w1G2 (b c d e j : ℝ) : ℝ := interp 5 w1T2 (point b c d e j)

def w1T3 : Tower 5 := [[[[[],[],[],[],[],[332424,145800,26892,2724,156,4]],[[],[],[],[260496,237276,58275,6279,354,10],[145800,53784,8172,624,20]],[[],[57672,72576,16074,1044],[91476,62766,10665,792,30],[26892,8172,936,40]],[[5868,6678,1044],[11781,4923,522,30],[2724,624,40]],[[537,84,10],[156,20]],[[4]]],[[[],[],[69336,-31104,-21042,-3018,-177,-5],[-121032,-16488,405,168,10],[7290,2430,270,10]],[[0,-12204,-5733,-507,21,1],[-67176,-23580,-1521,84,5],[-12114,972,378,30],[2430,540,30]],[[-5733,-1521,126,10],[567,252,30],[270,30]],[[42,10],[10]]],[[[6336,4788,477,-84,-5],[-1440,-3312,-396,-20],[294,84,10]],[[-30,-168,-20],[-51,5]],[[-5]]],[[[-21,-5],[1]]]],[[[[],[],[],[-53352,54252,28035,4341,306,10],[145800,53784,8172,624,20]],[[],[-23976,34884,13671,2019,129,5],[120960,81540,15111,1224,50],[46494,13914,1602,70]],[[5400,8568,1611,84,5],[24507,10413,1170,70],[5742,1332,90]],[[1263,252,30],[354,50]],[[10]]],[[[6912,468,-945,-189,-21,-1],[-36288,-21672,-4356,-264,-10],[-12114,972,378,30],[1620,360,20]],[[-6678,-2088],[-318,240,40],[360,40]],[[42,10],[20]]],[[[-30,-168,-20],[-27,5]],[[-7]]]],[[[[],[-24624,-468,945,189,21,1],[29484,18774,4446,432,20],[19602,5742,666,30]],[[-468,1890,567,84,5],[13671,6057,774,50],[4122,972,70]],[[915,252,30],[306,50]],[[10]]],[[[-945,-567,-126,-10],[-885,-12,10],[135,15]],[[-21,-5],[15]]],[[[-3]]]],[[[[],[945,567,126,10],[1104,264,20]],[[189,84,10],[129,25]],[[5]]],[[[-21,-5],[4]]]],[[[[],[21,5]],[[1]]]]]

def w1G3 (b c d e j : ℝ) : ℝ := interp 5 w1T3 (point b c d e j)

def w1T4 : Tower 5 := [[[[[],[],[],[],[],[],[5668704,2913084,627669,74844,5454,240,5]],[[],[],[],[],[7584516,6318972,1771389,232812,16236,660,15],[2913084,1255338,224532,21816,1200,30]],[[],[],[2154600,2988576,886356,103788,4374],[3405888,2287440,473904,43128,2100,60],[627669,224532,32724,2400,75]],[[79272,79272,13662],[467208,558468,128844,8748],[614466,293112,39258,2340,90],[74844,21816,2400,100]],[[26406,25056,4374],[52020,14076,1020,60],[5454,1200,75]],[[1710,120,15],[240,30]],[[5]]],[[[],[],[],[1111536,-1316520,-729270,-119628,-8217,-270,-5],[-2028564,-182142,66852,12564,900,30],[98415,43740,7290,540,15]],[[],[51840,-826848,-478980,-72288,-2286,174,6],[-2565432,-1068444,-121176,1512,750,30],[-160272,119124,31212,2820,120],[43740,14580,1620,60]],[[-86184,-68796,-20520,-1908,120,6],[-406350,-121176,2268,1500,75],[52272,24732,3060,180],[7290,1620,90]],[[-13680,-3816,480,40],[6084,1260,120],[540,60]],[[120,30],[15]]],[[[-24192,6912,20736,6840,477,-24,-1],[425088,343872,46980,-3420,-630,-24],[-179280,-157572,-21006,-1080,-30],[31104,7236,780,40]],[[7992,-4536,-1512,-240,-15],[-20772,-16380,-1320,-60],[3591,750,75]],[[-1233,-240,-30],[-30,30]],[[-5]]],[[[6840,1908,-240,-20],[-2286,-270,-15],[54,6]],[[-96,-24],[6]]],[[[-1]]]],[[[[],[],[],[],[293004,2052432,979128,179172,15993,780,20],[2913084,1255338,224532,21816,1200,30]],[[],[],[-649296,1611576,821070,153792,12879,510,15],[4573800,3172500,720036,72720,3900,120],[1156923,405324,58158,4260,135]],[[30456,99792,40068,8352,729],[522936,784404,215244,21924,750,30],[1309824,643032,92394,5940,240],[180792,50868,5580,240]],[[58482,54648,10260,240,15],[131328,40320,3300,200],[14526,3180,210]],[[4653,480,60],[660,90]],[[15]]],[[[],[452736,37152,-93636,-27288,-3042,-126,-4],[-1643976,-1124604,-252288,-17820,-300],[-160272,119124,31212,2820,120],[29160,9720,1080,40]],[[-106704,-121608,-45576,-4824,120,6],[-510300,-189432,-11448,960,60],[32616,34452,4800,300],[9720,2160,120]],[[-28872,-8640,720,60],[8100,2220,240],[1080,120]],[[240,60],[40]]],[[[28728,15984,1350,-480,-30],[-20772,-16380,-1320,-60],[2997,630,60]],[[-1260,-600,-75],[-18,48]],[[-12]]],[[[-72,-18],[4]]]],[[[[],[],[-865080,-30456,78570,21960,2817,174,6],[1167912,885060,246132,29592,1800,60],[529254,180792,25434,1860,60]],[[-38664,13608,5670,1512,252,24,1],[69336,237276,90936,14184,870,36],[776250,406728,67014,4860,210],[151632,41148,4500,200]],[[37746,34128,7398,480,30],[108108,39420,3780,240],[15714,3420,240]],[[4428,720,90],[780,120]],[[20]]],[[[-13608,-11340,-4536,-1008,-120,-6],[-103950,-68256,-13716,-540,-15],[-19656,9720,1740,120],[3645,810,45]],[[-16704,-5832],[486,1050,150],[810,90]],[[120,30],[45]]],[[[-27,-360,-45],[-18,18]],[[-12]]]],[[[[-14040],[13608,11340,4536,1008,120,6],[80892,56808,13878,1260,60],[45684,12096,1320,60]],[[5670,4536,1512,240,15],[30312,14184,1740,120],[8451,1830,135]],[[1737,480,60],[510,90]],[[15]]],[[[-1512,-1008,-240,-20],[-1530,90,30],[216,24]],[[-24,-6],[24]]],[[[-4]]]],[[[[],[1512,1008,240,20],[1809,390,30]],[[252,120,15],[174,36]],[[6]]],[[[-24,-6],[5]]]],[[[[],[24,6]],[[1]]]]]

def w1G4 (b c d e j : ℝ) : ℝ := interp 5 w1T4 (point b c d e j)

def w1T5 : Tower 5 := [[[[[],[],[],[],[],[],[],[97785144,58576608,14788494,2063070,176580,9756,342,6]],[[],[],[],[],[],[207143892,170376048,53763021,8535699,741636,36576,1107,21],[58576608,29576988,6189210,706320,48780,2052,42]],[[],[],[],[72841680,105511248,38106288,6160212,482112,14940],[111799440,77949054,19417887,2260224,134100,4590,105],[14788494,6189210,1059480,97560,5130,126]],[[],[6440472,7709904,2048490,145638],[24522264,30055212,8802756,1042956,44820],[25426062,13917582,2483946,187650,7290,210],[2063070,706320,97560,6840,210]],[[671328,737748,145638],[2840184,2755296,639576,44820],[3035394,1153764,124110,5400,210],[176580,48780,5130,210]],[[112752,78732,14940],[188406,38790,1755,105],[9756,2052,126]],[[4806,162,21],[342,42]],[[6]]],[[[],[],[],[],[8295048,-50049576,-25402977,-4713795,-394794,-14355,-180],[-27766152,2214702,3550797,668412,55440,2538,63],[1240029,688905,153090,17010,945,21]],[[],[],[1341360,-38158776,-25028514,-5007906,-377379,-2709,783,21],[-82744416,-38475648,-5567778,-46980,47385,3510,105],[2037555,6609519,1808406,190170,10395,315],[688905,306180,51030,3780,105]],[[-699840,-1739232,-746010,-32886,19683,1494],[-7803216,-6968268,-2256498,-262116,-1170,1188,42],[-18062676,-5375160,47628,109710,8775,315],[3058722,1611576,237870,16200,630],[153090,51030,5670,210]],[[-707130,-260658,13608,3240,405,21],[-1083942,-236520,45360,6300,315],[471582,126990,11610,630],[17010,3780,210]],[[-12879,-2610,1215,105],[23850,3510,315],[945,105]],[[243,63],[21]]],[[[],[-1990656,368064,1796256,719280,85212,1728,-198,-6],[18871056,15421752,2243538,-136404,-41085,-2322,-63],[-10019376,-6645240,-1055592,-57420,-1080],[1374165,400140,46530,3060,105]],[[1067904,754272,-46980,-78732,-7470],[375192,-745200,-323676,-47700,-1755,-63],[-1857168,-1062396,-95400,-2160],[323595,67545,6345,315]],[[-79866,-157464,-29880],[-161514,-45450,-1080],[21015,3510,315]],[[-7470],[225,105]]],[[[-38880,162000,104490,11700,-405,-21],[557280,131868,-17820,-2340,-105],[-133002,-14355,-540],[1701,378,21]],[[32562,10080,-1215,-105],[-16164,-1350,-63],[378,42]],[[-243,-63],[21]]],[[[1170,-162,-21],[-36]],[[-6]]]],[[[[],[],[],[],[],[39932676,71595360,33649911,7084017,774360,46656,1665,35],[58576608,29576988,6189210,706320,48780,2052,42]],[[],[],[],[-9821088,65144520,39085578,9075726,1027323,56205,1485,35],[152584344,113457186,30929931,3982932,263160,9990,245],[28336959,11689515,1965870,178110,9315,231]],[[],[2618568,9577440,4872150,1192482,145962,7470],[31398192,46022256,16006410,2386584,151965,3510,105],[55367550,31477086,5992866,490590,20790,630],[5500305,1812780,241650,16740,525]],[[946080,1458972,483894,78732,7470],[6677154,6462666,1630044,143820,2565,105],[8090442,3338496,393390,19080,770],[553230,144090,14850,630]],[[348462,245268,48060,540,35],[554202,134370,7425,455],[31770,6480,420]],[[15066,810,105],[1107,147]],[[21]]],[[[],[],[18712944,969192,-5936490,-2181654,-309987,-18027,-333,-7],[-61779456,-46840680,-11803320,-1088640,-19350,1620,70],[2037555,6609519,1808406,190170,10395,315],[459270,204120,34020,2520,70]],[[466560,-692928,-659988,-205092,-34830,-2340,54,2],[-10210752,-12509640,-5143176,-749088,-27810,1512,56],[-24451632,-9930924,-918540,67320,10260,420],[3303504,2452032,397260,28080,1120],[204120,68040,7560,280]],[[-1367118,-875934,-195372,-20160,1215,63],[-2434212,-661608,52740,11880,630],[745686,258030,25650,1470],[34020,7560,420]],[[-60588,-16920,3240,280],[50940,8640,840],[2520,280]],[[675,175],[70]]],[[[418176,598752,277020,60588,4230,-324,-14],[2249208,1088640,-21384,-53820,-3915,-147],[-1857168,-1062396,-95400,-2160],[249075,52785,4995,245]],[[2268,-105948,-24660,-1620,-105],[-242514,-99810,-3915,-105],[32373,5454,483]],[[-12078,-810,-105],[459,231]],[[-7]]],[[[32562,10080,-1215,-105],[-12042,-972,-42],[252,28]],[[-378,-98],[28]]],[[[-4]]]],[[[[],[],[],[-25602480,-530712,4507650,1584846,250695,19701,783,21],[40784904,35508132,11512044,1722708,129060,5400,140],[13548465,5500305,906390,80550,4185,105]],[[],[-2949048,1427760,1058022,337770,63018,6066,225,7],[8100648,17300628,7848090,1507896,128385,4698,147],[34456914,21201426,4533894,418230,19710,630],[5041035,1608660,207630,14220,455]],[[203040,782460,368874,87804,9090,162,7],[4864374,4690062,1354968,156420,5535,231],[7269102,3361824,450450,24840,1050],[702270,173610,17550,770]],[[368874,263412,54540,1620,105],[601668,179460,12150,770],[46530,9180,630]],[[18180,1620,210],[1665,245]],[[35]]],[[[326592,71712,-30618,-10206,-2268,-324,-27,-1],[-1714608,-1871100,-890838,-215784,-23850,-702,-21],[-6388956,-4555764,-966168,-42390,1485,105],[244782,840456,159390,11880,490],[76545,25515,2835,105]],[[-690606,-645894,-222588,-26640,405,21],[-1616598,-613656,-30600,4860,315],[243891,165825,18765,1155],[25515,5670,315]],[[-84807,-27630,2430,210],[31950,7560,840],[2835,315]],[[675,175],[105]]],[[[82134,51516,5220,-1620,-105],[-81000,-54360,-2835,-105],[12609,2106,189]],[[-4410,-1458,-189],[216,168]],[[-21]]],[[[-162,-42],[10]]]],[[[[],[-1117800,-71712,30618,10206,2268,324,27,1],[1224720,1333584,644436,164268,21240,1188,42],[4515426,3641922,1024974,115290,6210,210],[1603800,502200,63540,4320,140]],[[-71712,61236,30618,9072,1620,162,7],[1058022,1013310,378108,60660,3375,147],[2408454,1323216,217170,14040,630],[425655,101565,10125,455]],[[143370,105948,24660,1620,105],[296622,112590,9450,630],[38025,7290,525]],[[10710,1620,210],[1485,245]],[[35]]],[[[-30618,-30618,-13608,-3240,-405,-21],[-266328,-188568,-37980,-720],[-30213,34785,4725,315],[6804,1512,84]],[[-39366,-14940],[2034,2700,378],[1512,168]],[[243,63],[84]]],[[[198,-648,-84],[18,42]],[[-18]]]],[[[[],[30618,30618,13608,3240,405,21],[194400,146124,36000,2880,140],[100035,23265,2295,105]],[[10206,9072,3240,540,35],[63018,30330,3375,245],[16461,3078,231]],[[3114,810,105],[783,147]],[[21]]],[[[-2268,-1620,-405,-35],[-2826,270,63],[315,35]],[[-27,-7],[35]]],[[[-5]]]],[[[[],[2268,1620,405,35],[2952,540,42]],[[324,162,21],[225,49]],[[7]]],[[[-27,-7],[6]]]],[[[[],[27,7]],[[1]]]]]

def w1G5 (b c d e j : ℝ) : ℝ := interp 5 w1T5 (point b c d e j)

end SparseCubes.Certificate

namespace SparseCubes.Chart

def X : Rep := ⟨0,1,0⟩
def unit : Rep := ⟨1,0,0⟩
def V (d e : ℝ) : Rep := ⟨3*d,3*e,-3⟩
def S (b d e j w : ℝ) : Rep := ⟨(d+b)*w+e*(j+9),j,w⟩

theorem eval_unit (b z : ℝ) : unit.eval b z = 1 := by simp [unit,Rep.eval,Rep.u,Rep.l,Rep.k]

theorem eval_X (b z : ℝ) : X.eval b z = z := by simp [Rep.eval,X,Rep.u,Rep.l,Rep.k]
theorem eval_V (b d e z : ℝ) : (V d e).eval b z = variance b d e z := by
  simp only [Rep.eval,V,variance]; ring
theorem eval_S (b d e j w z : ℝ) : (S b d e j w).eval b z = skew b d e j w z := by rfl

def linear4 (b c : ℝ) (r0 r1 r2 r3 u0 u1 u2 u3 : Rep) : Rep :=
  ((Rep.mul b c r0 u0).add (Rep.mul b c r1 u1)).add
    ((Rep.mul b c r2 u2).add (Rep.mul b c r3 u3))

theorem eval_linear4 (b c z : ℝ) (hz : z^3=b*z+c) (r0 r1 r2 r3 u0 u1 u2 u3 : Rep) :
    (linear4 b c r0 r1 r2 r3 u0 u1 u2 u3).eval b z =
      r0.eval b z*u0.eval b z + r1.eval b z*u1.eval b z +
      r2.eval b z*u2.eval b z + r3.eval b z*u3.eval b z := by
  simp only [linear4,Rep.eval_add,Rep.eval_mul _ _ _ hz]; ring

theorem rep_ext {r s : Rep} (u : r.u=s.u) (l : r.l=s.l) (k : r.k=s.k) : r=s := by
  exact Prod.ext u (Prod.ext l k)


theorem chartH_ne (x : Fin 3 → ℝ) (d e j : ℝ) (hc : ∑ i, x i=0)
    (hx : Function.Injective x) (hv : ∀ i, variance (coeffB x) d e (x i) ≠ 0) :
    Certificate.chartH (coeffB x) (coeffC x) d e j ≠ 0 := by
  have hz : x 2 = -x 0-x 1 := by simp only [Fin.sum_univ_three] at hc; linarith
  have h : 27 * Certificate.chartH (coeffB x) (coeffC x) d e j =
      (4*(coeffB x)^3-27*(coeffC x)^2)*variance (coeffB x) d e (x 0)*
        variance (coeffB x) d e (x 1)*variance (coeffB x) d e (x 2) := by
    simp only [Certificate.chartH,variance,coeffB,coeffC,hz]
    ring
  intro hzero
  rw [hzero,mul_zero] at h
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (discriminant_ne x hx hc)
    (hv 0)) (hv 1)) (hv 2)) h.symm

def Case (w : ℝ) : Prop :=
  ∀ (m x : Fin 3 → ℝ) (d e j : ℝ), Function.Injective x → (∑ i, x i)=0 →
    (∀ i, variance (coeffB x) d e (x i) ≠ 0) →
    (∀ n < 10, mass m (fun i => rawMoment (x i) (variance (coeffB x) d e (x i))
        (skew (coeffB x) d e j w (x i)) n)=0) → m 2 ≠ 0 → False

theorem center_distinct_of_cases (case0 : Case 0) (case1 : Case 1)
    (m x v s : Fin 3 → ℝ) (hm : ∀ i, m i ≠ 0) (hx : Function.Injective x)
    (hv : ∀ i, v i ≠ 0) (hc : ∑ i, x i=0)
    (hz : ∀ n < 10, mass m (fun i => rawMoment (x i) (v i) (s i) n)=0) : False := by
  have h0 := hz 0 (by decide)
  change mass m (fun _ => 1)=0 at h0
  have hm1 := hz 1 (by decide)
  have h1 : mass m x = 0 := by
    simp only [mass,Fin.sum_univ_three,rawMoment] at hm1 ⊢
    linear_combination (1/3 : ℝ)*hm1
  obtain ⟨d,e,j,w,hv',hs'⟩ := chart_parameters m x v s (hm 2) hx hc h0 h1
    (hz 2 (by decide)) (hz 3 (by decide))
  let b := coeffB x
  have hvar i : variance b d e (x i) ≠ 0 := by rw [← hv' i]; exact hv i
  have hraw n (hn : n < 10) :
      mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j w (x i)) n)=0 := by
    simpa only [← hv',← hs',b] using hz n hn
  by_cases hw : w=0
  · subst w; exact case0 m x d e j hx hc hvar hraw (hm 2)
  · let y := fun i => w * x i
    have hy : Function.Injective y := fun a b h => hx (mul_left_cancel₀ hw h)
    have hyc : ∑ i, y i=0 := by simp only [y,← Finset.mul_sum,hc,mul_zero]
    have hb : coeffB y=w^2*b := by simp only [coeffB,y,b]; ring
    apply case1 m y (w^2*d) (w*e) j hy hyc
    · intro i
      rw [hb,show y i=w*x i from rfl,variance_scale]
      exact mul_ne_zero (pow_ne_zero _ hw) (hvar i)
    · intro n hn
      simp only [hb,y,variance_scale,skew_scale_to_one,rawMoment_scale]
      have h := hraw n hn
      simp only [mass,Fin.sum_univ_three] at h ⊢
      linear_combination w^n*h
    · exact hm 2

end SparseCubes.Chart
namespace SparseCubes.Chart

def initialRep (b c d e j w : ℝ) (n : Fin 4) : Rep :=
  let v := V d e
  let s := S b d e j w
  let x2 := Rep.mul b c X X
  let x3 := Rep.mul b c x2 X
  match n with
  | 0 => unit
  | 1 => Rep.scale 3 X
  | 2 => (Rep.scale 9 x2).add (Rep.scale 3 v)
  | 3 => ((Rep.scale 27 x3).add (Rep.scale 27 (Rep.mul b c X v))).add
      (Rep.scale 3 (Rep.mul b c v s))

def recRep (b c d e j w : ℝ) (n : Fin 4) : Rep :=
  let v := V d e
  let s := S b d e j w
  let t := (X.scale 2).add s
  let p := ((Rep.mul b c X X).add (Rep.mul b c X s)).add (v.scale (-1))
  let a := t.scale 3
  let o := p.scale 9
  let u := ((Rep.mul b c t t).scale 2).add p
  match n with
  | 0 => a.scale 2
  | 1 => (((Rep.mul b c a a).add o).add u).scale (-1)
  | 2 => Rep.mul b c a (o.add u)
  | 3 => (Rep.mul b c o u).scale (-1)

theorem eval_initialRep (b c d e j w z : ℝ) (hz : z^3=b*z+c) (n : Fin 4) :
    (initialRep b c d e j w n).eval b z =
      rawMoment z (variance b d e z) (skew b d e j w z) n := by
  fin_cases n <;> simp [initialRep,Rep.eval_add,Rep.eval_scale,Rep.eval_mul _ _ _ hz,
    eval_X,eval_V,eval_S,eval_unit,rawMoment] <;> ring

theorem raw_step (b c d e j w z : ℝ) (hz : z^3=b*z+c) (n : ℕ)
    (u0 u1 u2 u3 : Rep)
    (h0 : u0.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) (n+3))
    (h1 : u1.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) (n+2))
    (h2 : u2.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) (n+1))
    (h3 : u3.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) n) :
    (linear4 b c (recRep b c d e j w 0) (recRep b c d e j w 1)
        (recRep b c d e j w 2) (recRep b c d e j w 3) u0 u1 u2 u3).eval b z =
      rawMoment z (variance b d e z) (skew b d e j w z) (n+4) := by
  rw [eval_linear4 _ _ _ hz, h0,h1,h2,h3,rawMoment.eq_5]
  simp only [recRep,Rep.eval_add,Rep.eval_scale,Rep.eval_mul _ _ _ hz,eval_X,eval_V,eval_S]
  ring

end SparseCubes.Chart

namespace SparseCubes.Chart.Chart0


variable (b c d e j : ℝ)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r0 (b c d e j : ℝ) : Rep :=
  ⟨(e*(54 + (j*6))),(12 + (j*6)),0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r1 (b c d e j : ℝ) : Rep :=
  ⟨(((e*(e*(-891 + (j*(-198 + (j*(-11))))))) + (d*30)) + (b*(-54 + (j*(-54 + (j*(-11))))))),(e*(-456 + (j*(-252 + (j*(-22)))))),(-84 + (j*(-54 + (j*(-11)))))⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r2 (b c d e j : ℝ) : Rep :=
  ⟨((((e*(e*(e*(4374 + (j*(1458 + (j*(162 + (j*6))))))))) + (d*(e*(-810 + (j*(-90)))))) + (c*(288 + (j*(252 + (j*(66 + (j*6)))))))) + (b*(e*(1278 + (j*(1260 + (j*(294 + (j*18))))))))),(((e*(e*(4536 + (j*(2556 + (j*(390 + (j*18)))))))) + (d*(-180 + (j*(-90))))) + (b*(108 + (j*(162 + (j*(66 + (j*6)))))))),(e*(2088 + (j*(1350 + (j*(294 + (j*18)))))))⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r3 (b c d e j : ℝ) : Rep :=
  ⟨(((d*((e*(e*(4374 + (j*(972 + (j*54)))))) + (d*(-81)))) + (c*(e*(-3456 + (j*(-2916 + (j*(-738 + (j*(-54)))))))))) + (b*(((e*(e*(-5670 + (j*(-4914 + (j*(-963 + (j*(-54))))))))) + (d*(270 + (j*(270 + (j*54)))))) + (b*(-81 + (j*(-162 + (j*(-99 + (j*(-18))))))))))),((((e*(e*(e*(-8748 + (j*(-3402 + (j*(-432 + (j*(-18)))))))))) + (d*(e*(2268 + (j*(1242 + (j*108))))))) + (c*(-432 + (j*(-432 + (j*(-153 + (j*(-18))))))))) + (b*(e*(-1188 + (j*(-1674 + (j*(-630 + (j*(-54)))))))))),(((e*(e*(-10044 + (j*(-5886 + (j*(-1017 + (j*(-54))))))))) + (d*(432 + (j*(270 + (j*54)))))) + (b*(j*(-162 + (j*(-99 + (j*(-18))))))))⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m0 (b c d e j : ℝ) : Rep :=
  ⟨1,0,0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m1 (b c d e j : ℝ) : Rep :=
  ⟨0,3,0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m2 (b c d e j : ℝ) : Rep :=
  ⟨((d*9) + (b*9)),(e*9),0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m3 (b c d e j : ℝ) : Rep :=
  ⟨(((d*(e*(81 + (j*9)))) + (c*(-54 + (j*(-9))))) + (b*(e*(81 + (j*9))))),(((e*(e*(81 + (j*9)))) + (d*(81 + (j*9)))) + (b*27)),0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m4 (b c d e j : ℝ) : Rep :=
  ⟨(((d*((e*(e*(729 + (j*(162 + (j*9)))))) + (d*189))) + (c*(e*(-864 + (j*(-162 + (j*(-9)))))))) + (b*(((e*(e*(1161 + (j*(270 + (j*18)))))) + (d*(486 + (j*(108 + (j*9)))))) + (b*81)))),((((e*(e*(e*(729 + (j*(162 + (j*9))))))) + (d*(e*(1350 + (j*(270 + (j*18))))))) + (c*(-216 + (j*(-108 + (j*(-9))))))) + (b*(e*(486 + (j*(108 + (j*9))))))),9*(Certificate.w0G0 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m5 (b c d e j : ℝ) : Rep :=
  ⟨(((d*((e*(e*(e*(6561 + (j*(2187 + (j*(243 + (j*9))))))))) + (d*(e*(5346 + (j*594)))))) + (c*((e*(e*(-11502 + (j*(-1971 + (j*(-108))))))) + (d*(-3240 + (j*(-378 + (j*(135 + (j*9)))))))))) + (b*((((e*(e*(e*(16281 + (j*(5211 + (j*(621 + (j*27))))))))) + (d*(e*(12960 + (j*(4428 + (j*(513 + (j*27))))))))) + (c*(-1944 + (j*(-810 + (j*(-135 + (j*(-9))))))))) + (b*(e*(2430 + (j*(810 + (j*(135 + (j*9))))))))))),((((e*(e*(e*(e*(6561 + (j*(2187 + (j*(243 + (j*9)))))))))) + (d*((e*(e*(21627 + (j*(5805 + (j*(621 + (j*27)))))))) + (d*(2835 + (j*594)))))) + (c*(e*(-5184 + (j*(-3024 + (j*(-378 + (j*(-18)))))))))) + (b*(((e*(e*(10125 + (j*(3834 + (j*(513 + (j*27)))))))) + (d*(2430 + (j*(810 + (j*(135 + (j*9)))))))) + (b*243)))),9*(Certificate.w0G1 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m6 (b c d e j : ℝ) : Rep :=
  ⟨(((d*((e*(e*(e*(e*(59049 + (j*(26244 + (j*(4374 + (j*(324 + (j*9)))))))))))) + (d*((e*(e*(115911 + (j*(25758 + (j*1431)))))) + (d*4941))))) + (c*(((e*(e*(e*(-150336 + (j*(-19440 + (j*(1215 + (j*(324 + (j*18))))))))))) + (d*(e*(-127332 + (j*(-24786 + (j*(3942 + (j*(810 + (j*36))))))))))) + (c*(10368 + (j*(5832 + (j*(216 + (j*(-162 + (j*(-9))))))))))))) + (b*((((e*(e*(e*(e*(234009 + (j*(91368 + (j*(14553 + (j*(1134 + (j*36)))))))))))) + (d*((e*(e*(305694 + (j*(134136 + (j*(20061 + (j*(1458 + (j*54)))))))))) + (d*(25515 + (j*(10692 + (j*1431)))))))) + (c*(e*(-72900 + (j*(-38394 + (j*(-7236 + (j*(-486 + (j*(-18)))))))))))) + (b*(((e*(e*(69255 + (j*(37422 + (j*(8235 + (j*(810 + (j*36)))))))))) + (d*(10935 + (j*(4860 + (j*(1215 + (j*(162 + (j*9)))))))))) + (b*729)))))),((((e*(e*(e*(e*(e*(59049 + (j*(26244 + (j*(4374 + (j*(324 + (j*9))))))))))))) + (d*((e*(e*(e*(349920 + (j*(117126 + (j*(15984 + (j*(1134 + (j*36))))))))))) + (d*(e*(111051 + (j*(36450 + (j*2862))))))))) + (c*((e*(e*(-120528 + (j*(-70956 + (j*(-10395 + (j*(-648 + (j*(-18))))))))))) + (d*(-25272 + (j*(-16524 + (j*(-1647 + (j*(162 + (j*9)))))))))))) + (b*((((e*(e*(e*(199584 + (j*(97686 + (j*(17199 + (j*(1458 + (j*54))))))))))) + (d*(e*(94770 + (j*(48114 + (j*(9666 + (j*(810 + (j*36))))))))))) + (c*(-4536 + (j*(-4860 + (j*(-1215 + (j*(-162 + (j*(-9))))))))))) + (b*(e*(10935 + (j*(4860 + (j*(1215 + (j*(162 + (j*9))))))))))))),9*(Certificate.w0G2 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m7 (b c d e j : ℝ) : Rep :=
  ⟨(((d*((e*(e*(e*(e*(e*(531441 + (j*(295245 + (j*(65610 + (j*(7290 + (j*(405 + (j*9))))))))))))))) + (d*((e*(e*(e*(2283228 + (j*(761076 + (j*(84564 + (j*3132))))))))) + (d*(e*(267543 + (j*29727)))))))) + (c*(((e*(e*(e*(e*(-1864782 + (j*(-72333 + (j*(102222 + (j*(18441 + (j*(1377 + (j*45)))))))))))))) + (d*((e*(e*(-3452544 + (j*(-820368 + (j*(83187 + (j*(32805 + (j*(2754 + (j*90)))))))))))) + (d*(-132678 + (j*(23085 + (j*(30051 + (j*3132)))))))))) + (c*(e*(513216 + (j*(335016 + (j*(30132 + (j*(-7074 + (j*(-972 + (j*(-36)))))))))))))))) + (b*((((e*(e*(e*(e*(e*(3523257 + (j*(1607445 + (j*(307638 + (j*(31806 + (j*(1809 + (j*45))))))))))))))) + (d*((e*(e*(e*(6910920 + (j*(3657636 + (j*(693603 + (j*(62775 + (j*(3186 + (j*90))))))))))))) + (d*(e*(1321677 + (j*(742365 + (j*(144666 + (j*9396))))))))))) + (c*((e*(e*(-2204496 + (j*(-1380240 + (j*(-295569 + (j*(-21519 + (j*(-432))))))))))) + (d*(-265356 + (j*(-173502 + (j*(-43092 + (j*(-2862 + (j*(378 + (j*18)))))))))))))) + (b*((((e*(e*(e*(1803060 + (j*(1249344 + (j*(336879 + (j*(42201 + (j*(2754 + (j*90))))))))))))) + (d*(e*(586845 + (j*(403137 + (j*(123039 + (j*(18171 + (j*(1161 + (j*45))))))))))))) + (c*(-39366 + (j*(-25515 + (j*(-8505 + (j*(-1701 + (j*(-189 + (j*(-9))))))))))))) + (b*(e*(45927 + (j*(25515 + (j*(8505 + (j*(1701 + (j*(189 + (j*9))))))))))))))))),((((e*(e*(e*(e*(e*(e*(531441 + (j*(295245 + (j*(65610 + (j*(7290 + (j*(405 + (j*9)))))))))))))))) + (d*((e*(e*(e*(e*(5806485 + (j*(2368521 + (j*(392202 + (j*(34938 + (j*(1809 + (j*45)))))))))))))) + (d*((e*(e*(3236760 + (j*(1391175 + (j*(199179 + (j*9396)))))))) + (d*(103761 + (j*29727)))))))) + (c*(((e*(e*(e*(-2824632 + (j*(-1647216 + (j*(-272160 + (j*(-17442 + (j*(-432)))))))))))) + (d*(e*(-1253880 + (j*(-992412 + (j*(-166293 + (j*(-621 + (j*(1161 + (j*45))))))))))))) + (c*(31104 + (j*(57024 + (j*(21546 + (j*(1431 + (j*(-189 + (j*(-9))))))))))))))) + (b*((((e*(e*(e*(e*(3941703 + (j*(2296188 + (j*(494424 + (j*(53379 + (j*(3186 + (j*90)))))))))))))) + (d*((e*(e*(3020976 + (j*(1961982 + (j*(481545 + (j*(51597 + (j*(2754 + (j*90)))))))))))) + (d*(178605 + (j*(112266 + (j*(30051 + (j*3132)))))))))) + (c*(e*(-227448 + (j*(-322380 + (j*(-106029 + (j*(-14769 + (j*(-783 + (j*(-27)))))))))))))) + (b*(((e*(e*(408240 + (j*(290871 + (j*(92988 + (j*(15039 + (j*(1161 + (j*45)))))))))))) + (d*(45927 + (j*(25515 + (j*(8505 + (j*(1701 + (j*(189 + (j*9)))))))))))) + (b*2187)))))),9*(Certificate.w0G3 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m8 (b c d e j : ℝ) : Rep :=
  let t := linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j)
  ⟨t.u,t.l,9*(Certificate.w0G4 b c d e j)⟩


end SparseCubes.Chart.Chart0

namespace SparseCubes.Chart.Chart0


variable (b c d e j : ℝ)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec0 : r0 b c d e j = recRep b c d e j 0 0 := by
  apply rep_ext <;> simp only [r0,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec1 : r1 b c d e j = recRep b c d e j 0 1 := by
  apply rep_ext <;> simp only [r1,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec2 : r2 b c d e j = recRep b c d e j 0 2 := by
  apply rep_ext <;> simp only [r2,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec3 : r3 b c d e j = recRep b c d e j 0 3 := by
  apply rep_ext <;> simp only [r3,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base0 : m0 b c d e j = initialRep b c d e j 0 0 := by
  apply rep_ext <;> simp only [m0,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base1 : m1 b c d e j = initialRep b c d e j 0 1 := by
  apply rep_ext <;> simp only [m1,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base2 : m2 b c d e j = initialRep b c d e j 0 2 := by
  apply rep_ext <;> simp only [m2,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base3 : m3 b c d e j = initialRep b c d e j 0 3 := by
  apply rep_ext <;> simp only [m3,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step4 : m4 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m0,m1,m2,m3,m4,Certificate.w0G0] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step5 : m5 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m1,m2,m3,m4,m5,Certificate.w0G0,Certificate.w0G1] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step6 : m6 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m2,m3,m4,m5,m6,Certificate.w0G0,Certificate.w0G1,Certificate.w0G2] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step7 : m7 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) := by
  apply rep_ext <;> simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m3,m4,m5,m6,m7,Certificate.w0G0,Certificate.w0G1,Certificate.w0G2,Certificate.w0G3] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step8 : m8 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) := by
  apply rep_ext
  · rfl
  · rfl
  · simp only [linear4,Rep.add,Rep.mul,r0,r1,r2,r3,m4,m5,m6,m7,m8,Certificate.w0G0,Certificate.w0G1,Certificate.w0G2,Certificate.w0G3,Certificate.w0G4] <;> ring


end SparseCubes.Chart.Chart0

namespace SparseCubes.Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def bn (digits : List Nat) : Nat := digits.foldl (fun a k => a * 2^80 + k) 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0Den : Int := (bn [0xe41,0x1c00aa519120898ad1c9,0x7e8b1f79440747821db8,0x5685b3475efd86680000])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0NegH : Tower 5 :=
  [[[],[],[[],[],[],[[(27*w0Den)]]],[[[],[],[],[(27*w0Den)]],[[],[(81*w0Den)]]],[[[(-27*w0Den)]]]],[[],[],[[],[[],[],[(-27*w0Den)]],[[(27*w0Den)]]],[[[],[(54*w0Den)]]]],[[],[],[[[],[],[(-27*w0Den)]]]],[[[],[],[],[[(-4*w0Den)]]],[[[],[],[],[(-4*w0Den)]],[[],[(-12*w0Den)]]],[[[(4*w0Den)]]]],[[[],[[],[],[(4*w0Den)]],[[(-4*w0Den)]]],[[[],[(-8*w0Den)]]]],[[[[],[],[(4*w0Den)]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0P0 : Tower 5 :=
  [[[[[], [], [48, 12, 1]], [[12, 12, 1]]]], [[[[-12]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0P1 : Tower 5 :=
  [[[[[], [], [], [1080, 336, 42, 2]], [[], [252, 360, 57, 3]]], [[[72, -24, -15, -1]]]], [[[[], [-324, 24, 15, 1]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0P2 : Tower 5 :=
  [[[[[],[],[],[],[19440,7236,1131,90,3]],[[],[],[8208,9180,1911,162,6]],[[1188,1188,159]]],[[[],[3024,-756,-621,-72,-3]]]],[[[[],[],[-5184,1296,756,90,4]],[[-432,540,135,18,1]]]],[[[[-468]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0P3 : Tower 5 :=
  [[[[[],[],[],[],[],[332424,145800,26892,2724,156,4]],[[],[],[],[260496,237276,58275,6279,354,10]],[[],[57672,72576,16074,1044]]],[[[],[],[69336,-31104,-21042,-3018,-177,-5]],[[0,-12204,-5733,-507,21,1]]]],[[[[],[],[],[-53352,54252,28035,4341,306,10]],[[],[-23976,34884,13671,2019,129,5]]],[[[6912,468,-945,-189,-21,-1]]]],[[[[],[-24624,-468,945,189,21,1]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0P4 : Tower 5 :=
  [[[[[],[],[],[],[],[],[5668704,2913084,627669,74844,5454,240,5]],[[],[],[],[],[7584516,6318972,1771389,232812,16236,660,15]],[[],[],[2154600,2988576,886356,103788,4374]],[[79272,79272,13662]]],[[[],[],[],[1111536,-1316520,-729270,-119628,-8217,-270,-5]],[[],[51840,-826848,-478980,-72288,-2286,174,6]]],[[[-24192,6912,20736,6840,477,-24,-1]]]],[[[[],[],[],[],[293004,2052432,979128,179172,15993,780,20]],[[],[],[-649296,1611576,821070,153792,12879,510,15]],[[30456,99792,40068,8352,729]]],[[[],[452736,37152,-93636,-27288,-3042,-126,-4]]]],[[[[],[],[-865080,-30456,78570,21960,2817,174,6]],[[-38664,13608,5670,1512,252,24,1]]]],[[[[-14040]]]]]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0C0 : Tower 5 :=
  [[[[[],[],[],[],[],[],[],[],[],[],[-(bn [0xbc247dc685,0x9f1124def16f76c0c420,0x3483d23b3aa9fa944dd8,0xbb2b5a8371d999988c80]),-(bn [0xcb6dda226,0x37d672c7c1b30e663cd5,0xd49c0164fd54c73fd5cc,0x80a241f59272a1ed2400]),(bn [0x2dccf362a1,0x89c98f140128a39fe632,0xc49fa5a6c9843b179d2c,0x13e4c352b6862e85dca0]),(bn [0x156179a01a,0x7688674e1380b77c7ca1,0x52fec3322559a73bfbae,0x1291f54d6f3f51dd34b0]),(bn [0x5a4e88239,0xb26269ecf2159e581e01,0xfa59c31d9c9ff2306717,0x110482e4af3d64644f60]),(bn [0x13c4a6859,0xc19f92f76f5aa2860192,0x55c363fb47a41516e8f6,0xa930d433f2c694754b8c]),(bn [0x3d087e16,0xeedbf67002bea3ed75ae,0xe4365c07e74cc377bb65,0x4b5652b6714840f9ce88]),(bn [0x9207b01,0xc64b8e88045033ca4fed,0x1a6d4326d60c954441e0,0x67fc69c74363e7ab4ba4]),(bn [0xf642eb,0x54c32a871d01e428c27e,0x836b4c97e9e67e6a15e9,0x8168d6f0b6704354208e]),(bn [0x112883,0x5e48ccab7c9fb91a15a5,0x17630f6af95007020b8e,0x503a1ca10815bddfda06]),(bn [0xb701,0xf17d7e7c5bf792ff0d60,0x7fdef8009f7af7a25ba0,0xcf84941bba174691284e]),(bn [0x38f,0xb7574c651ce7fa66e011,0xfc364b77db3d3dbbe6ca,0xaf4bc6add9696abdda1e])]],[[],[],[],[],[],[],[],[],[-(bn [0x1079a808e2a,0xe436d91324a68818b290,0xf68d4023afd3b6ec814b,0xc6812753bfe4e1846000]),(bn [0x184a77452b,0xae4b645aa9fe09f189eb,0xbb3e08eb9d6c38314f18,0x8b1313b5fcf54d411e80]),(bn [0x70bd490c12,0x14da2cfa130608be9999,0x4e67f1bf99de951406dd,0x1e8e18e86aece2fe90e0]),(bn [0x390d30b007,0x71c0df6a698c419f3a39,0xd903fd6a4f0c5ac00591,0x38c164de35e4c81e96b0]),(bn [0x10607c2d59,0x5ddb49731d6411674bbf,0x62d475459fea19028c47,0xecb69add102652882738]),(bn [0x3997c5579,0x72fe8679806f1898a94c,0x2ba0d8d98b9dbd71a051,0x7635ea6277934178c17c]),(bn [0xa9888167,0x153e06fc6e3ca2e3b019,0x347e1442b29a1a5ad130,0xff09ed7abc0810f86324]),(bn [0x18a851ad,0xc92f92af44cae29d033a,0x75fbfb1f2cc100e1f393,0x64b549ce938b58c02186]),(bn [0x2964755,0x113026b8d700098b7aea,0x7f5856ec9909d1057a71,0x79319f2a3ccc33a1a527]),(bn [0x2e81eb,0x53df0d2963bd52931851,0xb2d793867e1067cfa222,0x7ee75bbfd3b6f24be4fb]),(bn [0x1f363,0x1d6efd78264329b80c68,0xa95b7e3e8aeda54c250f,0x6b303b36a84ccba3d3f7]),(bn [0x9af,0x910b0ecd5bce1a416f33,0x5ff6c91997a117e923fd,0x5f4a3bb6ec2a32974dd9])]],[[],[],[],[],[],[],[-(bn [0x230a47add,0xc63b6a3d175906a98c60,0x104936abd1c6fd673787,0xa53ff6372988ec642580]),(bn [0x2016813503,0x1a1cb9385512232baeae,0xc7b0561e02a6b3c47062,0xf5ed08bdee0fdbb49880]),(bn [0x4a8154691f,0x710fbbd5e2ed99b77221,0xe977a17f8e19e7ac85d0,0x11ca12e6b2e424b81c0]),(bn [0x2d9a63cde8,0x209bc773065767bbc25f,0x85ce916a0d16002fb1d2,0x734b20b4115586e0b30]),(bn [0xec3751195,0x5557dde294fe0f711f88,0xdcddcc714bcbdb3d7d60,0xc39a26d93fbe14e40878]),(bn [0x357083c73,0xb8588f98dd9f0d5eb6fa,0x23c18552a884bcab2ed5,0xb246c666288282cdab24]),(bn [0x985ebf4d,0x7cebe66f356d8d577477,0x11b11a989cfce68ec303,0xee15f8788785bddc0e80]),(bn [0x158f4759,0x39c07120cd74364826b,0x7a3af92137d19764b72a,0xb0894cd0b0e17886610]),(bn [0x23cb6c9,0xd2ef88a68a44f5318367,0x7fde87529d056fd2d811,0x73612b826ebdfa2d2fac]),(bn [0x280c92,0x17bc2b070cadba693120,0xd548f59a456d2a209200,0xe62550f2de6e3b07b384]),(bn [0x1aabe,0xe6949663b49a0a992fad,0x25371b57243e70248277,0x7945f29adb01a9f53de4]),(bn [0x818,0x25528aea2e120d1a6bc1,0xec85c1cc0c30f4508710,0x9214ce9cddb4790e27f8])]],[[],[],[],[],[(bn [0x22194aa3b4,0x6e5ea6aa7fee71413a91,0x91febd1c8f281d7f4d3e,0x3005d74aa38de465ae00]),(bn [0x16620155e6,0x2c7b3abad1fbc3d3397e,0x58d517f05d09ff59c431,0xa578d5333e13501d9100]),(bn [0xcd410d269,0x3ace2282a15e61603ecf,0x5bb0ea61e5428e8f2715,0xb9f05f8b749aec1cb640]),(bn [0x9d1d13774,0xe6cc948e302780b53443,0x717e94e91dcf19f86756,0xe0350484358036de6490]),(bn [0x4180e8034,0x8f014b4c054a94882c06,0xa3328cdacce60a5cfa18,0xb747df4f9665be1db780]),(bn [0xfb39427f,0xbcd4b9d69d268efef3e2,0x3280bebd55af82f17bdd,0x805ef669113770f3e314]),(bn [0x2be355db,0x5e2f885a238135307a42,0xbf690d2559fd434cd6de,0x9917b90562a773b5bf04]),(bn [0x6114b7f,0x4b196287ee4d5dbb4d48,0xaa5288d77d4ed08218d,0xa0f0eefcb4f051a1bee]),(bn [0x9e1bc7,0xe515a5304b11fa865e3,0x4355d4fa91630cfcf8fa,0x8b60af9fca9ffd7813c3]),(bn [0xacb71,0x72234289f0d101b6eb92,0x6580785f566b89450d67,0x5024c199fc4047a1ccff]),(bn [0x6fc4,0xf4f4fef944e3fb518679,0xbf9e8ac604b877a4ecdc,0xe6b5b5dd4c9359d91e6b]),(bn [0x20a,0x9d01b4e00cbaadb3de6e,0x6f333d5753bc643701b4,0x2ec0d41c67cc4800be2d])]],[[],[],[(bn [0x1b02e69,0xa13b6f07e64b11b6bd05,0xfcb6e5833170cf1bb03,0xb10df4bb31b05efe4000]),(bn [0x218e70b,0xcd27358d768c39d5683e,0x1e583822c5900949db42,0x9be61fae8c808e1ee000]),(bn [0x1a35b21,0x73164637da0e6ccc81d8,0xbf7937919a744dff2874,0x1abe1de690ae334b2000]),(bn [0xf06dd3,0x3f0f52f2a2029e2c3b9a,0x8764485ed7ab72c050a7,0xee3b85805d999b3cf00]),(bn [0x54f4cf,0x374c935e63bc7d828cd2,0x1dc15e33f10af259ac5f,0x73cd056adb08ecbf0a00]),(bn [0x14cd58,0x1edb01b6ca4224ef6e69,0xcdf79798ac40046227b8,0xbb8df80d5f369f01d8c0]),(bn [0x3c3bc,0x8985a2d0b75fc0b933cb,0x947ecbf3e1de33539c76,0x8d71c0ac2c21717d8b80]),(bn [0x7cc9,0x1230cf0397fa36694953,0xc196f044cdba94d14e52,0xf14ee147d99c397bd9e0]),(bn [0xb19,0x422e84a0eb84676bc3a1,0x5d22c368d7db96d9a49a,0x8ac3f31ace85a570310]),(bn [0xa2,0x552b94a2274472d78536,0x1d862d2e209efb2606a,0xd06985e6487114ef850]),(bn [0x5,0x4299ae05acb59930f9e3,0x76616ff7558fddd7a284,0x6323c4fc5977759241d0]),(bn [0x1254ac2f80f1af09d249,0xe06a46bc905e06562289,0xd7ae97ec019a2d91cb0])]],[[-(bn [0x8f1e,0xfc8baf29595ea2049783,0x89175cf994f7851a0a4,0x8443877f6ee7f8820000]),-(bn [0x176ab,0xf10b3cfb452c86c02e4,0xc1c308e5b540c213032,0xc28a0243cada8e750000]),-(bn [0x1994c,0x68d7e07672e8676e88ab,0xe699989495a82eae4f1,0x46992802dd0f834c0000]),-(bn [0xd80c,0xb47260f9acd52999081,0x7e41e694c7e27578df7c,0x8220eb3078c08d7ac000]),-(bn [0x3d99,0x55ecace0f38dcb68f31d,0x2551b4fbfa5c707e2a23,0x69c06ff66c346a591000]),-(bn [0xb20,0x1bd27457fb09dd6ddcd3,0x55adbe043b49788fb941,0xfb9705e447a3c4225000]),-(bn [0x17b,0xd77984f17793368eee89,0xf4206566b71f62cf5014,0x89019a4264fff600f800]),-(bn [0x24,0xa40461b7fc82393a18ce,0xc4ed2b606123f01ecbfa,0xf4fd764e35a092a10400]),-(bn [0x2,0x9668753099505878927,0x89d6ec9813173e72317e,0x63d082b3d2c90e2faa00]),-(bn [0xc91d364e3193baf86ae,0x3679d286de307a9d79f3,0x1b5b4d8f389a9412fc00])]]],[[[],[],[],[],[],[],[],[(bn [0x3ccabd7c95,0x5f9a2b8dc77af2fb1c1f,0x3c92b8ab66cd88ef0d5b,0x4a78bf9f6ed40c26fa80]),(bn [0xe4029b5bb,0xa25b1aa08457910b6830,0xe46d3ad7da5cb9409625,0xe0e836ceeb05dbff2a00]),-(bn [0x382feb2f,0xa6f45a12fb0a1414c8dc,0xfa268ee6de0ec7293703,0x95d89a53e22907aae040]),(bn [0xb9461273,0xee2011c62e2a30b99c84,0x56fc84d6b9b49242dd28,0x5685d55fb3435f8be460]),(bn [0x9f85cbd,0x191a822595a48f60fbac,0x8bd4c19174c83e135b70,0x9e0a3e92221f1b216e8]),-(bn [0x1b803234,0x4cab788d0fb72f6e234c,0x657385ef45543f7ab4e7,0x73bca8621029f6e3c20]),-(bn [0xb4985dc,0x70c233357805c79cdd33,0xaf2b7df37ab5101ccb3a,0xdef5791274bd04720f6c]),-(bn [0x249b4e1,0xf5e7eee992778237cacf,0x513d0f9cd44e37b0812c,0x5bdc9400ffd46b41e62]),-(bn [0x4ac3c9,0x6c0c4ab40c8152fbc76c,0xb059a668631ff21c95cf,0x76b733853a8384c4032d]),-(bn [0x62189,0x963cd77df67ec559f6d1,0x5dd3d6a03fa0aa2dadb4,0x3b39866385b613ecba09]),-(bn [0x4cad,0xffe1e526f84d4fcbebbc,0xbf6a74468232c2b9275e,0x7254c0b51e7bcb6c08d]),-(bn [0x1b3,0xa2949da0ba93b0dab2b3,0xf2632d8566fc164bd281,0x3f272a85d5d8fe3540bf])]],[[],[],[],[],[],[(bn [0x5464de52a5,0x7fe84aee88727fd478f7,0x16c8a7440d224ff7a137,0x641d98b9c6d3c17f0780]),(bn [0x22a0e483e,0x5cbb601311aa40edc192,0x1f0171da42579758cccb,0x5ae56c038fa43da3fd00]),-(bn [0x2fd0ef063,0xc2da2c3a1901c7c1bb1c,0x122e72f7cce068fcd3d4,0x5d52016ef533d1b42680]),(bn [0x9344795b,0x359b1dd8595408997c3d,0x954700713b475f137f8c,0x31fae81de06ce0051bb0]),-(bn [0x1ed206ab,0x2a293c43928b394c2c2e,0xb544b77f8f61e7d9d9cc,0x651ccd3cffce89e31d38]),-(bn [0x2db0f5a8,0xa1fddc94837edee24a29,0x39b15502d5b1e5e7a18b,0xfccda27252679c7dfbc0]),-(bn [0x10db865c,0xf99e066cf6fb5a719c74,0x4fc64b8f485d5d59ee5b,0xf0dee8f21ddf279a8bf8]),-(bn [0x3679714,0x17cdf9ac3b0086a70946,0xff1bc5438348944a3137,0x477af5345f13d0f50394]),-(bn [0x6f51ca,0x5f350aa55a9920a9d863,0x2e325ae196086e848f8c,0xbdc3989ea9943910b622]),-(bn [0x913cf,0x4d1517bf538574213ad1,0x620cf1f0c27bc7f8477a,0xa3f001f3df94f6fad312]),-(bn [0x6ec4,0xa20c461cab26450fe919,0x16426d6c8a98e9a99680,0xf4c7c9e76e66908f4f9a]),-(bn [0x258,0x98adfd1d0f35a4854f5,0x123bb7b57b584c746dc8,0x6565516a45aefe0bd7e])]],[[],[],[],[-(bn [0xb58410277,0x7bf32cf5507438d4a3f8,0x8bbd35425725cc04665d,0x831c1f81243fe69ca300]),(bn [0x37dd3c44d,0x725e796151fc5bbc15ba,0x3bd37787af3a5a8099b5,0x2aa7adcf4ebb52feca80]),(bn [0x303936c8b,0x2e70f47cf3ca62fff706,0x7349e8ae8b322f734f16,0x70a581c657aaf1b5fb60]),(bn [0x445a92bb,0xf6022eeb5136fc8b3aa9,0x3e874d90bb6cfc156854,0xb6633520a44c039873e0]),-(bn [0x2777f1af,0x828c1fb097fd602c5d57,0x3a4ca6386fe056588c4,0xf0921dc4a9c516e18d0]),-(bn [0x15c72ef5,0x2dd5311b31980bd387a5,0xfb25bf093797c2810064,0xf051b07e3b54d716e390]),-(bn [0x66fada4,0x224f7404d7fdbf76a4ff,0xbaa6addd36987bf9347a,0x36b02da9c15ed9f0d95c]),-(bn [0x138ee12,0x281c69f5f2cf4c880edb,0x97457ff8917dd1908417,0x18b00e65e7d4f5d98952]),-(bn [0x267fd1,0x69e15916085309a400da,0xad83d1bbf441c7bda99e,0x53be83596bcd85f1c7c5]),-(bn [0x2fe90,0xf8535c43e6e81bc3edd8,0xd12186960ee40456a266,0x82aec5275183ecc8c619]),-(bn [0x2287,0xec9332c4ef2f9ac66689,0x42a81e78c68f1cf11074,0x88c5fff80cd8cbb782dd]),-(bn [0xae,0x3181a8db1377a34f1cb2,0x3c6116dd1575aa78d704,0xffb506de4f59fa3df32f])]],[[],[-(bn [0x44c4de,0x9ea8f235ca5c2c693c67,0xdda636cff256a6c6fece,0x2f24625885ed8bbf3000]),(bn [0x9dc33,0xf9e4e0344a59d1091752,0xcb71f7c5e7a2472b41db,0x9d42782cae076ba6b800]),(bn [0x1608a3,0x3e97941e7a31d5ed0db0,0x41fd12d29943a5236d44,0xa978cd843b94ba357e00]),(bn [0xf8996,0xb32f12a5ea44136d98b3,0xeac3d5d104eca9bd5f6b,0x28777a29a2ada4b55a00]),(bn [0x13250,0xba79342523850166b0b4,0x3f1182ce442fe93542f7,0x33c57dc1b85cfea64500]),-(bn [0x1a2b8,0x7a6658e9df2c12393ed0,0x3420a4fc02c60a148404,0x7cc4dd1fedcec2738300]),-(bn [0x9b1e,0x33009b925cde4fffa12c,0x41855bc61ab940c539d1,0xed45fc2d595b79e54580]),-(bn [0x1af2,0x86b3c9b2d3639e75bed0,0xff71db31ff9538ec3d5c,0xc7c88a700b14eff71820]),-(bn [0x2d2,0x240b8668a083a9a770eb,0xf2b3a4a2dbf66481c5ab,0x40462a3ba818efa53bf0]),-(bn [0x2e,0x6e660df000eb1cd5f275,0x10e7b20c306d6185a297,0x34a73d5957dca2e077b0]),-(bn [0x1,0xa4c6f44d0173d4410d5b,0xbb9e04324c29c5ab6ba5,0x5844bc78fabc7b0c7db0]),-(bn [0x607fc7e4b5d4876182a,0xd9c20e3458962e6c396f,0xc72390f76ffab1538590])]]],[[[],[],[],[],[(bn [0xdf512159,0x9dc11a281e2de711c5c2,0x10c807199955c2bd44e0,0x15c6e19b1cf3a150000]),(bn [0x18e97784,0xdfa0f2f2f62df359fec8,0x6419f2b58885188483d9,0x982909a13b7abe5ee380]),-(bn [0x1dd07da2,0xc8bb8052e4dda00f636b,0xd07d72bc400dcb30ab98,0x3231ec7f38eafd287fa0]),-(bn [0x76e0987,0xd4923da1ddcd96b80f31,0x36fedec68783c90a525,0x42b4629198b956cb0d10]),-(bn [0xf191b3,0xef52e9866def48c595ba,0xd5e6f01dd8dbbb8d23ec,0x288d09f6d1d0d0de8050]),-(bn [0x1695f0,0xf6b32a3ee4fe1188e91d,0x61837e2248941aa6de4a,0x78f388ac9940f8164d50]),-(bn [0x1b57f,0x7ac08958dab62f235e43,0x78275107d3e28079b0f7,0x7494ed9247c6cc2853b0]),(bn [0xdddb,0x73f571efbd0abe1cf848,0x1233e5b3d149a6a5d698,0x91f96c299b2c1d33fae0]),(bn [0x4ec0,0xb8b99677ad8d5be91b38,0x4141f4e37471e85a2ca5,0xd002ed5fe0e95ae5a740]),(bn [0xb88,0x2c9b8e22688a8ac86aeb,0x51039faa4dd30f1d0de4,0xaec51eb7d6e901c1fcc0]),(bn [0xf2,0x5273d5270e41a1e8c71e,0xc3dca5f464bc64a9f2b8,0xaf41b4945e2c7f3c0840]),(bn [0x8,0x7a8ad602eae25ffecd3d,0xc33d33f7cb0dfdd992fe,0xcdcd45b3cbe19cb3fc60])]],[[],[],[(bn [0x2a9870,0x29f329c677c2ff1b34ac,0x360171c5c13da59dc7b2,0xf13485e6252adc7d4000]),(bn [0x130255,0x662f6dd4205da28217b6,0x3ecae421fd259b1edcbe,0x32ff016c09ce058a2800]),(bn [0x24a4e,0xb9769cfd11a3cc7dbf0a,0x9de441e5286e8d34e9d3,0x973f13b5c89cc22d4a00]),(bn [0x3bdbf,0x9247eb3605caf4994e9f,0x6318408f40810d69482a,0xaf728c269b037719100]),(bn [0xf80f,0x94368057b6ef78e4d729,0xf051bffcc2b3da5668a6,0x2a12eb0adcf63d070500]),(bn [0x25aa,0x67f46d9196d419b03ab2,0x2e1e21c6f8ad5b42af79,0x998b523f43c2707fcd00]),(bn [0x337,0x6bb51aa2a1829376887b,0xb14cef3069acf2669ce9,0x89efd275ed99f65a4300]),(bn [0x31,0x6721d082124f33c167b,0xb4fbecf92fcc20f921f8,0xb7f6ba48aa070f060800]),(bn [0x3,0x1c3cd8a4a62542723edb,0xdf696eadf04ea5cde6ce,0x19cc754bd9ab3edf7400]),(bn [0x22e15876613b515ee22a,0x33550eb9a7d47d0278a0,0x4796c23a54bf99f00400]),(bn [0xbaf23b368909d38dfd,0x4d1882bec0bd7b592e2a,0x9851a9ac9af479546800])]],[[(bn [0x529be,0xc046a3ebc078df914e18,0xdad968a3d06d28845b67,0xee61916a00fc7d5f4000]),-(bn [0x33ba5,0xc5b6d7cb0dcdf5e4e7ab,0x7b76d356c19b81a9bb06,0x84b5f2b3d621f654a000]),-(bn [0xc17c,0x5bcb0f74a7711f81db68,0x19078a68a55fe88b686d,0x170c41279d069fa12800]),(bn [0x5638,0xdcf7576972d11e8922a2,0x16213ce54b1b8a742be4,0x450cf26ebc479322a400]),(bn [0x2533,0xbbe6c0e5f900a53dead0,0x9b79c9d906f47a96a90b,0x3476721f9bf6b2a6e700]),(bn [0x5f1,0xbeb5461b10bb893dd483,0xd70585894bf09f804127,0x1a3f2466cd78f5f99b00]),(bn [0x9f,0xe50a53fbe35cbb4c9dd0,0x20a7b5b65eb96552d033,0x6c7972e7f5de5af59300]),(bn [0x10,0x3f092e3e33ff6a4aa2aa,0xc362b46e7e33551de4a9,0x101674af68e252cf7f00]),(bn [0x1,0x601ccfbfe75936292e17,0xf6ac8a658985f7f496eb,0x90cd792bcaabc3aa2200]),(bn [0x1170ac3b309da8af7115,0x19aa875cd3ea3e813c50,0x23cb611d2a5fccf80200]),(bn [0x5d791d9b4484e9c6fe,0xa68c415f605ebdac9715,0x4c28d4d64d7a3caa3400])]]],[[[],[-(bn [0x150d0,0xc629353c2943f83d81f2,0xfd52c2b0202198df949,0x1f31ef18e6bf86d30000]),(bn [0xcb2b,0x7b9f712ac335d9236f35,0x71a622cbcf17661a6d91,0xf548b464c0e49f720000]),(bn [0x2107,0x13870ae7b52b03a22f9c,0x9d16162a8aba4b477f2e,0xbe0536b5a1d6ebf5c000]),-(bn [0x3040,0x2be88b1c4157d219dca7,0xd6b83ea80e25de255eb8,0xfa6c495726f69190a000]),-(bn [0x12b1,0x4f932371f5c0ac83b744,0xe371c6e57ba78157cf44,0x68d5da68a5af2cae7800]),-(bn [0x341,0x77f038c99a1f122540b5,0xedcb3cb9e86f87167c36,0x6330b4d481fcfd034800]),-(bn [0x49,0x25fae5f309ad4d0af3f6,0xdb0a05e41442bb622607,0x8053f76047643e25800]),-(bn [0x3,0x92f60c3d0c98a05eaad7,0xcebbcba225abeb95acd5,0x4a3f7578fa8ebac75800]),-(bn [0x15e862f0640f26caa3af,0x8df525a9634747368fd,0xd991e23a28a637e43000])]]]],[[[[],[],[],[],[],[],[],[],[(bn [0xe6b4e3521,0xf859357c37301901d351,0xf7a8d9c36eacc0fe9daa,0x79e132692f6d20ce7b80]),-(bn [0xc8b70807,0x3eb7cc2e87eda104f756,0x5bcac8ef340990586203,0x6c71ddfe4562e7191200]),-(bn [0x3e698fe04,0x3250e25d213acbbc8f9c,0x2b2a0c9ea02fcf01a8f4,0xcbd5a7dab89871a71940]),-(bn [0x1255e8ccf,0xa78a30317c09238bc8a0,0x8415fd777defb6356d9a,0xd5b511db249b11d11070]),(bn [0xfec7709,0x68852503e2c2a9115c69,0x421fec0c82ef2c7a6131,0xba6f36daea0c412ed38]),(bn [0x22f3874d,0x2daa6e3d4f5372cc4d0b,0x34d031918a262a33bea1,0x77a3622ba706e786b714]),(bn [0xbd50220,0x18a4262446bb9a4119bb,0x14fc7013b1ea665e6352,0x8d6c65eaff84d1e527d4]),(bn [0x244513e,0x122bea64d5ec43aaa613,0x833eb9c8b261fc0735b4,0x6a3cd4e99fe69060ca66]),(bn [0x47ef09,0x67b218458462dd7b570b,0x8db0de78249df48b252c,0x585332aaf607eb4179cd]),(bn [0x5c8d9,0x8e69c7ec2ce90162730c,0xf66aeffe190669191301,0x7c06651347e293bd7ce9]),(bn [0x46ae,0xd9d737efce06f0a5204d,0x9c8db1eb693aa5a11e73,0xc75df77362314fecfa4d]),(bn [0x189,0xe40bce8b1e60e8a38858,0xa71dad1bdb66d1527ed,0x2b7bc6f8745679c1849f])]],[[],[],[],[],[],[],[(bn [0x17d8563f88,0x238cec6b03af464be7a6,0x752790255348dea9a8f1,0x3cab79b8af7ffc413480]),-(bn [0x5b8301d7b,0x9ad92de490d4c45ef34,0x10a3dffecd30402a4f77,0x9c61cd16b936fc59c700]),-(bn [0x7cc4d8870,0x809c6549dd04cf3e9dca,0x80a073d70b18d6c9f5d1,0x3ea16ba8395d581406c0]),-(bn [0x1e6f667e4,0x89c73d447d6243a09223,0x52e4c076953bcf688325,0x7277a4822a8108476800]),(bn [0x23709460,0x78e7c042e8d511c8f276,0x710aeb47b51f0165ecfb,0x13f1362b3e6a2618bf8]),(bn [0x366e7a7e,0xe811cc8d53869fa4e607,0xec1c0e314908f3a7ccb2,0x3dd6eb19b59151ccb138]),(bn [0x1202a0e1,0x4c839ce7226d57b74e31,0x72748793d3a3616e96f7,0xaba1a9a777bdcdc3d058]),(bn [0x370c620,0xd435c5f8a1b6689197d6,0xc3ec5d6684eb5be6dc04,0xf5fa8617a12d9a06bd7c]),(bn [0x6cdc95,0x19bedf71614a2d1e19fb,0x39db21fd4716dc33d57a,0x4edb254a239825294502]),(bn [0x8b30a,0x2bd81af148a30d68ad7,0x87e152f473879960e86a,0xb31b75c5092d20014a72]),(bn [0x67d3,0x85a8afb3b8010abef9be,0xc71f256a1f7eece07afb,0xa29c3ce3676ec6d101a]),(bn [0x225,0xd301de5036b3f3f07e8a,0xef72b0e4c9f79ccd232d,0x3401672eb08c898d7bfe])]],[[],[],[],[],[(bn [0x68cc5d2b1,0x41665521beceb4aa682,0x82438a83c12e822fd06,0xbaddbb8860f6877a5e00]),-(bn [0x295692020,0x13638dafe92a5a048625,0xb39920a98d51740d03d4,0x21aceae5304642279700]),-(bn [0x3b211277b,0xab4661777e48b7e9e026,0xefcfd3e40ea0f9ba0e4,0xf0109829f00d3816a40]),-(bn [0xe25abae1,0xd60ba0c19ff14e655c14,0x3628124b4ba7ed8c997,0x2a333079874802e523b0]),(bn [0x13a85993,0xc68b0c5e809a9910b725,0xc8400b83c8513787347e,0xd3f3fb58b582d6e13da0]),(bn [0x15bb542c,0x9ed100c8721a69727a37,0x8ccc35693eeed5473154,0x82e1837aad73eef5f604]),(bn [0x6c4afca,0xfc19267a1eb453f704e7,0x708cbe90a19be2abe08,0x10b665189d99048e19a4]),(bn [0x1423a63,0x851597c4013c4acff647,0xb85fbd2bfe0567c88dab,0xf923ce793e1409e1c5d6]),(bn [0x26e3c1,0xa654720e83ad5adb88e3,0x52fde3c914f2929dad02,0x2c23e128a1f8e847c945]),(bn [0x30206,0xb6604f8c87152a3e44ed,0xe989e579e12e571a6e36,0xaaae46052b5319cebfd9]),(bn [0x2288,0x748abe0333a8a769b15e,0xbebfc6b0203e725ad620,0x4671878edce84b8fa15d]),(bn [0xae,0x35519e3d76b8461c4e79,0x88f956a539e21d964379,0x166a9fe425ba927ca5af])]],[[],[],[(bn [0x429ff4,0xd29233b1fd7836d9b26f,0x52824cf4f6c66d58c7b5,0x1fa3c11271c9b7644000]),(bn [0x267da9,0x91793823e76ad08aa119,0x42b910f8619e18d5c5,0x328e4359f523001c2000]),(bn [0x12467b,0x8314b5be1a6ab421df47,0xd74c7651faa2a222ba10,0x3efcf2fe5fbd173a800]),(bn [0xbaf37,0x458e47907200a1f5b532,0x82672eede621ae3b05d5,0xb4e3825688593c981b00]),(bn [0x63918,0xcd9e1eaac5590d5b8abb,0xba03e85b763830bdce95,0xb0a8d23447ef6ee93a00]),(bn [0x2b35f,0xed4b413f3c17461f04ed,0x659d456c4ea1a02324a1,0x3f06caa329f04cd223c0]),(bn [0xb0bf,0x28bacc2cf4ac50b294c8,0x79e410bcccbbeb7449f0,0x17908293ea6bdecf1900]),(bn [0x1c37,0x715ef3e104405dcbbd28,0xb136be6278607388ad60,0x7acb5ced89d93e5eb0e0]),(bn [0x2ee,0x543add053cec50534fd2,0xe80481b37e9b5679ad7f,0x50a331c5eee2dafeb970]),(bn [0x30,0xf26af24daa96fd4a88dc,0x3e3e012c8572da54c7df,0x5f5184c3ac1df88c1630]),(bn [0x1,0xcce47dc6e56a29f968e0,0xf01d3c37d44191c81728,0xad3b85b4775f38fb5330]),(bn [0x7391162e22a3782a57f,0x823e1a1737dbd670362d,0xe6b0071be7625f1e3d10])]],[[-(bn [0x3392,0xbd462bde4426510d3d84,0x138267f3df0feabbdebe,0xcc785ec0178fcf480000]),-(bn [0x8660,0xe1e3ca09f19f0f3ab7a6,0x7737f12d1b907a319ae0,0x5435abf21007fae30000]),-(bn [0x9026,0x7389dcf9ae1e5818e312,0xd622b103a4f203f54529,0xf70f484a8dda4ea68000]),-(bn [0x514a,0xde1e6cf59caeb75ee5d,0xa699fdc9445158238907,0xc8baeb731bedf39b4000]),-(bn [0x1bc1,0x1f05771acf33e92eddbb,0x5b13679f3c91816d83f8,0xafaaa7758459549c000]),-(bn [0x711,0x5c46af2dfee43c0a0e46,0xf77127a7a4b3561c0931,0xf5a845fd27d7698a5000]),-(bn [0x16c,0xdb89a0244ed1c9454e,0xd45dbe88c5f8f6b0581f,0x749867a53403b7a53000]),-(bn [0x35,0x4b9aa0171fcaaad26818,0x13ccd1f9caf67ea8a62f,0x691d1ccfc665816b0400]),-(bn [0x5,0x7884e0650c64141d3e04,0xd18fed8dad93d229f72,0xbb33b449853453f87200]),-(bn [0x6161b38233f9cb3ff30d,0x267bafd02bb5f6db9950,0xa3fce6b77198f95aac00]),-(bn [0x41c8eecb6647516131b,0x568e91441f5bc200d120,0xb072901e8af3b6afee00]),-(bn [0x143ce6df9df1e28343,0x1bb6b40a8233d3b07cbd,0xe805678825632f9f8400])]]],[[[],[],[],[],[],[-(bn [0x4d7733984,0xb64451d1bf6c4fba6fe6,0x2a32ed1b95fcb1f3c9bc,0xf308d8f79d8253e43980]),-(bn [0x90cab663,0xb87672e1c43bc7f90b23,0xdc87c84e26a2583c9867,0xe9a2b0e6bea485acb280]),(bn [0x5df762b6,0x5d1f0922cc18d1d7e5a,0xb62ed49683b61516b90d,0x641525d97ac43c6f7540]),(bn [0x7703ec9,0x34434beefc9e1e6d8f59,0x84953bab8edcb211df49,0x5406b2ed5eca86fb2d10]),(bn [0xf20343,0xf65a4bf66495207f091e,0x44b709c475801fa8d094,0xc63d44faae1d809a0850]),(bn [0x2804ea,0xc890b7bd485fa003098f,0x8d5c0ae5a0ecaebcbc43,0xdf628529f59708a82f50]),(bn [0x401c5,0x73769a3aca2fd72c7748,0xc6dc56883ff9b9bb7ba,0x6a9205cca00d9fa9b5b0]),-(bn [0xddbd,0x923a7161f40508640cd3,0x7272c1463482083e8a08,0xe9f2352f213cb6dc22e0]),-(bn [0x4ebf,0x4447d00ab6036cd5d58,0x2066d6df56ec9a94182,0x865d66d42cf0d9a69940]),-(bn [0xb88,0x1b2ae1e737ece218f9d6,0x3759184d79e8d09bd194,0x8af9bd9aac8934c9fac0]),-(bn [0xf2,0x52165c0972fd1cff0020,0x1d506495045da6fd5ba3,0x6318dfbe10b24291d440]),-(bn [0x8,0x7a8ad602eae25ffecd3d,0xc33d33f7cb0dfdd992fe,0xcdcd45b3cbe19cb3fc60])]],[[],[],[],[-(bn [0x65f98ea13,0x727986e047b7e34a1bc5,0xf6550d12b326edc54b47,0x2aeb5bd816f367cdcf00]),(bn [0xb8ee4d1b,0x9d31aaedd6fe4323e5c8,0x751620046d70215c6609,0x799b318e776dfe29cc80]),(bn [0x94d97e2a,0x2583afe110f98f31285a,0xc6e9c85e54620cfa1062,0x235c6b24450178053e0]),-(bn [0x11540,0x786affb0c7ff98a57d15,0xf770fa5294f545ea68ce,0x1bfaac83f7936afa7100]),-(bn [0x596b,0x829a6888c633d9b5d3f3,0xf3abd1c2ca35fe54ea4f,0x37f51262e62382e6500]),-(bn [0xca8,0x1ce25f9defd099847c16,0xfee9e7158ed3627ad94c,0x377520e69a114462f500]),-(bn [0xb3,0x4ddd29b913535ed26c37,0x688839486e40d8afabd6,0x31f2e472da017dbd5300]),0,(bn [0x1c7ae7054ee07f3aa196,0xbebbeb0f5cddca96087d,0x3470d94b9b3e7bdbd800])]],[[],[-(bn [0x3d4025,0xbf7b825b55cc3d340ed7,0xfec4fb93fdc6bf244382,0x19075c5a6bf84a3cb000]),-(bn [0x14a0cf,0xcd56eae4e662f5eb4fb7,0x40ac8f5b33d67a555a47,0xa97e147ae1b85fb20800]),-(bn [0x76985,0x65d3bf10e7a85062ef4c,0xa7af2b128be92badb85f,0xa9e3c6e87b3228fa5a00]),(bn [0x24d4,0xe914322e759c811cd83c,0xe964e3dece57059fa83d,0x136462321ba00a28dc00]),(bn [0x220,0xecb9d89428e0ba767500,0x5618e4c24b6ead94c104,0xf85a86aafcc1f1c43900]),-(bn [0x32,0x26d216316a74cdf480fa,0x71031affe12c91177d23,0x38e64462bede557bfb00]),-(bn [0xc,0x802c700c4002cea46d53,0x2cb7f1e24fa1e4b5ceab,0x283854eb357914f72b00]),-(bn [0xad481e00e878cd26227b,0x7ce3b78510dabe21bc15,0x4a6666da335964e8a700]),(bn [0xe3d7382a7703f9d50cb,0x5f5df587ae6ee54b043e,0x9a386ca5cd9f3dedec00])]]],[[[],[],[-(bn [0x27ef9,0x35879e9908272f833dbd,0xb3f87ce2d7321353c41a,0x7e508c2c32cacfc34000]),-(bn [0x603f,0x4f3c89ae80df430ce20b,0x1e4b0b942df7d086a9dc,0x83cb0e097ad67c74e000]),-(bn [0x6d9c,0x79be18fc53c075538048,0xa6a19d07d49279175d67,0xd415a5f5a26ed5efc000]),(bn [0x2983,0x5e9627ad4dc8248ca72b,0x1806f1183dbd6b65b3da,0x19db8bf349b509c30000]),(bn [0x1458,0x2f1f0c643da824691792,0x61eee13811f5b86e755a,0x9d784d9a6756bf26f800]),(bn [0x38d,0xd0a92d3d5a1a1bc38326,0xa75e5da64abb65db3c7e,0x8c79b8acad7c0c7ee800]),(bn [0x52,0x1a5128d741235ac8c8de,0x7f08dc939cfcce0e1fc4,0xebe53b1b12f7817c9000]),(bn [0x4,0x2fa9fe5bfd71c5180897,0x53d55e55df5c288f849c,0x20d04a4b624a36aa3000]),(bn [0x1a4a1053ab4561bff79e,0xd77262d31aa5588a7dfd,0x6b7bdc45ca610fdea000])]],[[(bn [0x74e6,0x94952dcefc7bfb80e09c,0x98fae23bbc7d864a6340,0xfbb56c7f7d51aaa30000]),-(bn [0x1f674,0x33a5acf095bbdc16f948,0x861c816e6a35f2a3634e,0x3eb3eddcb31a8a778000]),-(bn [0x36a2,0xdea33132c6f015ebaade,0xf4352d8d8f81d9b1791,0x2ba6d66aa7ac67e44000]),(bn [0x261,0xce8d249b14b0a1cb960e,0x34be324b99c761ee72ab,0xcae31c809fd5cac4a000]),(bn [0x14d,0x50adc064aee5dfd878ac,0xaccfe4eb5fba15f84c01,0x80e107d3aff6ad09a000]),(bn [0x48,0x89246b9a699001fa261,0x60ceea4a032b580c14b4,0x86f6e064f79274f56000]),(bn [0x8,0xf45642e437760dbdd4e7,0xa3fed6af88ba12abf9bd,0xe3dffba50e813d9a3800]),(bn [0x9cb3f21ef0d924b95dbf,0x851992b3b9b03cf9d7c6,0xd690d4d267bb7be2d800]),(bn [0x461ad6347363af553ef,0xce9310788470e41714ff,0x91e9fa0ba1bad7fa7000])]]]],[[[[],[],[],[],[],[],[(bn [0x26485048,0xe73dba04fc83a4d0c763,0x161ed1399739197a3a06,0xb596591f2963c526000]),-(bn [0x893291d,0xb82ef879da355c2fc019,0xbdf25450254b9575eccf,0xb2fff758b58f4808ec00]),-(bn [0x69860d9,0xaa2037757153c0e795d8,0x552e8cffa87e29928c1c,0x7a38a58e0825c6576000]),-(bn [0xf4dd46,0x746043e2361464522485,0x5f76781097fc17a6fd9c,0x5e51dcc7d7072c620700]),-(bn [0x91295,0xd09f0faa45ddf0f15811,0x84341ed6303ce13da146,0xb88d836ae1a67c10e100]),-(bn [0x2354,0x1692b834b58eeeb7dc91,0x5ca4e56401b1a6eb0cac,0xd2106af92f2385f94600])]],[[],[],[],[],[(bn [0x20fc76,0xeacbfdddc276e414f7be,0x326a3e004ba5f46eba39,0xff8d37f24503a69f0000]),-(bn [0x1cf75a4,0x2d3e941e575c283009f7,0xc3463c2ad9e93505a598,0x976c5836fa07be9e000]),-(bn [0x3b5dd86,0xaaafce70a55bf9d00f,0xd8835fe52a84e28ea858,0x5855079a0dcaecad800]),-(bn [0xbbbb63,0xab4d42ea7de3ddba85c8,0xbbca0eac6f71f07a3452,0x94b0f10585392b9a9600]),(bn [0x10,0xe4ded16190144c7d164d,0xf84a20254d5a1b971ef3,0xd0fe3fa51237b1370000])]],[[],[],[-(bn [0x980,0xbd55c6e10b6b065c8bdb,0xa9b214fb82af85016925,0x8f03ccda3f53aef00000]),(bn [0x980,0xbd55c6e10b6b065c8bdb,0xa9b214fb82af85016925,0x8f03ccda3f53aef00000]),(bn [0x58b,0x191cb40346a9190b5195,0x78528c3d61910d962800,0x936ce229fa46260c0000]),(bn [0xca,0xba71d092c0f395dd0ba7,0xa37981bfa0394b15736d,0xcbeafbbcda9c4e940000]),(bn [0x8,0x726f68b0c80a263e8b26,0xfc251012a6ad0dcb8f79,0xe87f1fd2891bd89b8000])]],[[-(bn [0x25,0xa5ff42c8902aa63cd12e,0x56b3c059e6ca141ef944,0x4bf0e7a1c6361ece0000]),(bn [0xd05,0x56de2f1b047778bb5f98,0x1a3788ed6665597306bb,0x46b5bfacdbce7cba0000]),(bn [0xeec,0x8ba54d75d35ed342a512,0xae75cc6ad2442d7aca91,0xbf215f90dd9e2708000]),(bn [0x48c,0x9844cd1ea0dd47d556ed,0xeb09bd070a4a832d3067,0x662f354dd5b8f5538000]),(bn [0x79,0x701c76f33e888f421814,0xf7bbe824d72baf6dec97,0x417e48d96c8f5633d000]),(bn [0x4,0x55ec15f7fe49decee877,0xec222054ca61d7394f2c,0xe86612c277bbd46f6000])]]],[[[],[],[],[-(bn [0x2ac3,0x5401fef4b3619ca0755c,0x7ba15e6bcc15d6865929,0x39119d61cf893380000]),-(bn [0x980,0xbd55c6e10b6b065c8bdb,0xa9b214fb82af85016925,0x8f03ccda3f53aef00000]),-(bn [0xca,0xba71d092c0f395dd0ba7,0xa37981bfa0394b15736d,0xcbeafbbcda9c4e940000])]],[[],[-(bn [0x17c1,0xd95671329c8b8fe75da5,0x283d3474c6b6cc8386dd,0xe58980219e5135580000]),-(bn [0x980,0xbd55c6e10b6b065c8bdb,0xa9b214fb82af85016925,0x8f03ccda3f53aef00000]),-(bn [0xca,0xba71d092c0f395dd0ba7,0xa37981bfa0394b15736d,0xcbeafbbcda9c4e940000])]]],[[[(bn [0xf3a,0xc8e8f5f973a1994e3ab1,0x37b0251617cfa941003f,0x594072e4d83186c4c000]),-(bn [0xb0a,0xf5291e047052355bc1cc,0xd1609da68d0789af70c,0x5335a51c2558fa9a4000]),-(bn [0xf0,0x4cfd3cc986317eb367e9,0x518f519f8f5d51e7a06a,0x78296deddf350eee8000])]]]],[[[[],[],[],[],[(bn [0x1301,0x7aab8dc216d60cb917b7,0x536429f7055f0a02d24b,0x1e0799b47ea75de00000]),(bn [0x4c0,0x5eaae37085b5832e45ed,0xd4d90a7dc157c280b492,0xc781e66d1fa9d7780000]),(bn [0x65,0x5d38e8496079caee85d3,0xd1bcc0dfd01ca58ab9b6,0xe5f57dde6d4e274a0000])]],[[],[],[(bn [0x980,0xbd55c6e10b6b065c8bdb,0xa9b214fb82af85016925,0x8f03ccda3f53aef00000]),(bn [0x4c0,0x5eaae37085b5832e45ed,0xd4d90a7dc157c280b492,0xc781e66d1fa9d7780000]),(bn [0x65,0x5d38e8496079caee85d3,0xd1bcc0dfd01ca58ab9b6,0xe5f57dde6d4e274a0000])]],[[-(bn [0x4c0,0x5eaae37085b5832e45ed,0xd4d90a7dc157c280b492,0xc781e66d1fa9d7780000])]]],[[[],[-(bn [0x980,0xbd55c6e10b6b065c8bdb,0xa9b214fb82af85016925,0x8f03ccda3f53aef00000])]]]],[[[[],[],[(bn [0x4c0,0x5eaae37085b5832e45ed,0xd4d90a7dc157c280b492,0xc781e66d1fa9d7780000])]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0C1 : Tower 5 :=
  [[[[[],[],[],[],[],[],[],[],[],[(bn [0xfe2760f16,0x3f2a71d09ddbb6c2ef44,0xd1ceafe81ee7b6d983f0,0xeb2f119b24508d8dda80]),-(bn [0x1290fe3e2,0x65012e36be626ce66148,0x2a9489ebd7cbfd982e79,0x29a8d8e9757838913c00]),-(bn [0x33a1047f4,0x95c1faa116e51c1539af,0x4836173cadd7c7ba4b38,0x1119efb54f7446f6d700]),-(bn [0xabf81784,0xba2334e949dde6c2f38d,0x373370df9905a8975685,0x7e3105b118315e990690]),-(bn [0xadbbb5b,0xeb299ec4ab59b046d9cc,0x7812288ef83aebdde317,0x3107db39ba902ea09ab8]),-(bn [0x2b5cdf5,0xf4917672b0e0eb1b7428,0x47f2049835da5985a7b0,0xbefe7cc6bc4351ec05a4]),-(bn [0x1401025,0x465761f3454535fa9334,0x14dd8b0d9b52f9dae227,0xb282cc6d0f302145860]),-(bn [0x3cd617,0xcb3553127e1b684ea64b,0x8cbb2c4a44cca2ecd5f1,0x8563791e1b41715f03a]),-(bn [0x609df,0x593abaa2111934e7f7cf,0xfa66bfabbbb308760601,0xea6e476c9412719774d]),-(bn [0x5178,0xec88dc61fedc9aad0bc9,0xc882ace949fe41a4ab50,0x71f85567b117247c15b0]),-(bn [0x1ed,0x9d85aca38190989c7d9,0x904d85e20a5d23233a47,0xbbf278f9b53a5f0921f])]],[[],[],[],[],[],[],[],[(bn [0x189cf026f0,0x15c7a9cb4a06c4bebf4c,0xd8c3fc85b837a7a79ebc,0x42afe85091420bca0e80]),-(bn [0x3a3a7dbb7,0xe7d0d0d36c1c4707e331,0x59df399396b0a0b591ff,0x9e9293606cb69561f300]),-(bn [0x75a6a3b40,0xdc82a4e1b27bc777b8e2,0x160754a9ea2f15c64666,0xf1e18d129833cc5f8e60]),-(bn [0x23875f01f,0x2ead3f710f6faa989933,0x197f7e77e36d8765704,0xe4b45ffe51b4adafb440]),-(bn [0x57da0195,0x2c9149762ba48acf477,0x246ff9e4c53a5e89a523,0x74de7e4251e33c277dc0]),-(bn [0x101de69f,0xaedb356ce2f69033cbf7,0x56b9be6de03d5aabdb13,0xabefeebf8975ce9717d8]),-(bn [0x3a7456f,0x13e279b4f7894b8e5976,0xcb88f7e427985f3d5144,0xc2d951bf301f72edfbec]),-(bn [0x92e292,0xdd0b72e0510c328d68b8,0x2141875db6621148fbdb,0xd7fc2b26fb5cea46e9ca]),-(bn [0xdc99c,0x6f867fab53fe4d77a7dd,0x22510dc14dcf9b5e7dd2,0x221a4da355de42b8bf87]),-(bn [0xb643,0xd47652c75ac48dd30bd1,0x55749b4c155be4e4f0af,0xe1bcbe30a57cfd9f6f0]),-(bn [0x42b,0x9c22cdce81e3fe3b5186,0xbfa1221fdbb28fd0162a,0x7b42797f2f488f37f57d])]],[[],[],[],[],[],[(bn [0x673e914c4,0xc86d1aecc7d387cb49cd,0xd4ebc0982acfd7b5f2a7,0x2be3b9abf10a53b3900]),-(bn [0x1e4a54084,0x1fa4aa9b9cb0597e6242,0x3154daa574a2ab8fded2,0x9e8fac631b08513f2e00]),-(bn [0x4cc2be8ee,0xc58604c0342b2f7181ba,0xa1eb6c94564769b9979,0x83f4511bf317bc530be0]),-(bn [0x1ff3a9364,0x6e08dc8fede0fee56f1b,0x5a3b76898ecf379e9813,0xa9b99588462e4d4ec290]),-(bn [0x6de5bfa1,0x5b3d6647342fc1d4ff60,0xbc8cbe1c049384ecd994,0x213b4e4917fca1e58db8]),-(bn [0x14479d97,0xe90d564f04587a83a1d3,0xb04f74fff6064a11be37,0x8feb3f562eb3d2fc5d44]),-(bn [0x3791a78,0xb3dcba45186cfa7bf605,0xb657f0ae409a913a43b0,0xb7c955908bd74460ffd8]),-(bn [0x768687,0xf8889178a7ccb86f2353,0x2a70f00541ae3d346070,0x36cc7fe83d545e749506]),-(bn [0xa6c0c,0x20b27e21a12931c263c7,0x2f2a2ba40665fcf716c6,0x8a68c9ad259ad82ee117]),-(bn [0x8547,0xa8900eedf683f8e8a35d,0x908f919b6684eb9a47d1,0xde3ce9fad099a4771890]),-(bn [0x2ec,0xbffc267cfa01f5337498,0x1f1c7352c25ea4084674,0x5882bfc80cee4b46a40d])]],[[],[],[],[-(bn [0xcd26e58d,0x9dd755b22684d7c90e77,0x7934d4385d16fbd541ca,0xab0dbe49617c1b07f400]),-(bn [0x114cf3022,0xa87b720211f8307aabe3,0xfba9ef1ebd98789857e7,0x5b0b4ccecc6e712a9900]),-(bn [0xd3dab6c3,0xdc4624dcf0bee0714803,0xc0e7f5785b50a9b6d063,0x162d11bcba2c061e2200]),-(bn [0x71771d81,0x4c3196304b0da4005526,0x874a22b5ceab8fb7e051,0xb448234b140f300369e0]),-(bn [0x22d09bdc,0xa6f9391ba27b3bb71bdc,0xbc8f25f48003878a0677,0x4abbdd1ffe5026ec9c30]),-(bn [0x6c7dffc,0xfc1952bd13a45e00198d,0x85a06cfd5f03f2d26351,0x239a4e1ddad831d30110]),-(bn [0x1086556,0x90d9f50c9fe30185306e,0x63f78bc9ff3428e2e93a,0xd17d46d10f5763a66acc]),-(bn [0x1fe6a1,0x1162c2c122005bb10131,0xd53f01ce72a3389fb937,0xdc094ae1ed63ca86d496]),-(bn [0x2a562,0x193d28bfc2bcb49ac3df,0xa15df434416e7efc7b13,0x99f750a5273cabf32b4d]),-(bn [0x207e,0x5f44fce5e7e5521ce9e3,0x3b68c0daae5800f1d298,0x9a0152b42b0e7ad7f650]),-(bn [0xae,0x33f666ab9a6e1e9f8cdf,0x1caf0168d03ae0d91a3a,0x68333568591da231523f])]],[[],[-(bn [0xba2be,0x70b9b9df6d2372fa8652,0x31d64e89f3feb02bd3ab,0xaeac818f441295e28000]),-(bn [0x11f27f,0x438ad2fa15066397b242,0x5b9e8880853e18ba4761,0xdf5f1d2b65e3a26fb000]),-(bn [0xf373b,0xfad9aa58bb6a559d919,0x7f120931592099011478,0x3d4d6910a52f298e5000]),-(bn [0x8805f,0xc9c2c49e452031e56e50,0x87a33d55ba6f0908110e,0xa530f593920f1e149200]),-(bn [0x2c23d,0xee746ee3f74c4446263c,0x7f8c948dfb8a930721ed,0x8e3462e97aa8e234600]),-(bn [0x94f2,0x6c1aa032adb362059ae9,0x49b0e558cc96fff75273,0x6f9e90c3b0f3439ac00]),-(bn [0x16ad,0x779f7008bd3e9bffecd3,0xc8b68c292e78e3a73d7,0xaac103c567b3e81e8d00]),-(bn [0x271,0xdac775575f9db3c6f2bb,0xd54afbfa77e35bc03051,0x18e34020c8bcf235e920]),-(bn [0x2a,0xfc5410344155c94e3fdc,0x5b5271aebf73e404ab60,0x1d387c3d58ce68bd0d70]),-(bn [0x1,0x9ea2645d4d494c5a468d,0x37cb1da21330b897d025,0x57e7df34b3b581bebf00]),-(bn [0x644b332ea371e1da1f4,0x2ce62a53df31a97dafa9,0x7f33c78fe02440321190])]]],[[[],[],[],[],[],[],[-(bn [0x3f388f1e7,0x1f42ce09abd0bcd82390,0x916b369aa5bf79a924f2,0xe6e43ddf2515d6210e80]),-(bn [0xd8cebe77,0x3301cac3b68ae0a4592a,0x81f216b40e6bd8b1eb4,0xd85da2a794b269e14400]),(bn [0x35b4d5e4,0x3e6316339090eefe5808,0x1d29a15c88ae93d49bb4,0xe4e99147a5a5e6cd5980]),(bn [0x5500d8e,0x23b862040820f728c576,0x939c823725bd49df2e3c,0x4425f9e48c5b09183390]),(bn [0x739d44,0x34bf3e4d12889c7df007,0x619bc6ef72d55129f115,0xc66ea9a2f2f65fdbd740]),(bn [0xf59e5,0x7e9e6af24331ca59f32c,0x1a842378041fc5da504a,0x2a3fe8ed4e17e4ad5a50]),(bn [0x45d40,0x9b24ec1e9ac6695f6145,0xa5f230b7cadd82de297b,0x5dfc9800a1e1879aa300]),(bn [0x854e,0x311bf7894043531cd2aa,0xaa14de9c1d427e17aab8,0x8b07e50de9b396c11a20]),(bn [0xcef,0x44310e22cc67772e277c,0x47687432855708fd7468,0x68814bc2c7b7bcec0160]),(bn [0xd8,0xe3ebbe771f6810a9b461,0x6dc9ce2b24aea422fefc,0x2a5461fbe2f65f1eaf20]),(bn [0x8,0x7a8ad602eae25ffecd3d,0xc33d33f7cb0dfdd992fe,0xcdcd45b3cbe19cb3fc60])]],[[],[],[],[],[-(bn [0x702019419,0xcc3d1571adb2958d5ec8,0x46b111efcf69a70172a,0xc749328efd3a167b200]),(bn [0x4119b36f,0x1425707846083d4bc821,0x6caa5cfb10df1098d834,0x4275a50012a2ef52b100]),(bn [0x97a30467,0x116db5cef4d4cec5d600,0x4d024026227db6a8890,0x7c880715c4b2c99d9f40]),(bn [0x97fd144,0x5fc34cb50dc66e80348a,0x39624be9784740cfecc5,0x6cdd0061b73ea3408c10]),(bn [0x732d96,0x5d2ddfdc1887d1b706c1,0xfb2afb181cc82ae2fac1,0xf150e61a97e7b8dd8940]),-(bn [0x17b9a,0xb7c4e671c4779167a59,0xe7ecbed94a99ab6a4ffb,0x344d31555601ea08a030]),(bn [0x16aa4,0x50303a812e5b42b02f41,0x25ba583fcf0a72817985,0x8cc162bfdf4b8601ef00]),(bn [0x3a62,0x1a68d88ef7cd8cff55e,0x2747c5717f7da6eaa52,0xfd04bc6d85723e223a20]),(bn [0x963,0x770baaee006bc2291d89,0x771441bc815bc1571140,0x12156323519058ab5be0]),(bn [0xd8,0xe5bf1c0b27bea93a975a,0xae87150806885881f266,0xa7208a2b66598e71b320]),(bn [0x8,0x7a8ad602eae25ffecd3d,0xc33d33f7cb0dfdd992fe,0xcdcd45b3cbe19cb3fc60])]],[[],[],[-(bn [0x44c088,0x606f2bc6aa1ae0b5dd5a,0xbdde39b29262cfafafc5,0x4f043abe928f69654000]),-(bn [0x14be18,0xaf48deadd86fa265e374,0xbb104e73eeb70eb11f15,0xe439dbc8ce59251ea000]),-(bn [0x6cac0,0xa6a0716e6242bfe68c76,0xf69c4dc831fa515e085d,0x922416b8d62a8bfce000]),(bn [0x17e,0xdc589a3e4c499ed9323d,0x77b67242e245384c5329,0x5392163163609b64bb00]),(bn [0x1836,0x43a3502d36d6724ef595,0x86ac22dc5f818b9c8f0e,0x88636327cad2b706fd00]),(bn [0x2b6,0xea85ce698133db877e75,0x35e5d8f647682fa5797f,0x300b942ae2f3c490a900]),(bn [0x2d,0x24368e36410d4366b7ea,0x23911ba4f864da1769f9,0x1e20b85d4e7c0534b700]),(bn [0x4,0x38970c2e372f0d867b0,0x57547eb24b3bc4f5cc24,0xdc3dd3511d3e43a3a000]),(bn [0x3ae488c67caa527e5127,0x2dc2ecb426811a6546f,0xc6411a68f1b7aadfae00]),(bn [0x230d6b1a39b1d7aa9f7,0xe749883c4238720b8a7f,0xc8f4fd05d0dd6bfd3800])]],[[-(bn [0xbba7,0xf757487e2344a96e6a49,0x2e3e9e77b5b949ff7832,0xc68f92a5a32c6b850000]),(bn [0xfdf,0xc2cfc5f7ae2cc21f7c47,0x369412cffb5d3314f066,0xcc13645015b45e5ca000]),(bn [0x401c,0xe662c2284404d52d98e8,0xf94977e51b6b80a45c69,0x79d1655c03bb6539800]),(bn [0x160c,0x6ec512337d6d7e4818f3,0x9e03b7bab53bda8d7b05,0xc6373c2314314d534800]),(bn [0x327,0xf65e6523fb01c313f93e,0xc729e41ec09381f84d3b,0xa002b5dae1d69f33a500]),(bn [0x5e,0x7993437c6d526114755d,0x9ee06543815c72e17f45,0xd9574a531ddeac604e00]),(bn [0xd,0x70ad2682be86a51616bd,0x31afd8ff877a474a7d78,0x7e9388b83440c7587700]),(bn [0x1,0x5af348a2aafcc8021bc4,0xb3f9996865d9efa273bb,0x1840bb2881fd42c92800]),(bn [0x114b1bb4da377090433e,0x729633bccd3bf1c14ff7,0x1f91bcfc029752739600]),(bn [0x5d791d9b4484e9c6fe,0xa68c415f605ebdac9715,0x4c28d4d64d7a3caa3400])]]],[[[],[],[],[-(bn [0x4440e,0xd2fd8e01c8ec6a71e5bd,0x841b19f297dc20be39e9,0x76c8a3aa01c503acc000]),(bn [0x998f,0x3e20a7365aeccbe0c505,0x897b638cc60fbf25ae94,0x75654014e3ce4220e000]),-(bn [0x3f0f,0x8dea8133e46fbcedc820,0xde40a68a7e8a89f50243,0xd194dbbe8f9dd48dc000]),-(bn [0x15fe,0xe0ab2376331da62726e1,0xbf418b5ed1ac27e08c8e,0x68ae0519542c46d28000]),-(bn [0x34f,0x82873021eda3f58fc65b,0xd15b9173d5e1f6401c32,0x542b2bc0ab4bb9760800]),-(bn [0x45,0xc4c8509a39c4390c9c4c,0x9b493cf3946d334f4fce,0xae5ee4891ae6023a0000]),-(bn [0x3,0x513ce36be06b2bfebfca,0xb41dd492630e8e3b71db,0xbd89ceca809c131ac800]),-(bn [0x15e862f0640f26caa3af,0x8df525a9634747368fd,0xd991e23a28a637e43000])]],[[],[(bn [0x74c9,0xba34cecf96192ef0b8fb,0xa7c08022ded6713a3627,0x5c5211b310698ef20000]),-(bn [0x2567c,0x5a80be46d2b0770373ab,0x84243141b81f2f80bb01,0x96eea60047d879d38000]),-(bn [0x8fbd,0xd8cd6baa3bea92f48e49,0x17031f84a122b203ff48,0xb23660706820f3c72000]),-(bn [0x13c2,0x9c4ab9955790f7c3b048,0x14f4bd51b69cdb53b7fa,0xfd8c83f26e9113032000]),-(bn [0x2ad,0x7068d8822e171bcf0a38,0x9338b80216fd23129911,0xe0c766f1f3590402800]),-(bn [0x40,0xa2512042c637218e3f46,0x86f1efb86021e842b44f,0xb02ddee793f0e8bec000]),-(bn [0x3,0x513ce36be06b2bfebfca,0xb41dd492630e8e3b71db,0xbd89ceca809c131ac800]),-(bn [0x15e862f0640f26caa3af,0x8df525a9634747368fd,0xd991e23a28a637e43000])]]],[[[(bn [0x256,0x14da13297acb3129bb40,0x3fde704f04c802650eaf,0x4d3cba8fd9757af90000]),(bn [0x4cf,0x4ce2204849045f3aa319,0x27b8c55c5f3d8bb34ccc,0xca127680df1215010000]),(bn [0x408,0x5fdc890992816447bac4,0x1b46c0dd9dfbb5d1daf8,0xb4513f5b4512d542e000]),(bn [0x6f,0x2bfe74313d58654d5f06,0x9de0bcf2113f3ae3b843,0x8e4278171225ae994000]),-(bn [0x4,0x43c16fa5380c4431605c,0xfdcb4baf94e27b7b599f,0x764629af2569f28b6000]),-(bn [0x349420a7568ac37fef3d,0xaee4c5a6354ab114fbfa,0xd6f7b88b94c21fbd4000])]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0C2 : Tower 5 :=
  [[[[[],[],[],[],[],[],[],[],[-(bn [0x81cec03d,0xa295765e320f559aa44b,0x211288b6e1f7eccf66b0,0xa4d4668d738ec6187680]),(bn [0x22cfb9e0,0x2883c58e9ea33d41dcfd,0xb6edd56f210ba1d2d7e4,0x3a9eebc08b3244233b80]),(bn [0xebb0ced,0xb7a978080a50515c5f1a,0x471a5d8615a28e7579c9,0x5d67ecee7c487208b760]),-(bn [0x740353e,0x1a7e69763221283cc448,0x71dcc41558ebd4b1f75a,0x446a3bf579ef314050]),-(bn [0x3616e49,0xebbd7e6faa0490061dd6,0xf403af078b146ff35b8d,0x6f72684b16bccf9794b0]),-(bn [0x7f5d6b,0x96978c7f8d110f14c6b7,0x8ae512e2becccb632cc7,0x2e4dd369514108dfb27c]),-(bn [0x7d482,0x7fc93f7017cae55a4f3e,0xb49ba7cccb28a4ab970c,0xf9f7301f54c644fcd170]),-(bn [0x14f7,0xe0abe0b066c528e68704,0xbb9c4b44641fbc9cb069,0x7c5c467dcc03b42ac45c]),(bn [0x320,0x8d5bd0e92c4db4cea0e,0x37d6c21e36c123765ec0,0x86c5179c01df9d9cb100]),(bn [0x18,0xc973230fc66e08398fe0,0x6176eac41329ad838496,0x7810d825c9bf4b0bc360])]],[[],[],[],[],[],[],[-(bn [0xa9b85ca0,0xf2dd9607540110652e20,0xa908e2174e5b355f80a5,0xcf30fb7e86f42de57980]),(bn [0x1f3e9bd4,0x27aec1fdaface714c56d,0xd7bd7c0517eddd959ae4,0xfc9a4d8f181c670ce380]),(bn [0x11e316cf,0xeafaf69b7409255de0df,0x695daa4f6abfd7bcfe62,0xa66e0a5f33f449c623a0]),-(bn [0x9af6935,0x3fba0558e51d1ab1ea5a,0xbb2e90551059d9e0542d,0x189aab50cac070a15a60]),-(bn [0x51c0611,0xe3ea85d71f84b022e14e,0xcb9aac749410cb39045b,0xe26823d55bbe1de71d20]),-(bn [0xc8231c,0x5644b08aad3a858e5f0b,0x1e1c08ade3c461709672,0xa86abae65613203a3678]),-(bn [0xc77f9,0x3a372dbea0b2eefa0aaf,0x6d8721059d8ef85ee208,0x5636b9b798c36d35ee40]),-(bn [0x30e7,0xe991ce130da080ceb1fa,0x4c34c7c1286163798f61,0xfbfd7bfb8cb7c5eb2ef8]),(bn [0x31f,0xb96c56d39b84fd5e9d01,0x44cbd75613413b3b0ede,0xc812a6c427170e0c8000]),(bn [0x18,0xc6e87f78d998465b6eb0,0xd9116ae95036b61a919e,0x68ed1ccc902990374c60])]],[[],[],[],[],[-(bn [0x3fece19c,0x5795d1546bc47d8d2ae3,0x5bbd2b93ac1da4556177,0xec25f2865ceb532b1a00]),-(bn [0x853d865,0x45c9092d0fec74837ca4,0x7cef529e09bb68b23876,0x184f48aab77d7df4cf00]),(bn [0x6b6235f,0x581089cc10411f752e25,0xf7097d0f55ae3931ffa5,0xb7cdaf495133346d3ac0]),-(bn [0x24f1396,0xfe8e727e1a1dd29b1431,0xfa43748772fd5b004bbc,0x9e22597a3eb554fa0610]),-(bn [0x1cedef2,0x2b0cf3d5e0a7145f1cb4,0x220ada0d89556c5d208d,0xf6e87790dda87c3bc9f0]),-(bn [0x476217,0x9d476bf670a7fcdd19f,0xa3bf7ad73b977d9437d3,0xb3241846514ef81fa93c]),-(bn [0x47ef8,0x36ba3b9818067679bbe4,0x4c3ad47aed12f0054fb7,0x5fc815acb5b51485ec50]),-(bn [0x1bf3,0x3e50f9d9aff46ce4c89f,0x21c72fb9598ca75911e8,0xc23d4e5a339b413c15dc]),-(bn [0x751bff359ce6f1dfad1a,0xd88cf89fa336c923b8dd,0x7b2b16a91e0c89b02b80]),-(bn [0x3cff5626340a2cd31c7,0x4c983fc8246c731d6c74,0x16b59905d660983eb280])]],[[],[],[-(bn [0x47e72,0xa9fce070401b0a869e5e,0xedeabd559b11f648e987,0x8813a560260037e4c000]),-(bn [0x47ebb,0x81130b4016e738635691,0x6bbbccc0af3a8f26ce2,0x278c9e81f738a189c000]),-(bn [0x2e78b,0xcc8609513a4a411d7c39,0x1b8598a015864b3eb957,0x46ab9c9627f3aa454000]),-(bn [0x152a6,0x110cb874ff08d50add45,0x2b719bd0467b5ccb1bae,0x4e5c289a696292a2df00]),-(bn [0x3e8e,0xe99bf2d1ebce2fb42f1d,0xb4f47b83a16123588dfe,0x8469dabe536b3098e00]),-(bn [0x5ce,0xa4e520376ea90b6c96c5,0xceec0c99022fa9350580,0x79cd6d1bb4b3652a5040]),-(bn [0x4e,0xe795681d9886358c64c4,0xacc5b30e92d5299f648c,0xb592940587699f3e700]),-(bn [0x2,0xede4440835bb3486ce2f,0x11bef7a2c6c4fcfccf84,0x599fa3d673d448994f40]),-(bn [0x220f77772cf64a2a6085,0x353bb4d26d92150a844e,0x7c2682e398a3612d2480]),-(bn [0x13114e496ccef0c8d54,0xa87c0be2df45a803fcbe,0x1f8c76247767adcab780])]],[[(bn [0x1fa,0xaff0e702b0691e2717a2,0x61c068cbe68e4e4e9582,0x6f57366213865b400000]),(bn [0x4cc,0x513d1883fd4a2cb773b0,0x3b8bd5058f61d7bf0763,0xce43582f84c124c10000]),(bn [0x4f4,0xa144874234f97631e2d3,0xb3e4c11d9f67dff0501e,0x34237b641b1e7eac8000]),(bn [0x257,0x93ef0af7fe422a35a3cc,0xffdb9705291bfa7e14b8,0x85a752a944b3a4e0c000]),(bn [0x94,0xad3598226778ea28fb4b,0x3b5e263639aaeea0a98f,0xda6d102f58e9fb904000]),(bn [0x18,0x4eb37ceb2eb8f17a6959,0xe251f06fc0f3bc0b46f,0xbf359fe781b952add000]),(bn [0x3,0x1d3ec278d5d0ae1f4ea9,0x893c2324a3879e37e739,0xf7f63d61948f3c03e800]),(bn [0x4786c86ed35de075cf7a,0x7f6fbb99ce86037f636b,0xe8fc7505ff12e6e25c00]),(bn [0x3a3218378b0c9c6ff88,0xb04659051224cbdde4ad,0x405222edaaa098f2d600]),(bn [0x143ce6df9df1e28343,0x1bb6b40a8233d3b07cbd,0xe805678825632f9f8400])]]],[[[],[],[],[],[],[(bn [0xb66051c,0x7da4bd75f6ad9f004e7f,0xb06d09f80d7d077ed476,0x2fa053081c315bf93c80]),(bn [0x26e8728,0xeed6062edd2da2db256a,0xcd347bf820a07d391ee8,0x9b6ee093187ab97e3a00]),-(bn [0x1a4e84a,0xa1c71169ec73c9cb8658,0xaa872a051ee22aa15e33,0x59a87ecaf89d3a10160]),0,0,0,0,0,-(bn [0x5d791d9b4484e9c6fe,0xa68c415f605ebdac9715,0x4c28d4d64d7a3caa3400])]],[[],[],[],[(bn [0x29d0e5d4,0xfe908aeaa89c83a1fd99,0x6f9c0f4eb19dca46d71a,0x3df3688cf1108fc1f900]),-(bn [0x4bc490a,0x722cf12096fa3137d23f,0x18bb3a4f9e8bdc31db9b,0x479f1a772c24c3bf6780]),-(bn [0x3d0d6f8,0xa87f4a91d8aaba9c1b2f,0xe1a6afd69550f6c76657,0x3b9b7498e8ea6bf3ff20]),0,0,0,0,0,-(bn [0xbaf23b368909d38dfd,0x4d1882bec0bd7b592e2a,0x9851a9ac9af479546800])]],[[],[(bn [0x12a61,0x96c0dc7308ef5f1107fe,0x4708edad92022309326d,0xa188888d7c0877675000]),(bn [0x805d,0xea6b49e0a8c9601d6a3a,0x2508a7a9c33cf3f83d11,0xa8eb34f645423ce5800]),(bn [0x35e2,0x52d69ee92f2658049ac1,0x55f44bb17ec7e61f1b4a,0xb667b785af04ddcafe00]),0,0,0,0,0,-(bn [0x5d791d9b4484e9c6fe,0xa68c415f605ebdac9715,0x4c28d4d64d7a3caa3400])]]],[[[],[],[(bn [0x21ad,0x8916e60595b70eace779,0x89d92439969e11e4fe6e,0x57a9c624feb4ac0000]),-(bn [0xf23,0x41eba1d3db8f7c9964a4,0x1c8dacb39d1f5a834ba3,0x372080eca84b18d02000]),-(bn [0x123,0x173ba38c106d57b37588,0x4a08e9542b17588bb1f1,0xe00d4a79dc26dcd70000])]],[[-(bn [0x1dd,0xf85e40c10851effd6d2a,0x20463e403b36aa23a406,0x3c6c9b6f0a30809c0000]),(bn [0xbf3,0x5cd678316ea85f2e1671,0xb1c68a7c9d8586994b27,0xe13ff75210f0efc0000]),(bn [0x139,0xd5017eeb1f75da57ef1b,0x7f51670504ecac018bb6,0x88ad8a126f0fda3ce000])]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0C3 : Tower 5 :=
  [[[[[],[],[],[],[],[],[],[(bn [0x1e46f0c,0x969d878200bf6b9e6044,0x63cb84a52534a17fad5,0xa94e5da7f88f0ee43c80]),-(bn [0xd09a6d,0xf02d27c82fc29b173db1,0x6f3c5befaa0dd1a51d84,0x3f6eb16f7029af0f7080]),-(bn [0x83e1a,0x3a48b452f4ff2901ef74,0x533a221d352e81a6fe35,0xab31e649baae4734afa0]),(bn [0x37bcf4,0x582360ee6835337beb4e,0x3196feb7b185469e1262,0xd63477597a4d92083a20]),(bn [0x107b17,0x906fad8ecf6a61bd08af,0x60ad264f16cef5503ad7,0xa449dfb80fc9e2e5f2d0]),(bn [0x1bf19,0x820ec036bea9850e3841,0x92a3f94c8f2685f9f3de,0xb5a160f6de3160a71418]),(bn [0x1248,0x4f49f9b85a8b7c1a59ce,0x596a6aaa5ea285294d54,0x4a5da71e448cde64f574])]],[[],[],[],[],[],[(bn [0x5331ba,0x1f26e26547b90e091b10,0x81cd61bac8d636a97174,0x585b8ef1ebc9214b380]),(bn [0xa6bd4,0xc767ef0ebeacc7e1ab32,0xf675d71b2abc5f0645dd,0x35fb95788319f7272d80]),(bn [0x812f82,0x93d2e3093d77148974e,0x2de771afc74c3170419b,0x59986715ad16390978a0]),(bn [0x63905f,0x4ab5aa640a7b959b4083,0xe75b30b255fe71c3ba4,0xd557d353b5d78ebd67a0]),(bn [0x1a8a58,0xc35892a671993ab93eb0,0xd2aa1b0a31e16a94d590,0x62f8b1170a82b6894ca0]),(bn [0x2be9b,0x2b0db9c8d5871990fea8,0xd481ff2fd47744fd9569,0x6f48f18036fca01365b0]),(bn [0x19be,0x2935cda062c4dd589775,0x88b8fc32614995a4e327,0x7ad38ec469564eda44e8])]],[[],[],[],[(bn [0x65e680,0x4a0b70965a22a46da9fd,0x19924cab54cd548c7d16,0xdf93510e82d8cf34a600]),(bn [0x783fa0,0x361c23cbedc977b00a5f,0x90a3441bc7ea3da3aa8c,0xf0e396d3951fba4b9580]),(bn [0x553fb0,0x602278aeee394a8c9972,0x9f44c095655b24223baf,0x8c3409b6aaa185a26840]),(bn [0x2af67c,0x895c6db4c69efeed95fa,0x6644c746ca71afe14e4f,0xa3ce172f13c84833c280]),(bn [0x9fab8,0xc823c7121d67076b2052,0xfdc6ca9f86d8edad7b51,0x644c5844000cb18e04d0]),(bn [0xf2e8,0xfa2923a58e82d51710ce,0x1b8c059c88583c579e51,0x3c5cf61d373b58087818]),(bn [0x82a,0x7fd36ae190a34953adb2,0x6bb00fbeb699630b29ad,0xcff7eb1c4beddd7c434])]],[[],[(bn [0xdd4,0x521d785db5563bb7a3a2,0x190abbdc7aee789b4136,0xa5526e6296ad2f6dc000]),(bn [0x115f,0xeac6b148d77437c45bad,0xde4a76535139dcb9e262,0x507cfbd9450e789d7800]),(bn [0xc8c,0x4592c6a83af9cb9f5d97,0xe6c9606e5074aa1d5061,0x9d53f0666cfdcbc2c800]),(bn [0x5a1,0x612dd4a5d1c0da686595,0xbf1e9bfd3da9f08634e4,0xc53656f7c6f3a7b1c800]),(bn [0xe6,0x4521fd344587b8acaba8,0x1dd8ce01740807b840a3,0x77bac5710b19ef178e00]),(bn [0xf,0x4b7eeba124ebc5fcb2ba,0xae2bcfa1df41b4f53b56,0x9169e8eca9d61dacba80]),(bn [0x5c5df1917e66a1d4acd9,0xe64bdc0b3ce196e59f90,0x11c573995c81da47fcc0])]]],[[[],[],[],[],[(bn [0x632b63,0x326f0ce8ac75739ab838,0x83c97d5f24b896db037f,0x2362b99c9e0cbd020080]),(bn [0x458d9,0xdb9de3fbfc5f3b17329b,0x16bb7c7516f2ff3d9fe,0x9c04fffccdf3bd667240]),0,0,0,-(bn [0x303,0x3861a5922d06dd21f8b5,0x2f858f10529df1b398d6,0xf19dfec1644dda98480]),-(bn [0x65,0xbe820823029c7ff19ee5,0x26de6f9d84a7e632e3f1,0xa59f446d8e93586fd480])]],[[],[],[(bn [0x189f,0x4b1896c7c84a24ecb576,0xf3218e49d5ecaf2af746,0x919b563f60a891ba3800]),-(bn [0x867,0xa65df4ace7e871dd1298,0xe662af652b0a283c0e0a,0x5762b5623811e4dfe400])]],[[(bn [0x1f5,0x7602d703f2526fee3f6f,0x770502f0bd60675fd756,0x1309716920cca549e000]),(bn [0x14,0x90e84851d6c841d4d1a8,0xd7895060dbbc70af74ef,0x5a2943c40a52596e6000]),-(bn [0x8,0x1f61680ae5a99dc99dc9,0xdaac9a3cca40e994d0ff,0x7cccd23a6830bae7d400])]]]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def w0C4 : Tower 5 :=
  [[[[[],[],[],[],[],[],[-(bn [0x86046,0xf31670cbb3fe81690247,0x1b3fa58b1ff814ce513,0xc8416bd0bb4a1fb000]),(bn [0x1e057,0x549b3f085016babd6742,0xda03a90f5e906b23c544,0x228e74389de8ff20c600]),(bn [0x1716e,0x1f52f57582c61f02534,0x9951d117bc97225f7cf2,0xf59827ed63062e923000]),(bn [0x3593,0xed010e0559eba87941e6,0xa84328b1309f55a2f367,0xf0b848d3ea45801ae780]),(bn [0x1fc,0x3261d147686190de205b,0xba17b4fd92c82faf44f6,0xf992d3f0f47ea26cac80]),(bn [0x7,0xbae09e222daa91ed570d,0xb0a74e871651c3f8c2f6,0xf53d476bdd4023c78b00])]],[[],[],[],[],[-(bn [0x72b,0x33be17ebffe38bc24743,0x157da55c5bbac19b000e,0xbc4ff6e6ccf8ca838000]),(bn [0x6573,0x8205d140c170effb7191,0x8b939ad8157a3dd37c26,0x7cd9f02cae1f7dc17000]),(bn [0xcfd8,0x7ae98fa1e11159bb6c8c,0xea03ca1e4d9781dd1b24,0x65d832386d16e0110c00]),(bn [0x2913,0xe7bd868a4c24b6b57cda,0x2ae347907295a357a998,0x8ba277aa567a3086f300])]],[],[[-(bn [0x2,0xc0ddbcaa20516666d57,0xab64ddf062604034b4d3,0xc6831453699117890000]),-(bn [0x3,0xe37deddaec34fd26ed8b,0xdfd2b72f6a01b5fd34e,0x2df5fb8c0e6fe9510000]),-(bn [0x3,0x5a2092a4ec2219843304,0x92b536624e786cb4f484,0x38006aaf021311f34000]),-(bn [0xfed13c20a0bd3c3b7a62,0xaa360d8231ad5b226408,0xd72bcd107a0e615bc000]),-(bn [0x1a922f5cfb055e3539c8,0xe124435efdfef17d77e3,0x3f4a484473d6fccaa800]),-(bn [0xf2dad27b67569e2725,0x4c90707e1a6dec45d8e6,0xe040da61c0a63b7a3000])]]],[],[[[-(bn [0x2,0x4aebec52d3213db8b288,0xb348d39b0b039a742152,0xa2ea104fbf2c50736000]),(bn [0x2,0x6a8c49c32d2b64b1f731,0xd7c058d7b54241be7dcd,0xe790acc6ea96d4e42000]),(bn [0x349420a7568ac37fef3d,0xaee4c5a6354ab114fbfa,0xd6f7b88b94c21fbd4000])]]]]]




end SparseCubes.Certificate

namespace SparseCubes.Certificate


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def total : Tower 5 := (add 5 (add 5 (add 5 (add 5 (add 5 w0NegH (mul 5 w0C0 w0P0)) (mul 5 w0C1 w0P1)) (mul 5 w0C2 w0P2)) (mul 5 w0C3 w0P3)) (mul 5 w0C4 w0P4))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem total_checked : isZero 5 total = true := by
  rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem g0_eval (b c d e j : ℝ) :
    interp 5 w0P0 (point b c d e j) = w0G0 b c d e j := by
  simp only [interp, value, point, w0P0, w0G0, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem g1_eval (b c d e j : ℝ) :
    interp 5 w0P1 (point b c d e j) = w0G1 b c d e j := by
  simp only [interp, value, point, w0P1, w0G1, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem g2_eval (b c d e j : ℝ) :
    interp 5 w0P2 (point b c d e j) = w0G2 b c d e j := by
  simp only [interp, value, point, w0P2, w0G2, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem g3_eval (b c d e j : ℝ) :
    interp 5 w0P3 (point b c d e j) = w0G3 b c d e j := by
  simp only [interp, value, point, w0P3, w0G3, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem g4_eval (b c d e j : ℝ) :
    interp 5 w0P4 (point b c d e j) = w0G4 b c d e j := by
  simp only [interp, value, point, w0P4, w0G4, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem negH_eval (b c d e j : ℝ) :
    interp 5 w0NegH (point b c d e j) = -(w0Den : ℝ) * chartH b c d e j := by
  simp only [interp, value, point, w0NegH, chartH, Int.cast_mul, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem w0_excludes (b c d e j : ℝ)
    (h0 : w0G0 b c d e j = 0)
    (h1 : w0G1 b c d e j = 0)
    (h2 : w0G2 b c d e j = 0)
    (h3 : w0G3 b c d e j = 0)
    (h4 : w0G4 b c d e j = 0)
    :
    chartH b c d e j = 0 := by
  have h := interp_of_isZero 5 total (point b c d e j) total_checked
  simp only [total, interp_add, interp_mul, negH_eval, g0_eval, h0, g1_eval, h1, g2_eval, h2, g3_eval, h3, g4_eval, h4, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (Int.cast_ne_zero.mpr (by decide : w0Den ≠ 0)))

end SparseCubes.Certificate

namespace SparseCubes.Chart.Chart0

variable (b c d e j z : ℝ)

theorem ev0 (hz : z^3=b*z+c) : (m0 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 0 := by
  rw [base0]
  exact eval_initialRep b c d e j 0 z hz 0

theorem ev1 (hz : z^3=b*z+c) : (m1 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 1 := by
  rw [base1]
  exact eval_initialRep b c d e j 0 z hz 1

theorem ev2 (hz : z^3=b*z+c) : (m2 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 2 := by
  rw [base2]
  exact eval_initialRep b c d e j 0 z hz 2

theorem ev3 (hz : z^3=b*z+c) : (m3 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 3 := by
  rw [base3]
  exact eval_initialRep b c d e j 0 z hz 3

theorem ev4 (hz : z^3=b*z+c) : (m4 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 4 := by
  rw [step4,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 0 _ _ _ _ (ev3 b c d e j z hz) (ev2 b c d e j z hz) (ev1 b c d e j z hz) (ev0 b c d e j z hz)

theorem ev5 (hz : z^3=b*z+c) : (m5 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 5 := by
  rw [step5,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 1 _ _ _ _ (ev4 b c d e j z hz) (ev3 b c d e j z hz) (ev2 b c d e j z hz) (ev1 b c d e j z hz)

theorem ev6 (hz : z^3=b*z+c) : (m6 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 6 := by
  rw [step6,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 2 _ _ _ _ (ev5 b c d e j z hz) (ev4 b c d e j z hz) (ev3 b c d e j z hz) (ev2 b c d e j z hz)

theorem ev7 (hz : z^3=b*z+c) : (m7 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 7 := by
  rw [step7,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 3 _ _ _ _ (ev6 b c d e j z hz) (ev5 b c d e j z hz) (ev4 b c d e j z hz) (ev3 b c d e j z hz)

theorem ev8 (hz : z^3=b*z+c) : (m8 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 8 := by
  rw [step8,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 4 _ _ _ _ (ev7 b c d e j z hz) (ev6 b c d e j z hz) (ev5 b c d e j z hz) (ev4 b c d e j z hz)


theorem excludes : Case 0 := by
  intro m x d e j hx hc hv hraw hm
  let b := coeffB x
  let c := coeffC x
  have h0 := hraw 0 (by decide)
  change mass m (fun _ => 1) = 0 at h0
  have h1m := hraw 1 (by decide)
  have h1 : mass m x = 0 := by
    simp only [mass,Fin.sum_univ_three,rawMoment] at h1m ⊢
    linear_combination (1/3:ℝ)*h1m
  have hk := mass_quadratic_ne m x b hm hx h0 h1
  apply chartH_ne x d e j hc hx hv
  apply Certificate.w0_excludes
  · have h : mass m (fun i => (m4 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 4) :=
               congrArg (mass m) (funext (fun i => ev4 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 4 (by decide)
    rw [mass_rep m x b (m4 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G0 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m5 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 5) :=
               congrArg (mass m) (funext (fun i => ev5 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 5 (by decide)
    rw [mass_rep m x b (m5 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G1 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m6 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 6) :=
               congrArg (mass m) (funext (fun i => ev6 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 6 (by decide)
    rw [mass_rep m x b (m6 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G2 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m7 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 7) :=
               congrArg (mass m) (funext (fun i => ev7 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 7 (by decide)
    rw [mass_rep m x b (m7 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G3 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m8 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 8) :=
               congrArg (mass m) (funext (fun i => ev8 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 8 (by decide)
    rw [mass_rep m x b (m8 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G4 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)

end SparseCubes.Chart.Chart0

namespace SparseCubes.Chart.Chart1


variable (b c d e j : ℝ)

open SparseCubes.Certificate

namespace Reflection

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm4u : Tower 5 := [[[[],[[],[],[729,162,9]],[[189],[162,18]],[[9]]],[[[],[-864,-162,-9],[162,18]],[[],[18]]],[[[-9]]]],[[[[],[],[1161,270,18]],[[486,108,9],[270,36]],[[18]]],[[[-108,-18],[18]]]],[[[[81],[108,18]],[[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm4l : Tower 5 := [[[[[],[],[],[729,162,9]],[[],[1350,270,18],[162,18]],[[108,18],[9]]],[[[-216,-108,-9],[-54]],[[-9]]]],[[[[],[486,108,9],[162,18]],[[108,18],[18]]],[[[-9]]]],[[[[],[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm5u : Tower 5 := [[[[],[[],[],[],[6561,2187,243,9]],[[],[5346,594],[2187,486,27]],[[594],[243,27]],[[9]]],[[[],[],[-11502,-1971,-108],[2187,486,27]],[[-3240,-378,135,9],[810,270,27],[486,54]],[[135,27],[27]]],[[[-216,-270,-27],[-108]],[[-18]]]],[[[[],[],[],[16281,5211,621,27]],[[],[12960,4428,513,27],[5211,1242,81]],[[1404,270,27],[621,81]],[[27]]],[[[-1944,-810,-135,-9],[-1998,-216],[486,54]],[[],[54]]],[[[-18]]]],[[[[],[2430,810,135,9],[3024,756,54]],[[810,270,27],[513,81]],[[27]]],[[[-135,-27],[27]]]],[[[[],[135,27]],[[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm5l : Tower 5 := [[[[[],[],[],[],[6561,2187,243,9]],[[],[],[21627,5805,621,27],[2187,486,27]],[[2835,594],[3618,756,54],[243,27]],[[135,27],[9]]],[[[],[-5184,-3024,-378,-18],[837,270,27]],[[-594],[27,27]]],[[[-135,-27],[9]]]],[[[[],[],[10125,3834,513,27],[2187,486,27]],[[2430,810,135,9],[4428,1026,81],[486,54]],[[270,54],[27]]],[[[-810,-270,-27],[27,27]],[[-9]]]],[[[[243],[810,270,27],[243,27]],[[135,27],[27]]],[[[-9]]]],[[[[],[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm6u : Tower 5 := [[[[],[[],[],[],[],[59049,26244,4374,324,9]],[[],[],[115911,25758,1431],[26244,8748,972,36]],[[4941],[25758,2862],[4374,972,54]],[[1431],[324,36]],[[9]]],[[[],[],[],[-150336,-19440,1215,324,18],[26244,8748,972,36]],[[],[-127332,-24786,3942,810,36],[32562,14040,1944,108],[8748,1944,108]],[[-5832,-432,486,36],[8451,1944,162],[972,108]],[[324,72],[36]]],[[[10368,5832,216,-162,-9],[-12636,-11610,-1458,-72],[1431,486,54]],[[-1215,-486,-54],[-162,36]],[[-18]]],[[[-162,-36],[9]]]],[[[[],[],[],[],[234009,91368,14553,1134,36]],[[],[],[305694,134136,20061,1458,54],[91368,29106,3402,144]],[[25515,10692,1431],[69012,19764,1944,108],[14553,3402,216]],[[4077,486,54],[1134,144]],[[36]]],[[[],[-72900,-38394,-7236,-486,-18],[-25758,4860,1458,108],[8748,1944,108]],[[-16524,-3294,486,36],[4860,1944,216],[1944,216]],[[486,108],[108]]],[[[-999,-972,-108],[-162,36]],[[-45]]]],[[[[],[],[69255,37422,8235,810,36],[65124,20358,2430,108]],[[10935,4860,1215,162,9],[48114,19332,2430,144],[15984,3888,270]],[[3861,972,108],[1458,216]],[[54]]],[[[-4860,-2430,-486,-36],[-3591,0,54],[972,108]],[[],[108]]],[[[-27]]]],[[[[729],[4860,2430,486,36],[5805,1458,108]],[[1215,486,54],[810,144]],[[36]]],[[[-162,-36],[36]]]],[[[[],[162,36]],[[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm6l : Tower 5 := [[[[[],[],[],[],[],[59049,26244,4374,324,9]],[[],[],[],[349920,117126,15984,1134,36],[26244,8748,972,36]],[[],[111051,36450,2862],[90882,23220,2430,108],[4374,972,54]],[[10692,2862],[7236,1458,108],[324,36]],[[162,36],[9]]],[[[],[],[-120528,-70956,-10395,-648,-18],[38880,11610,1458,72]],[[-25272,-16524,-1647,162,9],[-20898,-432,486,36],[7236,1944,162]],[[-1647,486,54],[486,108]],[[18]]],[[[5832,432,-486,-36],[-6021,-972,-54],[324,36]],[[-324,-72],[36]]],[[[-9]]]],[[[[],[],[],[199584,97686,17199,1458,54],[26244,8748,972,36]],[[],[94770,48114,9666,810,36],[123444,37260,4374,216],[8748,1944,108]],[[15552,5292,486,36],[15687,3402,270],[972,108]],[[486,108],[36]]],[[[-4536,-4860,-1215,-162,-9],[-33534,-12042,-972,-36],[7236,1944,162]],[[-2862],[648,180]],[[18]]],[[[-324,-72],[27]]]],[[[[],[10935,4860,1215,162,9],[32562,14040,1944,108],[4374,972,54]],[[4860,2430,486,36],[9666,2430,216],[972,108]],[[486,108],[54]]],[[[-1215,-486,-54],[162,72]],[[-9]]]],[[[[],[1215,486,54],[324,36]],[[162,36],[36]]],[[[-9]]]],[[[[],[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm7u : Tower 5 := [[[[],[[],[],[],[],[],[531441,295245,65610,7290,405,9]],[[],[],[],[2283228,761076,84564,3132],[295245,131220,21870,1620,45]],[[],[267543,29727],[761076,169128,9396],[65610,21870,2430,90]],[[29727],[84564,9396],[7290,1620,90]],[[3132],[405,45]],[[9]]],[[[],[],[],[],[-1864782,-72333,102222,18441,1377,45],[295245,131220,21870,1620,45]],[[],[],[-3452544,-820368,83187,32805,2754,90],[983988,504792,86589,7128,270],[131220,43740,4860,180]],[[-132678,23085,30051,3132],[-252477,-162,30618,3888,180],[336960,95985,10692,540],[21870,4860,270]],[[8505,5103,1134,90],[27837,5508,450],[1620,180]],[[567,135],[45]]],[[[],[513216,335016,30132,-7074,-972,-36],[-557928,-395928,-55971,-3240,-90],[110808,29808,3564,180]],[[-52812,-60102,-9396],[-89019,-34101,-2430,-90],[15228,3888,360]],[[-6264],[324,180]]],[[[21546,4293,-1134,-90],[-11367,-1620,-90],[405,45]],[[-567,-135],[45]]],[[[-9]]]],[[[[],[],[],[],[],[3523257,1607445,307638,31806,1809,45]],[[],[],[],[6910920,3657636,693603,62775,3186,90],[1607445,615276,95418,7236,225]],[[],[1321677,742365,144666,9396],[2345436,903150,114777,7128,270],[307638,95418,10854,450]],[[141993,60102,9396],[275157,63099,4698,270],[31806,7236,450]],[[11097,756,90],[1809,225]],[[45]]],[[[],[],[-2204496,-1380240,-295569,-21519,-432],[-105300,356400,90234,8640,360],[131220,43740,4860,180]],[[-265356,-173502,-43092,-2862,378,18],[-831546,-195372,22032,5400,270],[303912,139644,18792,1080],[43740,9720,540]],[[-34587,-3483,3402,270],[49410,11664,1080],[4860,540]],[[1512,360],[180]]],[[[61236,26082,-810,-1512,-90],[-101979,-63909,-5994,-270],[15228,3888,360]],[[-8235,-2268,-270],[243,315]],[[-45]]],[[[-567,-135],[36]]]],[[[[],[],[],[1803060,1249344,336879,42201,2754,90],[1312200,484056,73548,5616,180]],[[],[586845,403137,123039,18171,1161,45],[1849716,902988,145395,11016,450],[418446,125226,14418,630]],[[137781,77112,14499,756,45],[305127,103113,10530,630],[51678,11988,810]],[[14499,2268,270],[3186,450]],[[90]]],[[[-39366,-25515,-8505,-1701,-189,-9],[-301077,-178038,-34101,-1620,-45],[-33048,43659,8100,540],[21870,4860,270]],[[-51597,-13689,1134,90],[15309,6804,810],[4860,540]],[[1134,270],[270]]],[[[-1971,-2268,-270],[-81,135]],[[-81]]]],[[[[],[45927,25515,8505,1701,189,9],[265356,168966,40014,3888,180],[176418,51678,5994,270]],[[25515,17010,5103,756,45],[123039,54513,6966,450],[37098,8748,630]],[[8235,2268,270],[2754,450]],[[90]]],[[[-8505,-5103,-1134,-90],[-6264,648,180],[1620,180]],[[],[180]]],[[[-36]]]],[[[[],[8505,5103,1134,90],[9936,2376,180]],[[1701,756,90],[1161,225]],[[45]]],[[[-189,-45],[45]]]],[[[[],[189,45]],[[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm7l : Tower 5 := [[[[[],[],[],[],[],[],[531441,295245,65610,7290,405,9]],[[],[],[],[],[5806485,2368521,392202,34938,1809,45],[295245,131220,21870,1620,45]],[[],[],[3236760,1391175,199179,9396],[2073276,653184,82944,5616,180],[65610,21870,2430,90]],[[103761,29727],[630099,229230,18792],[260982,61074,5994,270],[7290,1620,90]],[[30051,9396],[13068,2376,180],[405,45]],[[189,45],[9]]],[[[],[],[],[-2824632,-1647216,-272160,-17442,-432],[1016955,352836,51678,3996,135]],[[],[-1253880,-992412,-166293,-621,1161,45],[-495720,-162,30618,3888,180],[287226,81486,9558,450]],[[-86751,-43092,-4293,756,45],[-54594,30618,5832,360],[29808,7128,540]],[[-2862,1512,180],[1566,270]],[[45]]],[[[31104,57024,21546,1431,-189,-9],[277992,17172,-25515,-3132,-135],[-185004,-26163,-1296],[7290,1620,90]],[[-8505,-5103,-1134,-90],[-21033,-2484,-90],[1620,180]],[[-378,-90],[90]]],[[[1431,-756,-90],[-216]],[[-36]]]],[[[[],[],[],[],[3941703,2296188,494424,53379,3186,90],[295245,131220,21870,1620,45]],[[],[],[3020976,1961982,481545,51597,2754,90],[3057264,1157976,169533,12744,450],[131220,43740,4860,180]],[[178605,112266,30051,3132],[1007721,458298,68202,3888,180],[597942,157059,16686,810],[21870,4860,270]],[[68607,23895,1134,90],[40905,7884,630],[1620,180]],[[756,180],[45]]],[[[],[-227448,-322380,-106029,-14769,-783,-27],[-1053648,-396090,-25353,648,90],[287226,81486,9558,450]],[[-169290,-103194,-13689,756,45],[-135108,1620,4536,360],[52326,12636,990]],[[-7425,2268,270],[3078,630]],[[90]]],[[[13041,-810,-2268,-180],[-21033,-2484,-90],[1215,135]],[[-945,-225],[135]]],[[[-27]]]],[[[[],[],[408240,290871,92988,15039,1161,45],[983988,504792,86589,7128,270],[65610,21870,2430,90]],[[45927,25515,8505,1701,189,9],[403137,246078,54513,4644,225],[412938,130896,15390,810],[21870,4860,270]],[[47061,19602,2268,180],[44307,9396,810],[2430,270]],[[1134,270],[90]]],[[[-25515,-17010,-5103,-756,-45],[-80514,-28998,-1296],[22518,5508,450]],[[-6264],[1863,495]],[[45]]],[[[-567,-135],[54]]]],[[[[2187],[25515,17010,5103,756,45],[75978,34911,4698,270],[7290,1620,90]],[[8505,5103,1134,90],[18171,4644,450],[1620,180]],[[756,180],[90]]],[[[-1701,-756,-90],[351,135]],[[-9]]]],[[[[],[1701,756,90],[405,45]],[[189,45],[45]]],[[[-9]]]],[[[[],[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm8u : Tower 5 := [[[[],[[],[],[],[],[],[],[4782969,3188646,885735,131220,10935,486,9]],[[],[],[],[],[43046721,19131876,3188646,236196,6561],[3188646,1771470,393660,43740,2430,54]],[[],[],[9959598,2213244,122958],[19131876,6377292,708588,26244],[885735,393660,65610,4860,135]],[[132921],[2213244,245916],[3188646,708588,39366],[131220,43740,4860,180]],[[122958],[236196,26244],[10935,2430,135]],[[6561],[486,54]],[[9]]],[[[],[],[],[],[],[-19210608,4772034,3943647,742932,66420,3294,81],[3188646,1771470,393660,43740,2430,54]],[[],[],[],[-81218376,-19860876,2549556,1215324,137376,7020,180],[27092556,16036056,3331044,335664,18900,540],[1771470,787320,131220,9720,270]],[[],[-9039600,749412,2381886,461700,26244],[-6476436,2063556,1732104,266328,16200,540],[11206674,4039632,542862,37800,1350],[393660,131220,14580,540]],[[-528768,229392,225504,26244],[1088640,736776,164268,11340,540],[1451520,344412,32940,1620],[43740,9720,540]],[[88776,35316,2160,180],[70794,11610,945],[2430,270]],[[864,216],[54]]],[[[],[],[17449344,12118896,1294704,-252396,-51192,-3024,-81],[-20141784,-12621420,-2049948,-121824,-2700],[3877551,1233468,163296,11880,405]],[[1244160,466560,-301320,-136728,-10854,216,9],[-4082400,-4924152,-1118772,-69660,1080,54],[-4074138,-1615464,-103518,1620,270],[971028,239112,25920,1260]],[[-424278,-410184,-65124,2160,135],[-431568,-25272,6480,540],[75816,16200,1350]],[[-21708,2160,270],[2160,540]],[[45]]],[[[62208,373248,184680,17172,-1080,-54],[1360800,238140,-71928,-9180,-405],[-490536,-60912,-2700],[10935,2430,135]],[[47952,8100,-4320,-360],[-59454,-6210,-270],[2430,270]],[[-1080,-270],[135]]],[[[4293,-1080,-135],[-270]],[[-45]]]],[[[[],[],[],[],[],[],[55801305,29406402,6534756,804816,60021,2646,54]],[[],[],[],[],[154354086,95134500,22319793,2567700,159246,5940,135],[29406402,13069512,2414448,240084,13230,324]],[[],[],[49270194,33536916,8346078,934092,39366],[68916744,33341544,5682312,440640,18900,540],[6534756,2414448,360126,26460,810]],[[1245132,713448,122958],[10844604,5763960,1159596,78732],[11907486,4055184,432054,21060,810],[804816,240084,26460,1080]],[[606528,225504,39366],[940572,179172,9180,540],[60021,13230,810]],[[28512,1080,135],[2646,324]],[[54]]],[[[],[],[],[-61210728,-43558236,-10577304,-937980,-10530,2160,90],[8835480,14396778,3932712,448740,27000,810],[1771470,787320,131220,9720,270]],[[],[-17146080,-13384440,-3857868,-377784,11340,3132,108],[-27748656,-5994324,1193616,372276,29700,1080],[13018968,6815664,1098360,84240,3240],[787320,262440,29160,1080]],[[-1895400,-533628,81648,18144,2160,108],[-1428840,423792,362556,38340,1890],[2882952,850500,90720,4860],[131220,29160,1620]],[[68040,45360,10800,900],[200880,36720,3240],[9720,1080]],[[3240,810],[270]]],[[[590976,653184,258552,47952,2025,-432,-18],[3569184,1265544,-273132,-131220,-10260,-378],[-5687658,-3033612,-292572,-8100],[971028,239112,25920,1260]],[[-403380,-491832,-92340,-2160,-135],[-809676,-245916,-8100],[140697,29970,2565]],[[-45927],[4050,1350]],[[45]]],[[[109512,25272,-6480,-540],[-59454,-6210,-270],[1944,216]],[[-2376,-594],[216]]],[[[-36]]]],[[[[],[],[],[],[45683757,37603764,12000798,1848744,150498,7020,180],[26217756,11298042,2020788,196344,10800,270]],[[],[],[24035130,21143916,7758504,1384128,115911,4590,135],[60296076,34929792,7188912,680724,35100,1080],[10412307,3647916,523422,38340,1215]],[[1071630,898128,360612,75168,6561],[11346156,7797384,1937196,197316,6750,270],[14977062,6495876,870912,53460,2160],[1627128,457812,50220,2160]],[[895212,491832,92340,2160,135],[1418148,389124,29700,1800],[130734,28620,1890]],[[48438,4320,540],[5940,810]],[[135]]],[[[],[-2694384,-2469852,-1037610,-231984,-25110,-918,-27],[-12979116,-8563320,-1718496,-68040,4050,270],[1812294,2776032,555498,46440,1890],[393660,131220,14580,540]],[[-1551312,-1238328,-369360,-34344,2160,108],[-3402000,-886464,88452,24300,1350],[1411344,667764,82620,4860],[131220,29160,1620]],[[-143856,-24300,12960,1080],[177876,40500,4050],[14580,1620]],[[4320,1080],[540]]],[[[207522,103032,-1458,-6480,-405],[-378108,-220644,-14580,-540],[64881,13770,1215]],[[-26730,-6480,-810],[2106,1134]],[[-81]]],[[[-1296,-324],[90]]]],[[[[],[],[2173878,1939140,830088,197640,25353,1566,54],[10511208,7965540,2215188,266328,16200,540],[4763286,1627128,228906,16740,540]],[[183708,122472,51030,13608,2268,216,9],[2837268,2381400,818424,127656,7830,324],[6986250,3660552,603126,43740,1890],[1364688,370332,40500,1800]],[[462672,307152,66582,4320,270],[972972,354780,34020,2160],[141426,30780,2160]],[[39852,6480,810],[7020,1080]],[[180]]],[[[-122472,-102060,-40824,-9072,-1080,-54],[-884520,-573480,-109836,-2700],[-20088,161676,24840,1620],[43740,9720,540]],[[-136728,-43416,2160,180],[36288,17280,2160],[9720,1080]],[[2160,540],[540]]],[[[-2511,-4320,-540],[216,324]],[[-126]]]],[[[[6561],[122472,102060,40824,9072,1080,54],[728028,511272,124902,11340,540],[411156,108864,11880,540]],[[51030,40824,13608,2160,135],[272808,127656,15660,1080],[76059,16470,1215]],[[15633,4320,540],[4590,810]],[[135]]],[[[-13608,-9072,-2160,-180],[-11502,1890,405],[2430,270]],[[],[270]]],[[[-45]]]],[[[[],[13608,9072,2160,180],[16281,3510,270]],[[2268,1080,135],[1566,324]],[[54]]],[[[-216,-54],[54]]]],[[[[],[216,54]],[[9]]]]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm8l : Tower 5 := [[[[[],[],[],[],[],[],[],[4782969,3188646,885735,131220,10935,486,9]],[[],[],[],[],[],[98848026,48538278,9723402,1041012,66582,2646,54],[3188646,1771470,393660,43740,2430,54]],[[],[],[],[84676266,44037432,8775702,783756,26244],[45349632,17675334,2729376,222588,10800,270],[885735,393660,65610,4860,135]],[[],[6952716,2926692,245916],[24905556,11174112,1642680,78732],[7951932,2335716,268272,16740,540],[131220,43740,4860,180]],[[713448,245916],[2398410,934092,78732],[647352,135108,11880,540],[10935,2430,135]],[[75168,26244],[22842,3510,270],[486,54]],[[216,54],[9]]],[[[],[],[],[],[-65623608,-38398860,-7130349,-482760,-2187,1080,45],[23029110,9526572,1627128,152604,8370,216]],[[],[],[-44626464,-39290184,-8564778,-484056,37179,4590,135],[-8620668,1588248,1506600,240084,16200,540],[8640837,2860596,392202,28620,945]],[[-1866240,-1242216,-8262,75168,6561],[-5916564,-3238704,-381996,39852,6750,270],[-119070,1732104,399492,32400,1350],[1233468,326592,35640,1620]],[[-194886,40824,13608,2160,135],[5184,157464,20520,1260],[86994,18900,1350]],[[243,3240,405],[3510,540]],[[81]]],[[[],[1804032,3888000,1734048,202500,-3402,-1350,-45],[8293104,-505440,-1180008,-173988,-9450,-270],[-4697190,-631800,6318,4320,270],[131220,43740,4860,180]],[[528768,-229392,-225504,-26244],[-986580,-655128,-137052,-7020,-270],[-824256,-47628,3780,540],[43740,9720,540]],[[-150336,-52488],[-32076,-540,270],[4860,540]],[[],[180]]],[[[186624,184680,25758,-2160,-135],[17820,-65124,-7020,-360],[5346,1080,135]],[[6318,-3240,-405],[-864,54]],[[-81]]],[[[-216,-54],[9]]]],[[[[],[],[],[],[],[79637418,53310312,13667049,1783944,133002,5940,135],[3188646,1771470,393660,43740,2430,54]],[[],[],[],[88134156,68213988,20100960,2782836,189864,7020,180],[72442188,33711390,6060420,558252,29700,810],[1771470,787320,131220,9720,270]],[[],[11818548,9529488,3119634,461700,26244],[43334676,24411780,5017464,423792,16200,540],[19158606,6375348,811134,54540,1890],[393660,131220,14580,540]],[[1611576,967140,225504,26244],[5885460,2604960,321732,11340,540],[2098872,479520,44820,2160],[43740,9720,540]],[[239112,87804,2160,180],[93636,15120,1215],[2430,270]],[[1080,270],[54]]],[[[],[],[-9727776,-15052392,-5975370,-988848,-65205,-1458,-27],[-28762452,-11033172,-543348,118260,13500,540],[8640837,2860596,392202,28620,945]],[[-1244160,-1551312,-619164,-123120,-8586,432,18],[-12089736,-8306712,-1459944,-20736,8910,378],[-3465180,627912,420876,45360,2160],[2335716,609444,66420,3060]],[[-814050,-328536,-37908,6480,405],[-167184,250776,40500,2700],[217242,46980,3510]],[[-8100,8640,1080],[9180,1620]],[[225]]],[[[653184,517104,143856,8100,-2160,-108],[374220,-416988,-208980,-16200,-675],[-824256,-47628,3780,540],[32805,7290,405]],[[-115992,-53460,-6480,-540],[-86994,-4590,270],[7290,810]],[[-1080,-270],[405]]],[[[6318,-3240,-405],[-594,54]],[[-126]]]],[[[[],[],[],[13461714,12327876,4761828,922428,89667,4590,135],[27092556,16036056,3331044,335664,18900,540],[885735,393660,65610,4860,135]],[[],[3245508,2837268,1190700,272808,31914,1566,54],[20245788,14795784,3926880,437400,22950,810],[14461416,5743548,817452,58860,2160],[393660,131220,14580,540]],[[1020600,823284,266328,35316,1080,54],[4626720,2448468,420876,24840,1215],[2412504,627912,63180,3240],[65610,14580,810]],[[266328,105948,6480,540],[146124,25380,2160],[4860,540]],[[2160,540],[135]]],[[[-31104,-122472,-51030,-13608,-2268,-216,-9],[-2347380,-1973160,-655128,-91368,-3510,-108],[-3346110,-1104192,21384,12960,810],[1102248,282852,30780,1440]],[[-670194,-410184,-65124,2160,135],[-349920,29160,19440,1620],[184437,39690,3105]],[[-19197,6480,810],[8910,1890]],[[225]]],[[[34344,-972,-6480,-540],[-54918,-4050],[2916,324]],[[-1944,-486],[324]]],[[[-54]]]],[[[[],[183708,122472,51030,13608,2268,216,9],[1816668,1558116,552096,92340,6750,270],[3254742,1703916,274590,21060,810],[131220,43740,4860,180]],[[122472,102060,40824,9072,1080,54],[1190700,818424,191484,15660,810],[1117800,357696,39420,2160],[43740,9720,540]],[[115992,53460,6480,540],[104976,20520,1890],[4860,540]],[[2160,540],[180]]],[[[-51030,-40824,-13608,-2160,-135],[-177552,-64152,-540,180],[54189,11610,945]],[[-13122],[3834,1026]],[[81]]],[[[-864,-216],[90]]]],[[[[],[51030,40824,13608,2160,135],[156816,74196,9180,540],[10935,2430,135]],[[13608,9072,2160,180],[31914,7830,810],[2430,270]],[[1080,270],[135]]],[[[-2268,-1080,-135],[594,216]],[[-9]]]],[[[[],[2268,1080,135],[486,54]],[[216,54],[54]]],[[[-9]]]],[[[[],[9]]]]]



end Reflection

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r0 (b c d e j : ℝ) : Rep :=
  ⟨(((e*(54 + (j*6))) + (d*6)) + (b*6)),(12 + (j*6)),6⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r1 (b c d e j : ℝ) : Rep :=
  ⟨((((e*(e*(-891 + (j*(-198 + (j*(-11))))))) + (d*((30 + (e*(-198 + (j*(-22))))) + (d*(-11))))) + (c*(-54 + (j*(-22))))) + (b*((((-54 + (j*(-54 + (j*(-11))))) + (e*(-198 + (j*(-22))))) + (d*(-22))) + (b*(-11))))),((((e*(-456 + (j*(-252 + (j*(-22)))))) + (d*(-54 + (j*(-22))))) + (c*(-11))) + (b*(-54 + (j*(-22))))),((((-84 + (j*(-54 + (j*(-11))))) + (e*(-198 + (j*(-22))))) + (d*(-22))) + (b*(-11)))⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r2 (b c d e j : ℝ) : Rep :=
  ⟨((((e*(e*(e*(4374 + (j*(1458 + (j*(162 + (j*6))))))))) + (d*((e*((-810 + (j*(-90))) + (e*(1458 + (j*(324 + (j*18))))))) + (d*((-90 + (e*(162 + (j*18)))) + (d*6)))))) + (c*((((288 + (j*(252 + (j*(66 + (j*6)))))) + (e*(1098 + (j*(456 + (j*36)))))) + (d*(132 + (j*36)))) + (c*6)))) + (b*((((e*((1278 + (j*(1260 + (j*(294 + (j*18)))))) + (e*(1458 + (j*(324 + (j*18))))))) + (d*(((72 + (j*(132 + (j*18)))) + (e*(324 + (j*36)))) + (d*18)))) + (c*(132 + (j*36)))) + (b*((((162 + (j*(132 + (j*18)))) + (e*(162 + (j*18)))) + (d*18)) + (b*6)))))),((((e*(e*(4536 + (j*(2556 + (j*(390 + (j*18)))))))) + (d*(((-180 + (j*(-90))) + (e*(1098 + (j*(456 + (j*36)))))) + (d*(66 + (j*18)))))) + (c*(((252 + (j*(132 + (j*18)))) + (e*(162 + (j*18)))) + (d*18)))) + (b*(((((108 + (j*(162 + (j*(66 + (j*6)))))) + (e*(1098 + (j*(456 + (j*36)))))) + (d*(132 + (j*36)))) + (c*12)) + (b*(66 + (j*18)))))),((((e*((2088 + (j*(1350 + (j*(294 + (j*18)))))) + (e*(1458 + (j*(324 + (j*18))))))) + (d*(((162 + (j*(132 + (j*18)))) + (e*(324 + (j*36)))) + (d*18)))) + (c*(66 + (j*18)))) + (b*((((162 + (j*(132 + (j*18)))) + (e*(162 + (j*18)))) + (d*18)) + (b*6))))⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def r3 (b c d e j : ℝ) : Rep :=
  ⟨(((d*((e*(e*(4374 + (j*(972 + (j*54)))))) + (d*((-81 + (e*(972 + (j*108)))) + (d*54))))) + (c*(((e*((-3456 + (j*(-2916 + (j*(-738 + (j*(-54))))))) + (e*(-3402 + (j*(-864 + (j*(-54)))))))) + (d*(((-162 + (j*(-198 + (j*(-54))))) + (e*(-864 + (j*(-108))))) + (d*(-54))))) + (c*(-153 + (j*(-54))))))) + (b*((((e*(e*(-5670 + (j*(-4914 + (j*(-963 + (j*(-54))))))))) + (d*(((270 + (j*(270 + (j*54)))) + (e*(-540 + (j*(-954 + (j*(-108))))))) + (d*(9 + (j*(-54))))))) + (c*(((-594 + (j*(-504 + (j*(-108))))) + (e*(-864 + (j*(-108))))) + (d*(-108))))) + (b*(((((-81 + (j*(-162 + (j*(-99 + (j*(-18))))))) + (e*(-1512 + (j*(-1062 + (j*(-108))))))) + (d*(-144 + (j*(-108))))) + (c*(-54))) + (b*(-99 + (j*(-54))))))))),((((e*(e*(e*(-8748 + (j*(-3402 + (j*(-432 + (j*(-18)))))))))) + (d*((e*((2268 + (j*(1242 + (j*108)))) + (e*(-3402 + (j*(-864 + (j*(-54)))))))) + (d*(((270 + (j*108)) + (e*(-432 + (j*(-54))))) + (d*(-18))))))) + (c*((((-432 + (j*(-432 + (j*(-153 + (j*(-18))))))) + (e*(-2484 + (j*(-1170 + (j*(-108))))))) + (d*(-252 + (j*(-108))))) + (c*(-18))))) + (b*((((e*((-1188 + (j*(-1674 + (j*(-630 + (j*(-54))))))) + (e*(-3402 + (j*(-864 + (j*(-54)))))))) + (d*(((108 + (j*(-90 + (j*(-54))))) + (e*(-864 + (j*(-108))))) + (d*(-54))))) + (c*(-252 + (j*(-108))))) + (b*((((-162 + (j*(-198 + (j*(-54))))) + (e*(-432 + (j*(-54))))) + (d*(-54))) + (b*(-18))))))),((((e*(e*(-10044 + (j*(-5886 + (j*(-1017 + (j*(-54))))))))) + (d*(((432 + (j*(270 + (j*54)))) + (e*(-1512 + (j*(-1062 + (j*(-108))))))) + (d*(-45 + (j*(-54))))))) + (c*(((-432 + (j*(-306 + (j*(-54))))) + (e*(-432 + (j*(-54))))) + (d*(-54))))) + (b*(((((j*(-162 + (j*(-99 + (j*(-18)))))) + (e*(-1512 + (j*(-1062 + (j*(-108))))))) + (d*(-144 + (j*(-108))))) + (c*(-36))) + (b*(-99 + (j*(-54)))))))⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m0 (b c d e j : ℝ) : Rep :=
  ⟨1,0,0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m1 (b c d e j : ℝ) : Rep :=
  ⟨0,3,0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m2 (b c d e j : ℝ) : Rep :=
  ⟨((d*9) + (b*9)),(e*9),0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m3 (b c d e j : ℝ) : Rep :=
  ⟨(((d*((e*(81 + (j*9))) + (d*9))) + (c*((-54 + (j*(-9))) + (e*9)))) + (b*((e*(81 + (j*9))) + (d*9)))),((((e*(e*(81 + (j*9)))) + (d*((81 + (j*9)) + (e*9)))) + (c*(-9))) + (b*(27 + (e*9)))),0⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m4 (b c d e j : ℝ) : Rep :=
  ⟨interp 5 Reflection.pm4u (point b c d e j),interp 5 Reflection.pm4l (point b c d e j),9*(Certificate.w1G0 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m5 (b c d e j : ℝ) : Rep :=
  ⟨interp 5 Reflection.pm5u (point b c d e j),interp 5 Reflection.pm5l (point b c d e j),9*(Certificate.w1G1 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m6 (b c d e j : ℝ) : Rep :=
  ⟨interp 5 Reflection.pm6u (point b c d e j),interp 5 Reflection.pm6l (point b c d e j),9*(Certificate.w1G2 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m7 (b c d e j : ℝ) : Rep :=
  ⟨interp 5 Reflection.pm7u (point b c d e j),interp 5 Reflection.pm7l (point b c d e j),9*(Certificate.w1G3 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m8 (b c d e j : ℝ) : Rep :=
  ⟨interp 5 Reflection.pm8u (point b c d e j),interp 5 Reflection.pm8l (point b c d e j),9*(Certificate.w1G4 b c d e j)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def m9 (b c d e j : ℝ) : Rep :=
  let t := linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j)
  ⟨t.u,t.l,9*(Certificate.w1G5 b c d e j)⟩

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart.Chart1.Reflection
open SparseCubes.Certificate


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def neg : (n : Nat) → Tower n → Tower n
  | 0,z => -z
  | n+1,z => z.map (neg n)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_neg (n) (u : Tower n) (v : Nat → ℝ) : interp n (neg n u) v = -interp n u v := by
  induction n generalizing v with
  | zero => simp [neg,interp]
  | succ n ih =>
    change value _ _ (u.map (neg n)) = -value _ _ u
    induction u with
    | nil => simp [value]
    | cons h t ht => simp only [List.map_cons,value,ih,ht]; ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pnine : Tower 5 := [[[[[9]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_nine (b c d e j : ℝ) : interp 5 pnine (point b c d e j)=9 := by simp [pnine,interp,value]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pb : Tower 5 := [[], [[[[1]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_b (b c d e j : ℝ) : interp 5 pb (point b c d e j) = b := by
  simp only [pb,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pc : Tower 5 := [[[], [[[1]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_c (b c d e j : ℝ) : interp 5 pc (point b c d e j) = c := by
  simp only [pc,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr0u : Tower 5 := [[[[[], [54, 6]], [[6]]]], [[[[6]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r0u (b c d e j : ℝ) : interp 5 pr0u (point b c d e j) = (r0 b c d e j).u := by
  simp only [pr0u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r0] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr0l : Tower 5 := [[[[[12, 6]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r0l (b c d e j : ℝ) : interp 5 pr0l (point b c d e j) = (r0 b c d e j).l := by
  simp only [pr0l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r0] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr0k : Tower 5 := [[[[[6]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r0k (b c d e j : ℝ) : interp 5 pr0k (point b c d e j) = (r0 b c d e j).k := by
  simp only [pr0k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r0] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr1u : Tower 5 := [[[[[], [], [-891, -198, -11]], [[30], [-198, -22]], [[-11]]], [[[-54, -22]]]], [[[[-54, -54, -11], [-198, -22]], [[-22]]]], [[[[-11]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r1u (b c d e j : ℝ) : interp 5 pr1u (point b c d e j) = (r1 b c d e j).u := by
  simp only [pr1u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r1] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr1l : Tower 5 := [[[[[], [-456, -252, -22]], [[-54, -22]]], [[[-11]]]], [[[[-54, -22]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r1l (b c d e j : ℝ) : interp 5 pr1l (point b c d e j) = (r1 b c d e j).l := by
  simp only [pr1l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r1] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr1k : Tower 5 := [[[[[-84, -54, -11], [-198, -22]], [[-22]]]], [[[[-11]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r1k (b c d e j : ℝ) : interp 5 pr1k (point b c d e j) = (r1 b c d e j).k := by
  simp only [pr1k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r1] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr2u : Tower 5 := [[[[[],[],[],[4374,1458,162,6]],[[],[-810,-90],[1458,324,18]],[[-90],[162,18]],[[6]]],[[[288,252,66,6],[1098,456,36]],[[132,36]]],[[[6]]]],[[[[],[1278,1260,294,18],[1458,324,18]],[[72,132,18],[324,36]],[[18]]],[[[132,36]]]],[[[[162,132,18],[162,18]],[[18]]]],[[[[6]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r2u (b c d e j : ℝ) : interp 5 pr2u (point b c d e j) = (r2 b c d e j).u := by
  simp only [pr2u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r2] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr2l : Tower 5 := [[[[[],[],[4536,2556,390,18]],[[-180,-90],[1098,456,36]],[[66,18]]],[[[252,132,18],[162,18]],[[18]]]],[[[[108,162,66,6],[1098,456,36]],[[132,36]]],[[[12]]]],[[[[66,18]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r2l (b c d e j : ℝ) : interp 5 pr2l (point b c d e j) = (r2 b c d e j).l := by
  simp only [pr2l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r2] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr2k : Tower 5 := [[[[[],[2088,1350,294,18],[1458,324,18]],[[162,132,18],[324,36]],[[18]]],[[[66,18]]]],[[[[162,132,18],[162,18]],[[18]]]],[[[[6]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r2k (b c d e j : ℝ) : interp 5 pr2k (point b c d e j) = (r2 b c d e j).k := by
  simp only [pr2k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r2] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr3u : Tower 5 := [[[[],[[],[],[4374,972,54]],[[-81],[972,108]],[[54]]],[[[],[-3456,-2916,-738,-54],[-3402,-864,-54]],[[-162,-198,-54],[-864,-108]],[[-54]]],[[[-153,-54]]]],[[[[],[],[-5670,-4914,-963,-54]],[[270,270,54],[-540,-954,-108]],[[9,-54]]],[[[-594,-504,-108],[-864,-108]],[[-108]]]],[[[[-81,-162,-99,-18],[-1512,-1062,-108]],[[-144,-108]]],[[[-54]]]],[[[[-99,-54]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r3u (b c d e j : ℝ) : interp 5 pr3u (point b c d e j) = (r3 b c d e j).u := by
  simp only [pr3u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r3] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr3l : Tower 5 := [[[[[],[],[],[-8748,-3402,-432,-18]],[[],[2268,1242,108],[-3402,-864,-54]],[[270,108],[-432,-54]],[[-18]]],[[[-432,-432,-153,-18],[-2484,-1170,-108]],[[-252,-108]]],[[[-18]]]],[[[[],[-1188,-1674,-630,-54],[-3402,-864,-54]],[[108,-90,-54],[-864,-108]],[[-54]]],[[[-252,-108]]]],[[[[-162,-198,-54],[-432,-54]],[[-54]]]],[[[[-18]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r3l (b c d e j : ℝ) : interp 5 pr3l (point b c d e j) = (r3 b c d e j).l := by
  simp only [pr3l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r3] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pr3k : Tower 5 := [[[[[],[],[-10044,-5886,-1017,-54]],[[432,270,54],[-1512,-1062,-108]],[[-45,-54]]],[[[-432,-306,-54],[-432,-54]],[[-54]]]],[[[[0,-162,-99,-18],[-1512,-1062,-108]],[[-144,-108]]],[[[-36]]]],[[[[-99,-54]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_r3k (b c d e j : ℝ) : interp 5 pr3k (point b c d e j) = (r3 b c d e j).k := by
  simp only [pr3k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,r3] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm0u : Tower 5 := [[[[[1]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m0u (b c d e j : ℝ) : interp 5 pm0u (point b c d e j) = (m0 b c d e j).u := by
  simp only [pm0u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m0] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm0l : Tower 5 := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m0l (b c d e j : ℝ) : interp 5 pm0l (point b c d e j) = (m0 b c d e j).l := by
  simp only [pm0l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m0] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm0k : Tower 5 := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m0k (b c d e j : ℝ) : interp 5 pm0k (point b c d e j) = (m0 b c d e j).k := by
  simp only [pm0k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m0] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm1u : Tower 5 := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m1u (b c d e j : ℝ) : interp 5 pm1u (point b c d e j) = (m1 b c d e j).u := by
  simp only [pm1u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m1] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm1l : Tower 5 := [[[[[3]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m1l (b c d e j : ℝ) : interp 5 pm1l (point b c d e j) = (m1 b c d e j).l := by
  simp only [pm1l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m1] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm1k : Tower 5 := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m1k (b c d e j : ℝ) : interp 5 pm1k (point b c d e j) = (m1 b c d e j).k := by
  simp only [pm1k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m1] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm2u : Tower 5 := [[[[], [[9]]]], [[[[9]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m2u (b c d e j : ℝ) : interp 5 pm2u (point b c d e j) = (m2 b c d e j).u := by
  simp only [pm2u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m2] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm2l : Tower 5 := [[[[[], [9]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m2l (b c d e j : ℝ) : interp 5 pm2l (point b c d e j) = (m2 b c d e j).l := by
  simp only [pm2l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m2] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm2k : Tower 5 := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m2k (b c d e j : ℝ) : interp 5 pm2k (point b c d e j) = (m2 b c d e j).k := by
  simp only [pm2k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m2] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm3u : Tower 5 := [[[[], [[], [81, 9]], [[9]]], [[[-54, -9], [9]]]], [[[[], [81, 9]], [[9]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m3u (b c d e j : ℝ) : interp 5 pm3u (point b c d e j) = (m3 b c d e j).u := by
  simp only [pm3u,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m3] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm3l : Tower 5 := [[[[[], [], [81, 9]], [[81, 9], [9]]], [[[-9]]]], [[[[27], [9]]]]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m3l (b c d e j : ℝ) : interp 5 pm3l (point b c d e j) = (m3 b c d e j).l := by
  simp only [pm3l,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m3] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def pm3k : Tower 5 := []
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m3k (b c d e j : ℝ) : interp 5 pm3k (point b c d e j) = (m3 b c d e j).k := by
  simp only [pm3k,interp,value,point,Int.cast_ofNat,Int.cast_neg,mul_zero,add_zero,zero_add,mul_one,m3] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m4u (b c d e j : ℝ) : interp 5 pm4u (point b c d e j) = (m4 b c d e j).u := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m4l (b c d e j : ℝ) : interp 5 pm4l (point b c d e j) = (m4 b c d e j).l := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev pm4k := Certificate.w1T0
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m4k_unscaled (b c d e j : ℝ) : interp 5 pm4k (point b c d e j) = Certificate.w1G0 b c d e j := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m4k (b c d e j : ℝ) : interp 5 (mul 5 pnine pm4k) (point b c d e j) = (m4 b c d e j).k := by
  rw [interp_mul,eval_nine,eval_m4k_unscaled]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m5u (b c d e j : ℝ) : interp 5 pm5u (point b c d e j) = (m5 b c d e j).u := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m5l (b c d e j : ℝ) : interp 5 pm5l (point b c d e j) = (m5 b c d e j).l := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev pm5k := Certificate.w1T1
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m5k_unscaled (b c d e j : ℝ) : interp 5 pm5k (point b c d e j) = Certificate.w1G1 b c d e j := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m5k (b c d e j : ℝ) : interp 5 (mul 5 pnine pm5k) (point b c d e j) = (m5 b c d e j).k := by
  rw [interp_mul,eval_nine,eval_m5k_unscaled]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m6u (b c d e j : ℝ) : interp 5 pm6u (point b c d e j) = (m6 b c d e j).u := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m6l (b c d e j : ℝ) : interp 5 pm6l (point b c d e j) = (m6 b c d e j).l := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev pm6k := Certificate.w1T2
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m6k_unscaled (b c d e j : ℝ) : interp 5 pm6k (point b c d e j) = Certificate.w1G2 b c d e j := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m6k (b c d e j : ℝ) : interp 5 (mul 5 pnine pm6k) (point b c d e j) = (m6 b c d e j).k := by
  rw [interp_mul,eval_nine,eval_m6k_unscaled]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m7u (b c d e j : ℝ) : interp 5 pm7u (point b c d e j) = (m7 b c d e j).u := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m7l (b c d e j : ℝ) : interp 5 pm7l (point b c d e j) = (m7 b c d e j).l := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev pm7k := Certificate.w1T3
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m7k_unscaled (b c d e j : ℝ) : interp 5 pm7k (point b c d e j) = Certificate.w1G3 b c d e j := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m7k (b c d e j : ℝ) : interp 5 (mul 5 pnine pm7k) (point b c d e j) = (m7 b c d e j).k := by
  rw [interp_mul,eval_nine,eval_m7k_unscaled]; rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m8u (b c d e j : ℝ) : interp 5 pm8u (point b c d e j) = (m8 b c d e j).u := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m8l (b c d e j : ℝ) : interp 5 pm8l (point b c d e j) = (m8 b c d e j).l := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev pm8k := Certificate.w1T4
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m8k_unscaled (b c d e j : ℝ) : interp 5 pm8k (point b c d e j) = Certificate.w1G4 b c d e j := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m8k (b c d e j : ℝ) : interp 5 (mul 5 pnine pm8k) (point b c d e j) = (m8 b c d e j).k := by
  rw [interp_mul,eval_nine,eval_m8k_unscaled]; rfl



set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
abbrev pm9k := Certificate.w1T5
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m9k_unscaled (b c d e j : ℝ) : interp 5 pm9k (point b c d e j) = Certificate.w1G5 b c d e j := rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eval_m9k (b c d e j : ℝ) : interp 5 (mul 5 pnine pm9k) (point b c d e j) = (m9 b c d e j).k := by
  rw [interp_mul,eval_nine,eval_m9k_unscaled]; rfl

end SparseCubes.Chart.Chart1.Reflection

namespace SparseCubes.Chart.Chart1
open SparseCubes.Certificate Reflection


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff4u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm0l)) (add 5 (mul 5 pc (mul 5 pr3l pm0k)) (add 5 (mul 5 pb (mul 5 pr3l pm0l)) (add 5 (mul 5 pr3u pm0u) (add 5 (mul 5 pc (mul 5 pr2k pm1l)) (add 5 (mul 5 pc (mul 5 pr2l pm1k)) (add 5 (mul 5 pb (mul 5 pr2l pm1l)) (add 5 (mul 5 pr2u pm1u) (add 5 (mul 5 pc (mul 5 pr1k pm2l)) (add 5 (mul 5 pc (mul 5 pr1l pm2k)) (add 5 (mul 5 pb (mul 5 pr1l pm2l)) (add 5 (mul 5 pr1u pm2u) (add 5 (mul 5 pc (mul 5 pr0k pm3l)) (add 5 (mul 5 pc (mul 5 pr0l pm3k)) (add 5 (mul 5 pb (mul 5 pr0l pm3l)) (add 5 (mul 5 pr0u pm3u) (neg 5 pm4u)))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero4u : isZero 5 diff4u = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct4u (b c d e j : ℝ) : (m4 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j)).u := by
  have h := interp_of_isZero 5 diff4u (point b c d e j) zero4u
  simp only [diff4u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m0k,eval_m0l,eval_m0u,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  simp only [linear4,Rep.add,Rep.mul]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff4l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm0k)) (add 5 (mul 5 pr3l pm0u) (add 5 (mul 5 pr3u pm0l) (add 5 (mul 5 pc (mul 5 pr2k pm1k)) (add 5 (mul 5 pr2l pm1u) (add 5 (mul 5 pr2u pm1l) (add 5 (mul 5 pc (mul 5 pr1k pm2k)) (add 5 (mul 5 pr1l pm2u) (add 5 (mul 5 pr1u pm2l) (add 5 (mul 5 pc (mul 5 pr0k pm3k)) (add 5 (mul 5 pr0l pm3u) (add 5 (mul 5 pr0u pm3l) (neg 5 pm4l)))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero4l : isZero 5 diff4l = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct4l (b c d e j : ℝ) : (m4 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j)).l := by
  have h := interp_of_isZero 5 diff4l (point b c d e j) zero4l
  simp only [diff4l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m0k,eval_m0l,eval_m0u,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  simp only [linear4,Rep.add,Rep.mul]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff4k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm0k))) (add 5 (mul 5 pr3l pm0l) (add 5 (mul 5 pr3k pm0u) (add 5 (mul 5 pr3u pm0k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k pm1k))) (add 5 (mul 5 pr2l pm1l) (add 5 (mul 5 pr2k pm1u) (add 5 (mul 5 pr2u pm1k) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k pm2k))) (add 5 (mul 5 pr1l pm2l) (add 5 (mul 5 pr1k pm2u) (add 5 (mul 5 pr1u pm2k) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k pm3k))) (add 5 (mul 5 pr0l pm3l) (add 5 (mul 5 pr0k pm3u) (add 5 (mul 5 pr0u pm3k) (neg 5 (mul 5 pnine pm4k))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero4k : isZero 5 diff4k = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct4k (b c d e j : ℝ) : (m4 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j)).k := by
  have h := interp_of_isZero 5 diff4k (point b c d e j) zero4k
  simp only [diff4k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m0k,eval_m0l,eval_m0u,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step4 (b c d e j : ℝ) : m4 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j) :=
  rep_ext (correct4u b c d e j) (correct4l b c d e j) (correct4k b c d e j)

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart.Chart1
open SparseCubes.Certificate Reflection


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff5u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm1l)) (add 5 (mul 5 pc (mul 5 pr3l pm1k)) (add 5 (mul 5 pb (mul 5 pr3l pm1l)) (add 5 (mul 5 pr3u pm1u) (add 5 (mul 5 pc (mul 5 pr2k pm2l)) (add 5 (mul 5 pc (mul 5 pr2l pm2k)) (add 5 (mul 5 pb (mul 5 pr2l pm2l)) (add 5 (mul 5 pr2u pm2u) (add 5 (mul 5 pc (mul 5 pr1k pm3l)) (add 5 (mul 5 pc (mul 5 pr1l pm3k)) (add 5 (mul 5 pb (mul 5 pr1l pm3l)) (add 5 (mul 5 pr1u pm3u) (add 5 (mul 5 pc (mul 5 pr0k pm4l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr0l pm4l)) (add 5 (mul 5 pr0u pm4u) (neg 5 pm5u)))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero5u : isZero 5 diff5u = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct5u (b c d e j : ℝ) : (m5 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j)).u := by
  have h := interp_of_isZero 5 diff5u (point b c d e j) zero5u
  simp only [diff5u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff5l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm1k)) (add 5 (mul 5 pr3l pm1u) (add 5 (mul 5 pr3u pm1l) (add 5 (mul 5 pc (mul 5 pr2k pm2k)) (add 5 (mul 5 pr2l pm2u) (add 5 (mul 5 pr2u pm2l) (add 5 (mul 5 pc (mul 5 pr1k pm3k)) (add 5 (mul 5 pr1l pm3u) (add 5 (mul 5 pr1u pm3l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm4k))) (add 5 (mul 5 pr0l pm4u) (add 5 (mul 5 pr0u pm4l) (neg 5 pm5l)))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero5l : isZero 5 diff5l = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct5l (b c d e j : ℝ) : (m5 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j)).l := by
  have h := interp_of_isZero 5 diff5l (point b c d e j) zero5l
  simp only [diff5l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff5k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm1k))) (add 5 (mul 5 pr3l pm1l) (add 5 (mul 5 pr3k pm1u) (add 5 (mul 5 pr3u pm1k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k pm2k))) (add 5 (mul 5 pr2l pm2l) (add 5 (mul 5 pr2k pm2u) (add 5 (mul 5 pr2u pm2k) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k pm3k))) (add 5 (mul 5 pr1l pm3l) (add 5 (mul 5 pr1k pm3u) (add 5 (mul 5 pr1u pm3k) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr0l pm4l) (add 5 (mul 5 pr0k pm4u) (add 5 (mul 5 pr0u (mul 5 pnine pm4k)) (neg 5 (mul 5 pnine pm5k))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero5k : isZero 5 diff5k = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct5k (b c d e j : ℝ) : (m5 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j)).k := by
  have h := interp_of_isZero 5 diff5k (point b c d e j) zero5k
  simp only [diff5k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step5 (b c d e j : ℝ) : m5 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) :=
  rep_ext (correct5u b c d e j) (correct5l b c d e j) (correct5k b c d e j)

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart.Chart1
open SparseCubes.Certificate Reflection


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff6u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm2l)) (add 5 (mul 5 pc (mul 5 pr3l pm2k)) (add 5 (mul 5 pb (mul 5 pr3l pm2l)) (add 5 (mul 5 pr3u pm2u) (add 5 (mul 5 pc (mul 5 pr2k pm3l)) (add 5 (mul 5 pc (mul 5 pr2l pm3k)) (add 5 (mul 5 pb (mul 5 pr2l pm3l)) (add 5 (mul 5 pr2u pm3u) (add 5 (mul 5 pc (mul 5 pr1k pm4l)) (add 5 (mul 5 pc (mul 5 pr1l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr1l pm4l)) (add 5 (mul 5 pr1u pm4u) (add 5 (mul 5 pc (mul 5 pr0k pm5l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm5k))) (add 5 (mul 5 pb (mul 5 pr0l pm5l)) (add 5 (mul 5 pr0u pm5u) (neg 5 pm6u)))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero6u : isZero 5 diff6u = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct6u (b c d e j : ℝ) : (m6 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j)).u := by
  have h := interp_of_isZero 5 diff6u (point b c d e j) zero6u
  simp only [diff6u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff6l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm2k)) (add 5 (mul 5 pr3l pm2u) (add 5 (mul 5 pr3u pm2l) (add 5 (mul 5 pc (mul 5 pr2k pm3k)) (add 5 (mul 5 pr2l pm3u) (add 5 (mul 5 pr2u pm3l) (add 5 (mul 5 pc (mul 5 pr1k (mul 5 pnine pm4k))) (add 5 (mul 5 pr1l pm4u) (add 5 (mul 5 pr1u pm4l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm5k))) (add 5 (mul 5 pr0l pm5u) (add 5 (mul 5 pr0u pm5l) (neg 5 pm6l)))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero6l : isZero 5 diff6l = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct6l (b c d e j : ℝ) : (m6 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j)).l := by
  have h := interp_of_isZero 5 diff6l (point b c d e j) zero6l
  simp only [diff6l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff6k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm2k))) (add 5 (mul 5 pr3l pm2l) (add 5 (mul 5 pr3k pm2u) (add 5 (mul 5 pr3u pm2k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k pm3k))) (add 5 (mul 5 pr2l pm3l) (add 5 (mul 5 pr2k pm3u) (add 5 (mul 5 pr2u pm3k) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr1l pm4l) (add 5 (mul 5 pr1k pm4u) (add 5 (mul 5 pr1u (mul 5 pnine pm4k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr0l pm5l) (add 5 (mul 5 pr0k pm5u) (add 5 (mul 5 pr0u (mul 5 pnine pm5k)) (neg 5 (mul 5 pnine pm6k))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero6k : isZero 5 diff6k = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct6k (b c d e j : ℝ) : (m6 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j)).k := by
  have h := interp_of_isZero 5 diff6k (point b c d e j) zero6k
  simp only [diff6k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step6 (b c d e j : ℝ) : m6 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) :=
  rep_ext (correct6u b c d e j) (correct6l b c d e j) (correct6k b c d e j)

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart.Chart1
open SparseCubes.Certificate Reflection


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff7u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm3l)) (add 5 (mul 5 pc (mul 5 pr3l pm3k)) (add 5 (mul 5 pb (mul 5 pr3l pm3l)) (add 5 (mul 5 pr3u pm3u) (add 5 (mul 5 pc (mul 5 pr2k pm4l)) (add 5 (mul 5 pc (mul 5 pr2l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr2l pm4l)) (add 5 (mul 5 pr2u pm4u) (add 5 (mul 5 pc (mul 5 pr1k pm5l)) (add 5 (mul 5 pc (mul 5 pr1l (mul 5 pnine pm5k))) (add 5 (mul 5 pb (mul 5 pr1l pm5l)) (add 5 (mul 5 pr1u pm5u) (add 5 (mul 5 pc (mul 5 pr0k pm6l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm6k))) (add 5 (mul 5 pb (mul 5 pr0l pm6l)) (add 5 (mul 5 pr0u pm6u) (neg 5 pm7u)))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero7u : isZero 5 diff7u = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct7u (b c d e j : ℝ) : (m7 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j)).u := by
  have h := interp_of_isZero 5 diff7u (point b c d e j) zero7u
  simp only [diff7u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff7l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm3k)) (add 5 (mul 5 pr3l pm3u) (add 5 (mul 5 pr3u pm3l) (add 5 (mul 5 pc (mul 5 pr2k (mul 5 pnine pm4k))) (add 5 (mul 5 pr2l pm4u) (add 5 (mul 5 pr2u pm4l) (add 5 (mul 5 pc (mul 5 pr1k (mul 5 pnine pm5k))) (add 5 (mul 5 pr1l pm5u) (add 5 (mul 5 pr1u pm5l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm6k))) (add 5 (mul 5 pr0l pm6u) (add 5 (mul 5 pr0u pm6l) (neg 5 pm7l)))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero7l : isZero 5 diff7l = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct7l (b c d e j : ℝ) : (m7 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j)).l := by
  have h := interp_of_isZero 5 diff7l (point b c d e j) zero7l
  simp only [diff7l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff7k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm3k))) (add 5 (mul 5 pr3l pm3l) (add 5 (mul 5 pr3k pm3u) (add 5 (mul 5 pr3u pm3k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr2l pm4l) (add 5 (mul 5 pr2k pm4u) (add 5 (mul 5 pr2u (mul 5 pnine pm4k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr1l pm5l) (add 5 (mul 5 pr1k pm5u) (add 5 (mul 5 pr1u (mul 5 pnine pm5k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm6k)))) (add 5 (mul 5 pr0l pm6l) (add 5 (mul 5 pr0k pm6u) (add 5 (mul 5 pr0u (mul 5 pnine pm6k)) (neg 5 (mul 5 pnine pm7k))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero7k : isZero 5 diff7k = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct7k (b c d e j : ℝ) : (m7 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j)).k := by
  have h := interp_of_isZero 5 diff7k (point b c d e j) zero7k
  simp only [diff7k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step7 (b c d e j : ℝ) : m7 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) :=
  rep_ext (correct7u b c d e j) (correct7l b c d e j) (correct7k b c d e j)

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart.Chart1
open SparseCubes.Certificate Reflection


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff8u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm4l)) (add 5 (mul 5 pc (mul 5 pr3l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr3l pm4l)) (add 5 (mul 5 pr3u pm4u) (add 5 (mul 5 pc (mul 5 pr2k pm5l)) (add 5 (mul 5 pc (mul 5 pr2l (mul 5 pnine pm5k))) (add 5 (mul 5 pb (mul 5 pr2l pm5l)) (add 5 (mul 5 pr2u pm5u) (add 5 (mul 5 pc (mul 5 pr1k pm6l)) (add 5 (mul 5 pc (mul 5 pr1l (mul 5 pnine pm6k))) (add 5 (mul 5 pb (mul 5 pr1l pm6l)) (add 5 (mul 5 pr1u pm6u) (add 5 (mul 5 pc (mul 5 pr0k pm7l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm7k))) (add 5 (mul 5 pb (mul 5 pr0l pm7l)) (add 5 (mul 5 pr0u pm7u) (neg 5 pm8u)))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero8u : isZero 5 diff8u = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct8u (b c d e j : ℝ) : (m8 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j)).u := by
  have h := interp_of_isZero 5 diff8u (point b c d e j) zero8u
  simp only [diff8u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff8l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k (mul 5 pnine pm4k))) (add 5 (mul 5 pr3l pm4u) (add 5 (mul 5 pr3u pm4l) (add 5 (mul 5 pc (mul 5 pr2k (mul 5 pnine pm5k))) (add 5 (mul 5 pr2l pm5u) (add 5 (mul 5 pr2u pm5l) (add 5 (mul 5 pc (mul 5 pr1k (mul 5 pnine pm6k))) (add 5 (mul 5 pr1l pm6u) (add 5 (mul 5 pr1u pm6l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm7k))) (add 5 (mul 5 pr0l pm7u) (add 5 (mul 5 pr0u pm7l) (neg 5 pm8l)))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero8l : isZero 5 diff8l = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct8l (b c d e j : ℝ) : (m8 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j)).l := by
  have h := interp_of_isZero 5 diff8l (point b c d e j) zero8l
  simp only [diff8l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff8k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr3l pm4l) (add 5 (mul 5 pr3k pm4u) (add 5 (mul 5 pr3u (mul 5 pnine pm4k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr2l pm5l) (add 5 (mul 5 pr2k pm5u) (add 5 (mul 5 pr2u (mul 5 pnine pm5k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm6k)))) (add 5 (mul 5 pr1l pm6l) (add 5 (mul 5 pr1k pm6u) (add 5 (mul 5 pr1u (mul 5 pnine pm6k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm7k)))) (add 5 (mul 5 pr0l pm7l) (add 5 (mul 5 pr0k pm7u) (add 5 (mul 5 pr0u (mul 5 pnine pm7k)) (neg 5 (mul 5 pnine pm8k))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero8k : isZero 5 diff8k = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct8k (b c d e j : ℝ) : (m8 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j)).k := by
  have h := interp_of_isZero 5 diff8k (point b c d e j) zero8k
  simp only [diff8k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  have scalem8k : (m8 b c d e j).k = 9*Certificate.w1G4 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k,scalem8k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step8 (b c d e j : ℝ) : m8 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) :=
  rep_ext (correct8u b c d e j) (correct8l b c d e j) (correct8k b c d e j)

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart.Chart1
open SparseCubes.Certificate Reflection




set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private def diff9k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr3l pm5l) (add 5 (mul 5 pr3k pm5u) (add 5 (mul 5 pr3u (mul 5 pnine pm5k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k (mul 5 pnine pm6k)))) (add 5 (mul 5 pr2l pm6l) (add 5 (mul 5 pr2k pm6u) (add 5 (mul 5 pr2u (mul 5 pnine pm6k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm7k)))) (add 5 (mul 5 pr1l pm7l) (add 5 (mul 5 pr1k pm7u) (add 5 (mul 5 pr1u (mul 5 pnine pm7k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm8k)))) (add 5 (mul 5 pr0l pm8l) (add 5 (mul 5 pr0k pm8u) (add 5 (mul 5 pr0u (mul 5 pnine pm8k)) (neg 5 (mul 5 pnine pm9k))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem zero9k : isZero 5 diff9k = true := by rfl
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem correct9k (b c d e j : ℝ) : (m9 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j)).k := by
  have h := interp_of_isZero 5 diff9k (point b c d e j) zero9k
  simp only [diff9k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8k_unscaled,eval_m8l,eval_m8u,eval_m9k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  have scalem8k : (m8 b c d e j).k = 9*Certificate.w1G4 b c d e j := rfl
  have scalem9k : (m9 b c d e j).k = 9*Certificate.w1G5 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem5k,scalem6k,scalem7k,scalem8k,scalem9k]
  linear_combination -h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step9 (b c d e j : ℝ) : m9 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) :=
  rep_ext rfl rfl (correct9k b c d e j)

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart.Chart1


variable (b c d e j : ℝ)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec0 : r0 b c d e j = recRep b c d e j 1 0 := by
  apply rep_ext <;> simp only [r0,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec1 : r1 b c d e j = recRep b c d e j 1 1 := by
  apply rep_ext <;> simp only [r1,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec2 : r2 b c d e j = recRep b c d e j 1 2 := by
  apply rep_ext <;> simp only [r2,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rec3 : r3 b c d e j = recRep b c d e j 1 3 := by
  apply rep_ext <;> simp only [r3,recRep,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base0 : m0 b c d e j = initialRep b c d e j 1 0 := by
  apply rep_ext <;> simp only [m0,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base1 : m1 b c d e j = initialRep b c d e j 1 1 := by
  apply rep_ext <;> simp only [m1,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base2 : m2 b c d e j = initialRep b c d e j 1 2 := by
  apply rep_ext <;> simp only [m2,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem base3 : m3 b c d e j = initialRep b c d e j 1 3 := by
  apply rep_ext <;> simp only [m3,initialRep,unit,X,V,S,Rep.add,Rep.scale,Rep.mul] <;> ring

end SparseCubes.Chart.Chart1

namespace SparseCubes.Certificate
private def tailNat (words : List Nat) : Nat :=
  words.foldl (fun value word => value * 2^80 + word) 0

private def suffixDen : Nat := (tailNat [0x3fc23c1960c7,0xd99ef27a637a224692b0,0x4ceedfe1720f292f899e,0x1038b6a67231f0f32214,0x25da938e5af1a027d79a,0xe14239f8137589df7cdd,0xcae7da1c6c264b0a57a9,0x5c3cada33049bcdc244e,0x9a639423f836951c4e09,0x6f2754543e2053a4a6cb,0xc809b54fbdb28381b7f3,0xcd2da22860a72f0ccdf,0x5448e8d94c9aae01a95d,0x43c79967fb208e7f65d3,0xfd54329525190c520000])

private def signed (n : Nat) : Int :=
  if n % 2 = 0 then ((n / 2 : Nat) : Int) else -((n / 2 : Nat) : Int)

private def unpack (n : Nat) : Nat × Nat × Nat × Nat × Nat × Int :=
  (n % 16, (n / 16) % 16, (n / 256) % 16, (n / 4096) % 16,
   (n / 65536) % 16, signed (n / 1048576))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def suffix7 : List Nat :=
  ([[0x20a,0xd04cdf254b634f285e2e,0xd3eb6bc84301bd5bd48a,0xbdc2977762390f44190a,0xf1682c53cf2c8061eec0,0xa3119664af1e152ef4d5,0x9e18c0074c717615476e,0x4773890ca877c21683b4,0x1ed569ed6fb646a43b70,0x639b860d1c1f40d21fe6,0x77f209257d1a7992ba58,0xe97116e7420ac2930c6b,0xf24c8988d6ba886a14b6,0xe79d0c7dc411cd497973,0xebfb0c9fc69387eb3f94,0x3bb200121ca560102000],[0xba,0xf2eded7c802b9de67a81,0x405dc53462927320317e,0xe3984db4ddf8dfdf678c,0x23c0e796024b869a57d8,0xb0215a5e958aec7e8701,0xb3cb1cb033f558fcce58,0xb07f881f790490698ca3,0x3e1485976aae30259832,0x31c4d025337ab0c476,0x5fd8049837758d36cbc1,0xa6c8557c7e5368c0f478,0x257cf8b0c7b3c26c3043,0x54da4a32ef58de4fad0d,0x5cd1454f9adbbb82e1d5,0xcfc97639d01ff0112000],[0x22f,0xf6f6a1d5be0479bb23a7,0xb3601e77c00740fb7efc,0x970bb4c3e8b925dd4852,0xed95b6bb6d5de5c7b3db,0x3ed15e0ef1a1d820298f,0x933258594c0ae36b7778,0x7dcf3d2ca5a65591691a,0x9bd6955b00f5502e572f,0x2d9ffe0f8d24519f17a5,0x406a2b3cc86f8818b462,0xd0d2599f8b735881ce4b,0x5d12f132e9fa40fded70,0xd7bae3c88d2099720b24,0x11072b147723473405b2,0xf909c70a96586a022000],[0x1d1,0x8f674b839739608f6e36,0x2a2fe8317b3f56a1f05,0xfffb82500b1ea664c220,0x97c6717b4c547d77ba3e,0x99710674c2fe723214aa,0xbd187c2507606c08d6bb,0x5bb5de79e8a29751f6ec,0x4d0f72f724a1d1d67b80,0xbd2ef7607d5854f6b788,0x5836d6153d17c694a1ab,0xa8dbe3341547797f0ba9,0x3dae82902289270dc98f,0x5a188c0c2d7d76d3e716,0x24290a54cd6a0d887ee0,0xf22385666f3293832000],[0x98,0x5aac9a46e4a6cfc93e3d,0x80dc96878762c0055b92,0x7c48151dfa92b44ab3cf,0xbc5932049e4165b84b60,0xf726637a72d72f639bf3,0xff04e713b5c0c48477e0,0xe9a2b9afa6073ba10976,0x60518e987392a2d5f045,0xf839df2075a6cbddfd40,0x6ceb93aa609e65688649,0x9d4f1c35c93adc5c9356,0xa3f27f27cd9985cfc9ff,0xb908d6c9132c7000f4df,0x43826bf62ad6f11836f4,0x7317056191ac2a042000],[0x19,0x7408af2edddef8c3a279,0xb8dc62542745ed8200cf,0x1dc6067e819f937495ab,0x24c102f39e27127d3528,0xf0bad3140ceaf461a180,0x6740deb6bea63378049e,0x486bdd560dd36634f0f5,0xa45bc0c86e1304b9fc79,0xac61699b37f1ad62d26,0x3e81b861c50a2a6cac0,0x8678f1905b75b2b98824,0x7a76c48d2c6ca8852b01,0xfad9c4ca35a867af0b7b,0xef6521e47aaf122e435e,0x3545222cb693e7252000],[0x2,0x373479a77a25c2b0eeb4,0x91ff1ee6b2732881d294,0x533099288f6107356577,0xc9700e971cb05118397f,0x1bb81e82808e70f16e9,0x321398031cb11bf5c5fe,0xc1d12fcadcd083528d3e,0x6c507716ea5f3fedc92f,0x42b3a6924dac74c61f34,0x9a062b723b7439029a3,0xe9ba85bbac7fc32c5c52,0x71144fe08652268fd8ea,0xb7a70d071b3bd2580765,0x19a1aaceaf3ad7347f3c,0xd8b1d0b9f8b53e862000],[0x15aec1b68e14715cfaef,0x5b88e452f3e7bb363aeb,0x606d507934aeb0f64204,0x87423f8c6dfb413d7008,0x6adf5879cb44d7cca705,0xfc2383edb23b986319e0,0x2f6c5dc436c0264bace0,0x3c0340bf8ea7e73185ca,0x897a8d26b6ab5a09d96e,0xbfdf1be32a9d28b394f0,0x82781845e72b03f02729,0xfa717c5f9c70a7fe9fb9,0x1b4de103feac00fdb07e,0x22584f284bdafee09002,0x368ef1c2638545672000],[0x1d046abfd8c2ac56c4,0xe47830179610c05a7613,0xcfaf36a66f160482ca5b,0x74b6eb98aa4c53c6d840,0x9554397ad12808908831,0x8ed97e8ce603a71f4e2,0x24eee8da1a04c19d0fea,0xaba87eb16f66acf5ab71,0x76b39f372333816c3420,0xd86d93b903449d521d3c,0x5203aa33ec13ea41cd0b,0x5042d2d7ae91ba7404c7,0xd87419309c998e30f94f,0x1087fecc8cf7ca90e027,0xf04eccfb5b1571882000],[0x939d5535208dc17,0xf53ae146e507c8118be6,0xf946183e700963aa2d6f,0xd87d3fe3f6eb6e85cca6,0x6514f47f871ce98a817c,0x98f1c10c982206ed1928,0x84b2db17860dd3362840,0x460d477fcc67672e8e23,0x43b7e3a58b845fea60c4,0x3d066edb9d865ed0e838,0x98dcab95de307f24d381,0x93c2de34a2ca5020012c,0x2edf14455cc381bfe53b,0xfe258842a8ae34644fd0,0x9c130730642c0092000],[0xb34,0x5532f36432855125862,0x55658f808c1c908951e3,0x3cc7b2aa05cc04ae2722,0x326893282e4492029ea,0x1e6633abe28d778e1b0e,0xce8bdceedc1852afde53,0x4a09f5ad06c7cca50aab,0x53d129f56bef395bcd61,0xa17d5d5914f87e451f21,0x9a92b9bd1cf33ca64675,0x98b8e4f76551955aafb7,0x428f65fdff6834db31ec,0x97b5498b872073cb3903,0xe8260b3486ae784fc302,0x8924df0ecbcb9c103000],[0xa45,0x52e0ed886e3a5e0f3eab,0x11360e1f178b54979a1e,0x56e40245d0c3f6a80192,0x9ff40eb99c2e52fc579b,0xe75f6753c07577b284d3,0x987e1f3561da28521052,0x961da796f2398c059bb,0x8c15c0f48b3837a39475,0x5b08aaa29c7abcfd0920,0xec9954c604ad7886d796,0x49ae2158b874af383002,0xc5dad422f175ea242d6,0x611ac3b5939b32e1a17a,0x555ff6c7276523876968,0xec9b3eef2a4850113000],[0x437,0xa2d3e504d2295a4ac163,0x44a6cf7448b383388770,0xed2235bf8d6d1eb7e2cf,0x286d30eb4ed47005707b,0x6c885ddbaecb07ff6201,0xbb99f1a7fc41394a0dfc,0x1d1410f3c2b3246b72e6,0xbb054820060f5972e48b,0x60397e4358aa8d558801,0xf523f96ae22846fa731b,0x3e630636e7dd3046ba6a,0x7263c131cd8e34b3ed4f,0xffde1a5ef3a8481e45df,0xbf43a5a270f49030b3ff,0xa9b51359808cf0123000],[0xe2,0xd19f52649cc81e79cea6,0x9af262561c0c472d3c8b,0x7fd3352f4ed4b1a6ec06,0x6fd7d23f5793115fd21e,0x4803e5b918d5d681cefe,0x73b910615f3fe48c1167,0xc7c330e504ad2661f1a0,0x94c44938b0ab5d4af3be,0x89559393fa4ba2b84d2e,0xdce235824ec45a149965,0xa421ee04e64f1c304103,0x5949d9d100049dc27942,0x17e0796f0be0b6455437,0xd312fb24e5dc90266339,0xa5e5770e4a3909133000],[0x1a,0x13010a6c856050625fac,0x87f660e7b311da52a9f,0xd9131e6308b9700dc242,0x68b541ac5d560caadd52,0xe1e25d26aa2ba6a77eed,0x6271045fea473834a7a7,0x6adcc2616b134eb133b3,0x3fae372668cb92f1019d,0x6c91aa356cf91d8a897c,0x50603b952254c1829d66,0x44263993327701e21899,0x3d43f1a97b77b97b3d2b,0xad45ceb8ec6d07008019,0x4ba4d74941eff2111e83,0xf7899d54588c36143000],[0x1,0x99ae365177632ab7eb46,0x9378637d06508112b66a,0x8e2157a932e665eeea73,0x4e20b4ffdbc525229db6,0xc3409dd5cc7dcc152135,0x74c2c4a568aa09e8a6c7,0x95016c65962e908ddc13,0xb56f65e733c3f77fcaec,0xfb9dadfcc599852e28a3,0x2ac563156c507622486e,0xf1e34c819601c3cd2d51,0x783ceec1eaea6fa7ce37,0x530585abd1aaad6e5fad,0x530abe8679c873f9a883,0xcc89b2a31c161cf53000],[0xb14d0aea70109489409,0x8c4077f8a3392d2613f7,0xc3b7672167f17d25cc14,0xcce195fee9ba48d00bae,0x75e91b49bbb8d275491f,0x975523038f13fc2c1c05,0x3f9805a5304ab63a1a5a,0xcc0da5dcf11462dd41b5,0x62f9d50078c6637bf2ba,0xb56005e6cf802a4d2900,0xde2d53484f010e936cc9,0xfba736cd1509c4c88411,0x67e40b808f91c82246e9,0x5916c44fcb7ea0c5941f,0xf493eccf38d21fb63000],[0x19f47d1d781209da08,0x99e8861518e14f14ee08,0x8d2ba7cc65b863efd2db,0xd52e7650ddf68891dfe0,0x7b4c96328b4f9b9bea9c,0x883c703c528a743c8a6d,0xd8a9d7c109afb0be7f64,0xc7d81a549720fcb2fd42,0xfe3edc55c4918ad11ebc,0x9d002ba4b86fd735888f,0x37c84dbe61122dadd588,0xfcc301e64a498a6d0b7,0xb9238621be0874c7125a,0x5df1af3b052a6674475e,0xfbd098db3bf890873000],[0x76bfc3a35ff5bb4,0x4ca7448f54caf111c2f4,0xd2518e85f486817a737d,0x48fd14b5170cb1df1ed5,0xda346688b982d15a5280,0x47a83c88a40d5ececa5d,0x83f153bb2ab40b12bf42,0xe0bf2a9d75949197eb08,0x54c91c9e1588d71e5f37,0x8d80b2e876e010a51d81,0x3de53f39eb648b6c4aab,0x7177f9182b7f321b9bf,0xa28768db5db25fd2ee87,0xa26482f78d9b4cf70ffe,0xdb9bbe9833b740083000],[0x126,0x2b0d94a52f6fe562783,0xe704d798fdd21fe38c5f,0x5de76737936cca7a561,0x68627a2b08f34e2ba624,0xc3a26903ba0dc2b684ba,0x8b4cdba4ca3ac5674243,0xd32ee3ec623a09ab6c66,0xd6972de6053195604b12,0x565cce0ed284ed55fd9d,0xd5c47731f8b32bec8c63,0xe718c213a025c6e5674f,0x5976a1a98c6dae533328,0x39c38ad03d9e3bb7cb84,0x63a1bd7e0e8e79af30f,0x991c3d80203177104000],[0x220,0x76f51337140c004ea2fa,0xf5e9252922e352cc0dbf,0x9f3e14df42974d1e9c19,0xfb7e0c9d245e30620aa4,0x504c28c2e6babb63e73f,0xf28f3a44ebd3871cdf5e,0xeee42d771f6b9a69a3d4,0x33a324ab87b076012a,0xc11b70058cb0d64f2800,0x2cf3417e09f9841b4448,0x60922238d8b3075e2b14,0x5602d7583e4f64cb59a9,0x537bdb0e5ff2cbe85107,0x2929959ef417649b39b1,0x69588e19120a25114000],[0xe4,0x2c34cf92b3fc6ed5802f,0xf8fd2b54e8cc81c59a98,0x5e628dda3758f4f0fb92,0xedf50e6313ad1afe27d0,0x4b484dca8af3d772fd16,0x5005b5ba7f17f37be393,0xac8c3715f30c63d29f3b,0xa98356c9acdae00cb0a2,0x4b7abc9d710759cbfef3,0xba1847d75f6b2f57ea1c,0xb60a258ce952292f7fc4,0x7289bb315259f9eeefcb,0x24ce31f2f6b2ad51e7e3,0xd8f26a0ed3439aaf466d,0xb585cd26d3ef9d524000],[0x31,0xf9a5ef272f4f485300ff,0x4f2dc059d2fa7783e4bd,0x434e12377bdbe2e8cc3a,0x1994967545d1b4798789,0x8a42d7cc44137c2d9ac0,0xfa71f438545ff19ff8a4,0xe76d727f01de5df44ee6,0x284963ef7922b383236d,0xf620b367d4e80f19384c,0x30cf1dace4a5fd94415c,0xb3599cc8b20869e86902,0x365b8e2ca4ae1234f382,0x47537b5970f0780750e8,0xbb827fbf462b30456f04,0xdb9b10805fd0a8d34000],[0x5,0xda3b85ebf572d04f66ba,0xbbb170bcfc5999e9d681,0x439b1261943bb49ae692,0xdc428cd41434cfc76c43,0x47cafb578488bf30389,0xfe61bd5388bbc692642c,0xd5b86aaebac34516d5e,0xeb2be985b046fe97090a,0xa4641f6590a6cf420c1e,0xb99b108903d88692eb0d,0x9e84b7021dc8662bd345,0x899d264d1f59bf737002,0x899273fd7faf25ddd7f8,0x9856055469d2d7e7333b,0x2d43c6ae47d86e544000],[0x5801b8e3cfaf3c5c24c0,0x1bd48aec7eb88a69f84b,0xfd0ae538651e31650eec,0x7cc5e81c93b3ccd1eb6f,0xddf4ecb9c5cde4e75c25,0x60dee93b7bb14b326118,0xd5200893a151cf5cc57b,0x8a45e41f7c0a58916614,0x595b76c3f295aebd5236,0x8062615d9dd9a6fd7d5c,0x55354fb1eac672e2dfa9,0x4f1a1cdfe1ce80bf7261,0xc535a929e75e4125208e,0x152201942a568354bf06,0xda18276808699b54000],[0x18fbfaafd00e3f06f03,0x56863536a9efede0f669,0xa355cd42c7f4f99019ca,0x12b73e9c66e0e6dc2b23,0x76d2a1b4c61ae8363075,0xf65e0e62b477e13b93b0,0x2dbcbe3ff556f003e8d0,0x91505017232d8869a00c,0xdee87217db230fdfd735,0x28665b72ee061b217629,0xaeb3d2c1f104c567a7c4,0x11a12e0d1b84d64076e6,0x1f8bf1840ef0fcbea76e,0x5a4c9937228c8ec0f0a5,0x1862b8753b7f47164000],[0x44647572fde806,0xb567f65e1cb4965e6554,0x31bbddb7422a1182a573,0xe48e2083272bacf52cc6,0x1b9455c73066de5156e7,0x6b6fa0066122c78832a9,0x12d6eda5ba6bcb1be38e,0x26161258fdcc77ef59e,0xd5d73d4992b9a0abdbdd,0x8aac653e40dc094aca4d,0x121847486a73930c09de,0xb65e8687ad8cdb43a970,0x2a4a79147bb5bdbbe0b6,0xe4e8f93817532956ed90,0x6a25c673ff6400074000],[0x37,0xbc3edc5abfe37be73931,0xd053146e8e5bf427cadc,0xe2f2f2b910b9db2d534b,0xdd4e388bccf8683dc1cd,0x794fab66f9e1285cb9cf,0x2f90da9b1b153d996584,0x4a454d2a73bbd4611674,0x8b3b799cf11c81f63159,0xb9866032ea235883c6fe,0x4de310bdc5d6240ceb30,0x31a5af8f3dd1bb52a9c0,0x19202652ff2478bbf7be,0xf3940d0529ae06f982f1,0x7a41138bfe17a91719c4,0xc14dab8944aa9905000],[0x36,0xd99fe767ca4ce510a5ba,0x44fd0510880e9dd47565,0x8de17e31b6f95d46198b,0xb47155f60cd93bee8760,0x889ec00181fe1534cdfe,0x621370602ff14de9c563,0xfc639e5bf0e4243a54da,0x62b78d6859f539498d9c,0x415acb66ac14ef227997,0xebdadc28bb9a030c3c02,0x37bb3fa58667a85ef4b5,0xfc5f1aa18338bab838ac,0x10c31a62aeae4f1946df,0xfa2ad50c55af8a44cd,0x4aa288ed310d05915000],[0x16,0xabf69370d94139738b5f,0x9d6034a38e72d7b6a277,0xdbf54a1e1a53b9c34f61,0x7067cc1b76f83467cf30,0x8bb21ca2e1759a4dfe1,0x7af275b0efcf88402345,0x3e450c26d7c5fc8a6395,0xf6ff01a3ad0ee737244d,0x84ff7e390aba34da16ad,0xd30adde331a232c5ef9a,0xf2d5cd3c083ccf8317a6,0x5df3a607ff3f55bab59a,0xc1d814064b8eca5b44c9,0x316dd95af965103bca2b,0xf83076413412ea125000],[0x3,0xefe5159fcd67e6a8c7f7,0xfbeab2b4866e408c59d5,0x5286bfee6eeeabaf87aa,0xaf305e18615ceffa76f4,0x764dec4ea45cf290b81f,0x866002e71ea87e7314b0,0xb31e019159ff0d911488,0xe5768e55122d9c04525f,0xcda4dd845819fd9425f7,0xb9d59d0f8e01c0bad1d1,0x591400b01843436101b,0x7e43425fb5885330a4b6,0x6cd6154b6403d5a3e0a7,0x94eaea102fe22035c982,0xcd43d1890bbacb935000],[0x4efb020af1abe8b72bf9,0x392d8a658351b0635bef,0x17ae6dd8746122827e0e,0x40cf352319e931c1478d,0x306e3a40f517f37ea8ce,0xaa3523664a37e325126,0x4571dbecb9492f4d61f6,0x813ae101a1f805baaeac,0x8207c98af20b6e500cf5,0x2002d76ccdda24c813af,0xb4b6ac360697c56455b4,0xbf6af4c192e943e799aa,0x5e0bde3bdc8ea650e4fe,0xa1e27ceedc2f90f291ae,0x77644fc6b8c0a7345000]] ++
  [[0x2033f3c86b198a8a494,0xf7f2568c7da80de9da4a,0x9367400323a5d1bacbdd,0x2deaeff0c31011ec7615,0xe697f6a445c1e6d521a,0x383f7c6f2837dad8a187,0x48a6f19f5f3ddcc125c3,0x28c2bda0775f46a68bf1,0xe5654e2bc7ecdfff19e5,0x6d980e8683014ef799ec,0x1d9461bea68ce0916ecc,0xa9bf6cba3ebe6b2eae2b,0x15a51ed1085bba052b50,0xd827417b51b0b1d7c206,0x788c51efaf8b30155000],[0x18952f73741957,0x2d5bf9ab5a4351c49bae,0x762d2af21e7bb12c1844,0x27e112c6288dc62c8060,0xcac5ea3d17c5b49c2d60,0xabe41aca5df56908b2d6,0xfec2d922596df98da760,0x26c6be8b56d6f239a94a,0xf3db339af59bbe01122f,0xae6d694a1c8fbf636de5,0xfe7f58cfeb8fdc542ca8,0x91064a60ac1b3a5dbe0b,0x8517b590a171d675971b,0x6b08505414fea02c0e2f,0xa6652588ad2de0065000],[0x4,0x3d372adc027251dda25e,0x88fc4f5d4ee7e4bd926c,0xe6c9a2e8505cdeae6f39,0xd82e3d80e7bb66536390,0xa229be5c20b501a47db1,0xf2322375786d1e2e8dde,0x26b2880e0a7b0b6a7b1a,0x6e75846ca9850b7e2c5c,0x395e4f4890574f8469d4,0x87bf224f156b1f747253,0xbb60943757c8fc824bf7,0xad57c8f4cac795da1b7f,0x5418b0d104bdd005dfa8,0x6c00551076231c641e03,0xf470158b7080ac506000],[0x5,0x4fd946711de242370ac8,0xe6a31f749a6e68434147,0x6d9db4b2f7c43d95279e,0x9f399b4a4f0409d2e320,0x71b2055837da2f90eb,0xbbbdb8bc8eca2e1855e6,0x2806b7a80d74e22668dc,0xfba5cfe60c031bcb5bc0,0xe86e6e4ffe161ab498a0,0xc32fbbcf6d19f1116f3c,0xe6ced7853e69cd591e0b,0x2a504867c8eacad1c585,0x8cd4882b51fb89ebc086,0xe5cc55363c7e5e5b502,0x38ee70edefe875516000],[0x1,0x78e40f695a86d0404105,0x3962608ae6a851fd61c2,0x7a5a1037bc282ade657e,0xaf195908b135565556ab,0x29ab69dc671d32f47bbe,0xad7c3e8a9657da91dc1,0xed4d73e662d300b1577,0xd9880ce3f5319b08c1c6,0x5298f4e9a3ffaa7313a6,0xe28e521c95da0bde92d1,0xe0f429f45fa4e5f1cfbe,0xd72c43e16079d458816e,0x359f997ca980c82ed1cc,0x7935542f9dd0f39e4c54,0x31dc45bcf8506e526000],[0x298686827674f322446d,0x8c76b5a262bc6c4acdb4,0x414e1efc1bcf39f4a6ac,0xd7d31a9e60173d55c38a,0x368ec3345e319c493703,0x37919ac54fdc5fa7cea1,0x1bc5b84fa766532ed3ce,0xaf8c7e453fc2801936b9,0x7bbaf5794a5662602378,0xfcafbfa9327dd5d74c32,0xe2ae4a62ff81334f04e1,0x625d4c5b79c11548f419,0x3ac50da88c75c89a921c,0xb91357c38c322ef75a84,0x480c7de0091124d36000],[0x192163c6aff63dff48f,0x1a627b5c071f46fa8269,0x50c06589aaa2592e6960,0x9b3afe329c9f163e72e4,0x2f10c6b92ebd7bfad5e5,0x18eecd3c09cb0a63de7f,0x73bbd289376bf86b2a92,0xa643df8ca24833c65d5,0x7e7b71d874eb442492db,0xfc5fe3baf79f8cb83c36,0x70d76895fba94f64e2e2,0x28a20eecc20f9be5034d,0x4fa8024cb2f16175aa5d,0x1c0d3df534cf77c3f1f3,0x1c76c618d7f6e9146000],[0x3da03ebb710192fd0289,0xc63d6607be6f50034791,0x6dc41fdf15f7a1dcc2f0,0xea3de572d791d5bce911,0x58ae5af1fa2d1014cab3,0x78663faae8788bfe0361,0xefa657bbe49f65ace78,0x83aca3e738c6f38df9be,0xc234063c1cce25a64dbe,0x48406f4fa5376279cc8a,0x6a8f88f9bc51badc305,0x19a98bccdc0e8d9f5532,0xdf7fbd81254a9054d1f8,0xaed1385559b86293162b,0xd48f434f0a7a54107000],[0x30e4e7c8d26ec7537e4c,0x82de765bdcf5b08e421f,0x41711b1dcaa6f06b6d43,0xad65c4843b6b911f8916,0x6f383a1e3d6bd2d5ec8b,0xff1dbc7379ba5dae9d25,0x805942d3a7796f79c8b0,0x81efce1a4b207990d3f4,0xc8a97a254861f3724615,0xa21008b00ef62ec17625,0xeeec76c26947a75eac77,0xd5b2b876f2254bde4fe7,0x7067bff8c03bd40aab5d,0xceb817a81830d39fb7c2,0x9ccdee9d7f817a117000],[0x966f7afc9d927fa88ca,0xf89c8a763e6e8927fb95,0x65446deed96ecf6cc49b,0x9bf8765f698c7e5f075e,0x3589d1616ba1444673e8,0x729e0be6ab1b1a6f5ab9,0x63e734c95e98cb55a3b1,0x7e39b0357be5303ac955,0x1e183a65663f6bc2aca,0x57e0f5982cac32329eeb,0x7db1d0255b7500bee938,0x237691b819247a9cb498,0x6847b66fec146e93e3c3,0x573fb6011d6e05e9401c,0x7343bea68caeaa127000],[0x94986abacbc1d48cdd,0x363359b27c1d6b18b4f2,0x6bc97194a39f725bffd6,0xb8b312afacdb421f62b2,0x5adbca71a7c048d5c908,0x875bac72f8f05edafa7c,0x7147ec2945849c2d47db,0xb08ef5aeed60e8116ebd,0x83943571402916b364ac,0x925839ecf536839c22d5,0x91f8c5b1e404241907ce,0x5bd2f86e5d70a0f7ee6,0x4080a05e553ca7f47a4c,0x79c96b3b588c73d09a99,0x2133a4006dd6b0137000],[0x1c09bf3e3368d3c6e42,0x881c78e076f2bdd0c156,0x5e750c10b431bb4dbb2e,0x19f4430cfc02a0c26e6b,0x51d79fc251aca6252065,0x5dd302955ae91d5fa0bf,0xd641e543809a07fe7851,0x6a42ace37c21d18b6cab,0x771ffcffb9e03b9d3aca,0xb8a65e90005012fd024a,0x90c0edfa48a8c92fc353,0x79c77535006ff7f7a402,0x2582acf380f19eedbb63,0xf4f498d9450d96ead664,0x807cf77f347a0108000],[0x802c8ed334285a68a5,0x4b75d964b4455acdee18,0xad4603727ca07ea87e9f,0x752137ba91255280b1d5,0x85190912f2c39d2f2dd3,0xd1aa00bcf5672cf6c036,0xcf808aa5927526dafdce,0x1e5c3165912e3bdeb155,0x8fbfff247e40110859f0,0xc70af672493b7323b783,0x4c96890a70ba73237ce,0xb5146aa16dd6d9222edc,0xab79f21004508d6358a,0x45fcbdf4ef28744318ae,0xddb916b48ea6c0118000],[0xe3dd6fb05cb984484,0x24d43499695d0a16e190,0xf6cee3f046bc7fd9d52e,0x297577f84904259c8589,0x809101021af94a5a9350,0x6ca11c86c5ef04fef8e9,0xa5472bd9820d045138a5,0x1fd15ad26576ea353025,0xf3871c59635c73ab9837,0x328f70b75d78622069b9,0x396bb648f61dbd3e77fa,0x85e5d2f57dfb6d75936d,0xc84d4a91e395e489942b,0xcee3318cfe20f0793ba1,0xa6dbad3081a0c0128000],[0x70,0x5d75efe0af9d7a59a4c7,0xe63ad77256c6b4f12cae,0x58a8232983f76d9b462f,0x6261bd8125476007d829,0x4f57b6d8ded674c0afab,0x75cea742560407205497,0xdbd8bb42028777e1753a,0x36f3bbd7957d3f79c79c,0xb83f62454aced9ecc17a,0x7459bec1853de3a14a71,0x33b6cfe034f737f8d287,0xf29138a5d9bab62d2020,0xafc6bc06ea6fd94f2ff4,0xc2580a235360123f2e5d,0xd688d69040f470100100],[0x76,0x5e2f7fbc5417f1a0ac15,0x54f256ca7ca4d670cdf5,0xa072faca514c572f4a83,0x5119bdf3e30f4d974d35,0x994a353930a545cae6bf,0x344cee3d7cca46cc7f80,0x9eb632413ff269b0eb1e,0x9ad1829ab600cfc494d,0x4223baeb7b64d35574b9,0x43e5f7d940a57ca64288,0xbbdee1443a323acb80d2,0xa3030029c996ed86097b,0x227d53d5e94e508a1a77,0x4630a31278195473d578,0xa766e1334f5340110100],[0x86,0x79ab1d5e3c4714fb8804,0x38f94ed32797b28970ca,0xa870b2e4dbccb0c54bd4,0x52749b0e7f49dfec900,0xc2adaf3a74ad3a26bb93,0x9f7748957ceefedf617e,0xbfd4c45a07654f74d39a,0x6223788f16f1c1c20925,0x5af9f830d2a4a9cdf31a,0xaca82a0321a928d19a34,0x32dddf0baf68a8cc02f4,0x5d8d2e0ac4ba06b0ddb,0x582b338bb10be170ad50,0xc3a2751ea73f2150cb7a,0x533df202cdb380020100],[0xdc,0x48db5c9c978c4b7af57d,0xad72d390c800af083b83,0xbb5f3458003a091c1ad0,0xacbc6ff94494d5e78996,0xc0c7e2a380d1b4cfe956,0x66c412d0579ad52c021a,0x9489af74224fd420126c,0x2d79882569d6d2c52571,0x8df9c7cfd4e33f42f1eb,0xd7a32522177a4d946446,0x29668f72ce25530db313,0xa83b4ec5354823fd66bb,0xdf27127a303ebd0f6964,0x9ad6e407bbba70acc201,0xbe848f74f118e9030100],[0x66,0xe58c15f4fd87b08e7ff1,0xf4350bb2d824a221a09c,0x4a57de86cb7c4d2bafe0,0xd7eb3ecf54434b89b4ce,0x71a7a3530eafbc60ed9d,0xa827b0d340b05dcdfa62,0x7826a34cc0af6c91901f,0x15ba37aabf34b7453134,0xfd24ca41c77d4fd58f08,0xfed6f8ac36d101d6c72,0xb5913f51febe723b328c,0x1a0b42419a74389748bf,0xd1c116ca9e795aa413b8,0x6dae08dba86db9e03775,0x806eb68cbf1015840100],[0x15,0x964bbb634467d1577bd9,0x719310214d1be69baa1b,0xaeb4418ab611a7657466,0x3d7a5d59237891cfb93,0x3804f54b2143160d8234,0xe38812760f5ea6444db6,0x2ac4b4d013b9eb9e4a34,0x4bb2417b777d2ea23522,0xc202f2975cfa9d85b6f3,0xffde853ea15d66effbab,0xc3995e9e3c4d1c5cda5,0x48a418b5fa5ea5e8094a,0xb50daab0ddcb0cc0e398,0xe7c5d2f4f8d85cdca69d,0x55c74c0203a8c5450100],[0x2,0x184813b146ea71d61191,0xebaa34aa637310328fd0,0xa4383cbd0a2b57c722fd,0xeae06a4f4b612ff92927,0xa31247281d0cc8ab42e8,0x20f08594622e0830052c,0x34a3e444b8b858517e3e,0x51945b106aee57dcc200,0xa7c35fede2c38e39b804,0xcf5b6dc9c542171846b7,0xde74cfeaca511e6259bd,0xc0e9fe1c429e4793b08c,0x6701989230d4e503c7bf,0xf14cc9ecef2ebbe29cf5,0x4ffd49160927aa060100],[0x1448717c8480c05ff5ea,0xa6642cf694f0d76b78e8,0xaa284e1ac943cb1996cb,0x8ee42654322d9edb4efa,0x5ffbf94d0f5d91ba00e3,0x61f2feae57af92e469cd,0xf95891b142776ab4595b,0x143e4bb19ef83bc6efc3,0x93322c083e67dfa54331,0x7ad11191e9f7b8062351,0xa4cc091ba6a58cf77fda,0xba297fd6d01f1fa1e8a1,0xab0506b99be57c196b6b,0x12391fac18a72da3a0c2,0xdca918abd325c7c70100],[0x17c73e0bdef7380e25,0x94315dcfa52a5138b03d,0xcc893ff469c02b406d1b,0x5f0115e9fecb399c9d68,0x81908181fcef133f09b,0xb2f93b7d9f05c08cd8b7,0xba6b8213b9f61f9ea0af,0x74a01fb5a9bf544324f0,0x372c7081590fdeecb66,0x1ebbdcb54ff7c0db37da,0x6d9cebef101d53cd31d1,0xc2871683cba436db5c91,0x94c528279f4d60f1a993,0x66e3b1d6b74b86a7a697,0x7a44ba97974ce9080100],[0x89126ce3fcd6377,0x725c49396c23f1029f74,0x5520646d68e3abb0e6ab,0x600dcec7854290db1099,0x48eb3d02378dd49cb2bd,0x56b2b2244cacc116f4b1,0x2e527ceb2b11ae9c2a04,0x3d2a721344f4a5599f6f,0x426e041b7ec1d51eefe6,0x47ddbd3759afe26f3ba9,0xf12f179e5b4d5644f5af,0x3f185731d56405792eec,0xb4effbce4cd6b19b5f87,0xead6d3948ac4fbd697c0,0xe7e09e3ca62a00090100],[0x35d,0x1c54a562a6a5ce9edc62,0xf113d2e55b2a1d99fb26,0xa9c4d3867210f19b1ee8,0xdb73aaf4356598b57622,0xbc5fbab9c54bb01b1e0b,0xa4002762b4836f84654c,0x2bdf315a06b36592bc5b,0xd8f7ad31af99c446bc1e,0x37b314b84a93fea04bbb,0xf62404a87bab4c7952b,0x9522a645ced597b85055,0x1f41b7a679541860a5f7,0x9bd7d05d1fd4cd497301,0x70ab3f4022829e664270,0x5c68a4e83ae924101100],[0x4b0,0xd5719540c59a336df2dd,0xf79aed84c50e6867e7b5,0xb26c93894cec02507df7,0x37ce79c23c087b0f6987,0x493730a33aa4854703b0,0xf97195ac08a5826aac0b,0x5127cec7f5adf0cb014b,0x2965b76b100916d4cd9b,0x5563677ebd5ba39c1aad,0xfdea7ed98691f09b78aa,0x7ae5b18dc02391182284,0xac37d2315809db8889b2,0x2178ad23af37ea5e8f75,0xebb1ff3817e029e7118a,0x8cdbef6951e0f8111100],[0x208,0xf24ed755ae6ca8adeb19,0x222fa3b3abff2549f693,0xbd1d00428c5154f80152,0xdea19db1be64e292988a,0xeab6ed6ba64f27a79be9,0xe074dad79f093c2463af,0x1ae3179afdde94abd93f,0x69bd52757ac64677b08a,0xf024b7bce84623b86667,0x51d8b0e75f31b25b9e1b,0xba4db474f2a2f53bc4f2,0xf09802d4edcd0f3da18b,0xfec92d26cd8aff66d7ff,0x5aed73c477c8949e55eb,0xc8017f9796475a121100],[0x63,0x3fedc35620438583d314,0x4864715417f45e753c9a,0x18cd5a2d630acf6db76e,0xf005d09ba5008a1e3355,0x42ebeb900f1858cf0561,0x4f2e43688dc669422bb8,0x20154169536e07cab143,0x511562e8d799d56c74,0x6d5518224847caba8ce7,0xa1e1761bdc802a9cbc68,0x247148063cb1a8869e94,0x83a271d0f03ed02f125a,0x67a53d2bd6749cd90b54,0x81d432276bcfc30896f7,0xb5132f56964e4b131100],[0x2,0xac69fbaf411c63f3edd9,0x636a7e532102872bd1c3,0xff54290d8450c5e33984,0x17360c1303de2d277b40,0x5bc9f0387ea498a4c066,0xc96c5ff9b95154a3b117,0x458fc3d301342fdf9aa2,0x6e9a53807ea095fc1073,0xb88789aa98e5e3194e9e,0x8a747d7cdce6a8192e31,0xaed942a3f9537520e586,0x25c2d5e2c1d39c219b22,0x722e73428977d8aa5dd7,0x40b1a35aec27446f53f0,0x77d6f84a83b316541100],[0x1,0x120e2396f4db460b89ac,0xcf58261e30b62dfe6952,0xc30ca715e501bdcc2378,0x3b5fce676ca7036592ce,0xcd78af2ee578fa56b95e,0xb81d38070748c0a463da,0x62d4c823466b465848f9,0xa4ddb5993b452092e35e,0xd73af972b42af52ab382,0x6e27fb35f37bcb93a98b,0x5ee477a91f47e18a2f73,0x17095e6d2353080b80bf,0xa22b0eb65acb4f0bdc88,0x755c84a637d29fdcaefb,0x1422c31ed8009c451100],[0x156812e7089273e68374,0x2e3a1644483edd50c0d2,0x9a7e258a6b942d854b5c,0x811758aaf98fee8d4e0b,0xc079e9752a1c7afb1ed8,0x28703264e0f71c80f911,0x3ea4ff4c35de6bcd1a2c,0x6607f2210046dc840c62,0x3ffe357ca5ac33bd3807,0xf3f8c20f1abd04cc0d4b,0xa9cb885b0107dce9ac6d,0x7619eda657a33eb8dd37,0xa07e0c0746cf8af06f01,0x2825b96c0c38dc38ddbc,0x6d5221a1834cffc61100],[0x422ba180aeefbd2c7a,0x82586bddc2d04a9a2e47,0x2b3fa60b0160f8cf183f,0x195ecdf5bf98f7f2fd59,0x5f297520bb161cbfab6c,0x556d41ef56cd810b39ba,0x81565e7f66ebe419e818,0x3dadb8e932397bb4832d,0xb3af72da28c969bda9aa,0x661f38a101142dc70fc9,0x241f1581528c843d012a,0x2613363eb8da044c6a93,0x47d17120f25d27225cf0,0x707c5d2c0575ced19d1b,0xd1db06f1ef4e81071100]] ++
  [[0x14ae48e9e1afd504,0x21f11ffb14f2953e5d80,0xb6320f4519e8f8d2fd76,0x2dad22384dbdc5897f72,0x859a70d620afc8842e50,0xd283576c3f7c4e8e6c3c,0x5ab036d01212c3baf9a1,0xf431eb8d249f8d416a80,0xa96b48b3607a449f06e4,0x34680f8705dc50eee1ee,0xda7daf6146710fc16856,0x71523db94f1897b6e6cd,0x778a10878dd2592ab861,0x5b9a6bf907ccefc4a942,0xc1bac350954a40081100],[0x341,0x1e9656eceda1fe20a301,0x36c6baf30625a78edf87,0xe8cef3c035c56938db12,0x4e535d7c31abc187d72b,0xc48fbd61898fad088ddf,0x947c2d9c5d2036800ef,0xe6a5b1207eed226f9860,0x9c9d11243c45911c8d54,0x89b3d94c52060bf4c02f,0xc3e4364d6c995b87c02c,0x1ae958172725f5c625b2,0xa4af82cc9ca54ce6cc56,0x66a468db147153bbccba,0xee1afc3d6b631b37df7,0xff2149246f2cfb102100],[0x294,0x2fe69b9e77bb7176f68,0xac49527e387c4055caa3,0x861edaa81baa7aa195c1,0x62b61b0833f36902d8e0,0x9565a21b3d6d14044706,0xce1baada3feb507b6f56,0xb0f79f27d11f809a9190,0xe1458a86e0a187c9fa32,0xdbd7fe684560ae77d5af,0xe5f9c10bd22acf54f46a,0xf5328156333376133b4e,0x611f351cf2f111609830,0x6556c56297c669f15f5b,0x4118517e4a007e034cbd,0xb43e8118eb949a112100],[0x124,0x3a56db6b7cef8c0d21dc,0x3b187542242f1442474e,0xbe61e1349f4736b9c8ff,0xe6d8b193bb2404d54448,0xa5bc70d5fcf33720906e,0x638d4d60a8bc2e7578d3,0xb668cc2cc6ead43a63ed,0x88f70c489973cceb7483,0x9b02bd3d10ffcf15bd81,0x28a8f53e8edb37275f1c,0xce59dc2b41c33efe75f6,0xcaae9aab49af7498f69,0x503896c28cae493bd983,0x361f911e16d940375871,0x9785edfd8ac300122100],[0x3a,0xb03c92271fda131cb2a3,0x5013df33bcb819eec922,0x45126afbf3b067b2c476,0xa061b519736fa88a73ed,0x77a5e87ed37bda420f6d,0xa72c84a4fa5099a91666,0xe0e620e4399c1973be92,0xc76e7553a7078465693c,0x134d3ee2c7cce79f6063,0x35beb8a9e6af470a112,0x63e831344fe95785a07a,0x7d34a9c1b8e33c3f7dd1,0x83688055f243d92ccef4,0xdbe89566a8357cf15c12,0x776ded9d0162fdd32100],[0x6,0xef01ec73e7758864c7cc,0xa4fb14ceaff9520aa1cd,0x275f4e216a08f003515,0xc86adad50417bbd4bbfc,0xf3bf93aa7987d17fd35,0xb4f5df0984cab3692de5,0x5432265b57fa1bb35d28,0x8968c053cddd04a66ddf,0x21f6e8f53898a73875c7,0x460516b458f8f38a1cc7,0x7d44e09120fd278a67f4,0xdd91d46139fd1c068549,0xffc34a8d88560ff8e821,0xe3e1386fc19077aef60f,0x7ccc2c8115d598f42100],[0x61e09751564b7fa18201,0xe83f16c17aca443b428d,0x2c56a40404ccda852745,0x37c362a2e79048211b5c,0x4294a4780d928b5b43ce,0xc162432c081692db85fe,0x9a335d9c7dc4d762def1,0xc3ab0b0130a12c8de2e1,0x25649a28e5c6e627f6dc,0x892c8ee583b56da6acfa,0xdb5ae52a6b5da3046f9e,0xc9d0f617f2c9e3400085,0x1b231c8c49f666606c99,0xc4dce6d9601799a789f,0x7bb3cd6f52f43152100],[0x176225537990a969113,0x2e1131833bef0864b916,0x6f6a898a96ced1c5ae36,0xa0bd19449bf1b36f007f,0xd1330d24257e1a72267c,0xb5bd825277a15a368d76,0x548338383a09dc3d3306,0x8b1d6522ec2cfef46ac9,0xa7e7e9cc0f6a9986f956,0xc84e6e6220718547a010,0xc8e017a66b4546dc8b09,0x879a59b2716a8fb81723,0x210c572bd8fce1a8c3d2,0xa161eb68064a924817ac,0x50f84ac0722500962100],[0xda5fec44b790ba4,0x699cddfd7adbe1756dd4,0xfd467d7a62b1f74b6ec4,0x7ba2fe14fe5ddecde3f2,0x6f60a4287ea09afab4ac,0x3b39cbe615d10c7152b,0x9c1d2ad9e474de91f9d7,0x45436af7aef51938a61,0x481b58db968c05fd2a25,0x45275d15b0cf938d1cb7,0xef06cc9e89f206ef57f3,0x2d89920d6082c100f7c2,0x8f04efb66c81f65e84a7,0xb1f93c4396e272681dc3,0x3a60ae40ec00a0072100],[0x92,0x89e4010523228a41e3be,0x3e38ea1873e7b584968d,0x65eec8f8057ff8e565d7,0xb7d6fe5b7c23573d4474,0xd4f49d918d3ca0c7fb9d,0x3607d98ff9f49af965f5,0x6a01487f2683e00262fe,0xfb06f47293e0c8292e60,0x6e3f58fd0cc12697985f,0xf67758cd7ff29ab6db39,0x4307d0e16a0ec8671f01,0x8a315d6e012daf4182c4,0x34314da8adba13e2e197,0xb9b80b3b7b94732a199a,0xdbd4429c9ba393103100],[0x95,0xac4c1bd4434d398cde32,0x3b556dc297d47afc0352,0xbf4403afaabb91395bcf,0xdbccb86833885e52b67d,0x32357e207fe3a516719d,0xee1e0e1858211503a8ae,0x77cba8c1aa7d1ed48e1a,0x1adf6d654c0cf5be83bf,0x639ef92f9608925eb27f,0xfde64c7caa68b76eb85b,0x21328b774e555b202523,0x29a001aca9b73cce5582,0x22d9392b28769e3e27b5,0x71ebb84012d614e25dc6,0xedb7a89a7fe08d113100],[0x33,0x1e605d391228d2688903,0x633d05c35755cddd0160,0x63d4d17046e82fbbf775,0x6091a6bfaa223ea41331,0x78e4a1c442106676ef54,0xee59472a5f027daaa6c8,0x649ea34bfb077cba6c84,0xfd0b0d5da2620fabfe0c,0x2c94b043765a727adfa3,0x7b82b114dfce17a215c7,0x597f86d322d32e0e0272,0x1667b61e2da54ae641b8,0xd76b32c5ca43cac19606,0x2749c0fa20d6cba617f2,0x18273afca4351d23100],[0x9,0x7e3dfa5a8ab5037d4854,0xc1f9ef70dae8021b7028,0x7bb7b95f1be4a4005230,0xdd185bd2fc84148e0495,0x8702525b8b1579db8511,0xe35784a063f7e87dd71e,0xe16e00975a622fb84e8f,0x5b965428e60dfcf51b6c,0xecbf4e4e4dd6eab3628a,0x77903f1ae34be582be47,0x610a26aedcc276bc993e,0x616386eda557b34e3fba,0xb174f348fcf36069495b,0xda3cb27e31e0a906b1da,0xb18a859c22add933100],[0xc4276d1de02c45bb01c5,0x63ae9e6c91666e5bf938,0xc86496337029fc6ed908,0xe042ffe956e39522e24b,0xdb94451b1d32c99f69d5,0x22da58a436d6025b0b32,0x7c51c5f21aa21f62a557,0x5e07e578f025ef4e9b2e,0x97bdad1eb64087a0a7be,0xbd8d7d41f323090cc32a,0x1a14a075213aa339f53,0xc4f1767246055a4aa6eb,0xe5ea683710a8f225c3bd,0xcfbf198310ce69439c20,0x8d8c189599c02af43100],[0x42b0646d36f356e6ddc,0xdd225ca4c8495439275a,0x90b4088f78a576e16807,0x1d4fe9e690d8f6d57d17,0x1c70aad2dffc8516b3a1,0x45a3692cd5f403f7abdf,0x6a275edbfa20689dbc20,0x9ac345614bcf6f84ffcd,0x246c97ad5ed8c61e1cd3,0xb05166d81cb4f09dc506,0xe8eb4019368208df4eb5,0xdf8c7eee5ca21703fa1b,0xa152dd7c6d82b93efbe1,0xfe12cd5afe562b57e3fe,0x32212d06af42aa153100],[0x83a47a853c1f8c,0x4045298eed4e383ecb2f,0x91f802fe645d96dc6c38,0xb69eb227a7defc5eefaa,0xada10b63acb56e686855,0xc537c98777c8a83e9117,0x62e8b26e3a9019f6d1aa,0xd319719b89aa6bddb48,0xc4dcdd3949e782a27670,0xf44c1d93ec41f05bc7d7,0xa1faee887e4c1156af94,0x24ce983ba527a375311,0x1ac85ee4db76ed63d9a2,0xf549ddd960f03b207f90,0x81d3b4cda61800063100],[0x15,0x4d38d104dc3681b56bb9,0x14284ca4ad6ccbd4655d,0x3d5433fc67d8a1328789,0xdfba56073f8901e169a,0xeb2a859fdd5f86df954b,0x3a1c55976e60281fc839,0x4efa128b5965f0d98b7d,0x2dc89fd687f47305684d,0x7936d74d08090a165844,0x2c5a7745af76c1ea73f,0x4f365357e4c5f6df966b,0x32ff133dad090d931bbe,0x9fb89c0bca74f9b9b999,0xef3859f5909ad14f564d,0x4ebefed5fe94d9904100],[0xf,0x33878eb27d9edd52b8f8,0xfe8fa0e6770db8f5743b,0xb86825354920e9086908,0xb0deb8b0f2509a612bc,0x81109a04eec80d2abc02,0x45190f32dd471838bdba,0x2d9d2168f62aeff43251,0xfefc37eebcb1037d68dd,0x5b94e765fbb0c0942f18,0xe44d070295307880f254,0xc70ae13202baad3bc7cf,0xb04fad58fe7d55df64b1,0xd06aa9cad387d9805e2f,0xba711a3a03559425e88,0xa8226fae028977114100],[0x4,0xe5ad7d7ca323111ab2ce,0xb8833a4969807718d725,0x4a2ec1b76b268e459e07,0xd1f87058938a92449f5,0xabf5591fa3e0aa9fc31f,0x63b59d2eb92c52c002d2,0xe9cf72dd88a790deb300,0x37a3027f1c6736eabff0,0x5117902cac4186b49880,0x1f2d409468caad87272c,0xe201b43243cde0fcc2ca,0x45f843c7ea449a243845,0xd8a4998aea56ca0d5a3e,0xd5648aa287c7982f1087,0x8adc4c0d5863b8524100],[0x90bfed0ea885f74155b3,0x4399e12b5b857ef4c965,0x5291b3753e5f3aa34097,0x79528d4b3709c92d1786,0x21ff2dd140c812a9fe0c,0xce39c90c6a5f5c8a1bd2,0x668027209d3998956a9d,0x2b39584686a2f599519d,0xb9b15a23e22718d3fb17,0x27f09e22fd98fc1dd972,0x9cb950c4b422342bac19,0x1ac7db97b91c74144827,0xaf45122f8883c44d1447,0x1de6493ff694bcdb8f65,0xd42d5c5aa0a979534100],[0x4718858dd3f7a0ac4ab,0x79a3e58ad2f2c1581911,0x7992a1305138d695fa7c,0x6ef2b26a37cc293e5893,0xc59da5d7a6849a39e5af,0xced58f749d8a29db23,0x4dd538fc55f10a444f0f,0x9697481b70b110de79ea,0xdb40f99e7c6b7ec818a2,0x82bf066296f543e48d4e,0x3cfc6720824272bbda3a,0x8b57b2a556d6274f848e,0xaa3d46bffde28c8710c7,0x6ff6594ddc63f9c438db,0xf329223dc760ee144100],[0x312a5ee6e832ae,0x5ab7f356b486a389375c,0xec5a55e43cf762583088,0x4fc2258c511b8c5900c1,0x958bd47a2f8b69385ac1,0x57c83594bbead21165ad,0xfd85b244b2dbf31b4ec0,0x4d8d7d16adade4735295,0xe7b66735eb377c02245f,0x5cdad294391f7ec6dbcb,0xfcfeb19fd71fb8a85951,0x220c94c1583674bb7c17,0xa2f6b2142e3aceb2e36,0xd610a0a829fd40581c5f,0x4cca4b115a5bc0054100],[0x1,0xe044fafef19be2ef6379,0x1c3d0d0da54916ffd2eb,0x63e0d9ce5ebcded63632,0x2a1e16e4c76c26568d71,0xe8c53c91de9dcea50830,0xb07d6c21133d7c34a432,0xab30ca7222fefc98839b,0xf8d43bddeba3df486707,0xfd7df89bb9683bcdea6e,0x1ffead373bf94ee1ed52,0x2054f36b55f40b303cdc,0x49050a8bf43b416e1579,0x62de46d66b00b19e9ab1,0x9a6c7f8d1078743b8928,0xc6f0de82ef09df505100],[0x1,0x54f9a21d3d004a83bbca,0x58f0ed4422e4819399d0,0x5a2af9e9d5fbf40a150c,0x6b88405341b2bb89da91,0x87ca693650dd0506462,0x263e37b195cfd7c1e94d,0x36624c3b74951a3fb1b0,0x74025b6eeb42c4b731f4,0x93bc3b3c2b4ca38a3d00,0x419a5e17bdbb99317db1,0x98fa8d7c6057882cec7,0x9d75fb2faf95dd91feb1,0x347fbadf5775667bd3fe,0x7289cf2577e5c4084a03,0x96cffcb1bd57f915100],[0x3fffe8a6b640d17be76f,0x978604b274a6d068fe48,0x94eafb65b972bf0d0151,0xd38fbef58a005a802e2,0xce005917a9a8c3b056ba,0x298615a7958754d1b913,0x419e7262dbf77ead8bbd,0xf27a952e654f99edb0f,0x68a3d67dc07bc68240cf,0xd1cbb3e80da422300f74,0x1fe3cd5f72526298ed5d,0x437369e0565c6aa18790,0xa203b91baba2e79f37dd,0x210ea2fd4ad23e10af5,0x5011e7762e26e3925100],[0x3257433d81d73e47d3d,0xce62b38a67f0d0061003,0x79460477b99679062d17,0x536bd7503aab5fa79da6,0x15db93ea90db38a6d9c0,0xaf5d37cf9ca62b80c2c3,0x80771cf069ade9e4040b,0xade2a10426a2b2e59cc1,0x7ffee3b8901437ccb66,0xc1ee635e9c9cd165d27d,0x30c1b16bec3d02c2f88d,0x24de89624496d0f76d78,0x26b698b398e36bafbf8a,0xe927f57642e9230e7efd,0x7d18d952c8d16135100],[0x19a83375bbda33d678c7,0x3e8b7e7d858b2e510a48,0x53bf7b58c6353e1a9522,0x67b0ea15d30a84cabcb,0x3c91fc176f710e661598,0xa501a5e7bbf2e698bac6,0x28e850df9db6c41a05e5,0xc37a5435a7fbe49ac42f,0x5be4f78f4d0e9715b1fa,0xa32a9627b8d70e9d7b78,0xdf2f6f634a83b3175bd2,0x729b2a2cc2fb1395e53,0xb3352f53f67a58a058d4,0xd1700ad6642d8e92578f,0x4d37887446c168106100],[0xc2801855274d6025bb0,0x81aeeb246d73a294c1f1,0xeb3023c6dc7d848cfd3b,0x58826e1ac08b3c833ad6,0x4f953245fdee8788e0f5,0x195e1debc76a2ca45068,0x47a4f8b9431cecee18e4,0x497382320cf194301e94,0x92642783923f4c78ec65,0x73238715fa8b93092182,0xa53f5f122480cf5554b7,0x8bea2eb5b46e3ef00d50,0xa1a8f9caaea9b0032788,0xf53e180f476e8a963f86,0x856235aa5818e8116100],[0x11af051a62729b7efc9,0x9797a99ba8454b148df3,0x694f0287f55a818edeaf,0xa0644e305d4349c0ee04,0xf87ebebdcf4fa5dad59a,0xbdcd0fbc03f6e67ad36d,0x80534537a331d9648910,0xc854dffd40934050793d,0x16b713f20a37f24cc67,0x6340338ffa44d9f70956,0x8493b359959998099670,0x90628502040e78c13eeb,0x6a964e3d73a120fdaa31,0xa6bd65aa0950100374bc,0x2a5039693d8e58126100],[0x802c8ed334285a68a5,0x4b75d964b4455acdee18,0xad4603727ca07ea87e9f,0x752137ba91255280b1d5,0x85190912f2c39d2f2dd3,0xd1aa00bcf5672cf6c036,0xcf808aa5927526dafdce,0x1e5c3165912e3bdeb155,0x8fbfff247e40110859f0,0xc70af672493b7323b783,0x4c96890a70ba73237ce,0xb5146aa16dd6d9222edc,0xab79f21004508d6358a,0x45fcbdf4ef28744318ae,0xddb916b48ea6c0107100],[0x1c7badf60b97308908,0x49a86932d2ba142dc321,0xed9dc7e08d78ffb3aa5c,0x52eaeff092084b390b13,0x122020435f294b526a0,0xd942390d8bde09fdf1d3,0x4a8e57b3041a08a2714a,0x3fa2b5a4caedd46a604b,0xe70e38b2c6b8e757306e,0x651ee16ebaf0c440d372,0x72d76c91ec3b7a7ceff5,0xbcba5eafbf6daeb26db,0x909a9523c72bc9132857,0x9dc66319fc41e0f27743,0x4db75a61034180117100],[0x6,0x13316cd252ec63f1d8c,0x5afdbf196e6bfeffde1,0x93245875ac3a0085a040,0x98087d61b29c8d7256a,0x84e8ca3cfd9b680e7ee7,0x32a54e46bdb80cf5c4f2,0xeb4b71e074d89b62bc43,0x97608a99d9bfac147a90,0xe75478cf920f19b5064c,0xb91bfe47fda4027873dc,0x939e8f3a3d0713d739c7,0xef4629f901271cddc1d3,0x176355bb2f54d2067b04,0x47c76ce17ff87fb2fd2c,0x74b2c725d34d78100200]] ++
  [[0x4,0x3cba29d9349a9910c73f,0xda164514decbed1abed1,0xb684efcf647487de2553,0xc0743581d1f02389cbbe,0x5d8e2a3f6823a6eede66,0xb0e2eeccf4a070755ce0,0x11ac5dd577e395c91a89,0x3ce7215c833e52f32163,0x34b09d2d6348882b4616,0x666cde9fd943b229103,0x58cca536041bf444e45,0x1f28ec77e0534f4df6c4,0x3def9d31885c4bb3c92,0x9dde8e5c3025f18f27b6,0xa68710c6714ded010200],[0x8,0x999d93f6ddf6370dbf49,0xd9bab087b5290a93c47a,0xcca1d91b8f0043540430,0xa29cc7d3f5637cbb8b91,0xb86405505b83d31cfd72,0x59c97221eb9b32938339,0xb9d9f52dabbe7de9207,0x609d650a09c1b818ca13,0xbf57be3985702a3da39a,0x3dac31c5fcf8c4a521ac,0x119db8c56fa13a448a23,0xec598cfa3836968b7771,0x77c5c2b2b296ce900e1d,0xa93ea993bfbb89cf6401,0xced7a44c481d77820200],[0x2,0x55d0bccf6cca09e11415,0xc2df99ca6f6c60884d5d,0x9c4054693f7b3312d78e,0xa40dcc96c77e90450f05,0x78b4e7eb1bd5fb45cab8,0x9ed0a96149c6102dd8a2,0x521a5c0a75001f08e137,0x1593ef774de6b054706e,0x5d239b1d657a58124981,0x48003afed06b85a06166,0xabda577893a5636dca22,0x2c9ab06191ebe07d0cd2,0x9f849e30f4fe9e215ffe,0x7882439282e0a14cab21,0x9ff561add757fb030200],[0x379b565b33b3733a1b88,0x5dbd055452dd81e460a1,0xa6a802735be0b9f78e84,0x91992b4d0e236e87c2a0,0x3a23f5dc6d0724ddce52,0x8787b1242213441ed94f,0x7a61432074308b41ace4,0x9ac98a7bc98aa8bbd003,0xb299377f986fb3bd4243,0x20927469d973bd56f2c1,0x37558ff71d9cfc3486e1,0xe006f5319e562caa5057,0xb94061b3480cebb4eee2,0xe1e1f4d2dde8a530822c,0xd764d01835b418640200],[0x5a697beeebb525622f,0x71dc1737ddcb8c127fff,0xe6e0735a15bb20e1e91c,0x4f8eb5542856284f0209,0x7497208a32ebf5fbba53,0x99cd2b5d6866c827b4c4,0x5343ecf220a314fb1e1f,0x31c4d8a29433b3567cfa,0x4831010a11d4ca8ef1a1,0x4d6b3cf6a4eb7755c251,0xde8bb299394374a5b229,0x18bed9ef5be0ae03545f,0x3a8e07e2b41535ccf611,0xa2a6ab81a226b59a6ced,0x26de9fa80b3c6250200],[0x251f0f535c86ff23e1,0x6e4c2f89a18a90b4ec19,0x3f280904ad1155307e05,0x711b28681fd4f0f80a0,0xd57b89ae581cabd0430,0x6ab9fa50a98620c3c93e,0x7d572ca5130fc27e4788,0xfb93cf74b254010c720e,0xe60ec4c8e400441501ae,0x11aeef528f2ee72dd94a,0x37285487b23b4d74fe36,0xc860f8c06a210628e187,0x5582dc5d6170a2f0a7c6,0xe0ee58704f4deab71f00,0x85d853165a8a73960200],[0x27b4526ecc81b5a,0x71c2aea55c9fbb27be9a,0xff5c570aa541b17ef234,0x1d4e6037dd7190c23036,0xed72ac303eb10ef864b6,0x520010e83821d5e11461,0xb0fffcf414532fffbaad,0xed6503914b6fdced0ae4,0xd93de8d665c74407a157,0xb00817cff7222ca4e246,0x884af5af3f72abbef24e,0xbbe50ebbab7c1dcf2711,0xe3a4160807c5815232e7,0x9f70e7cf19380310696d,0x745c46368ffd40070200],[0x39,0x89c2584782c081684113,0x738fc3fbe8c465d99917,0xe04138847d80f673d6fb,0x5e86aa9d8aa10c4c16c8,0x77d299531b20d3c0affa,0x57a50e4249792d3bb95,0x3b76e677b37f17ef75b6,0x977ea4c4444b9ddd0695,0x36ab522847bcb505860a,0xab8145dc84b1e9a8242e,0xf20b21c28a1070540c57,0xfa24337f3fd46ec15752,0x970e27ec8f6c68a8a399,0x4ba310c39fc090c7b913,0x99c0d13db896a0101200],[0x18,0x4f9666069d3c108e5e6,0xe081447a189f6c5fc285,0x982d1f13ec3d58482eaf,0x2641ddd8f06028e78037,0xe3b4f5383bd7f6f1a9a2,0x6fd1a0b65f4c4d5170fe,0x8d3dace05243ebaaad2c,0xb501d99b027e0c12bed4,0xef471fa89947e07dc183,0xffb64123b445a1e2efa7,0x6e57a482e002d3dfc6f9,0xd8d3f9c9ab7adde8c59,0x37280d67d07cdfb10959,0xd2b493c0641864d37ba6,0x10ee52bfbf35fb911200],[0x3,0x27b2f7187e46c6ff95ef,0x90121f264f6b19656ce,0xae58b6eeebfff15b3b1a,0x4ea32340a252232d1e2a,0x12815d52cfc52ad9e602,0x4b234068199dec8ec3af,0x994d9f3255e525640963,0x256915e3dfce78d7879a,0x1846b5d72d2a81756f92,0xcef129487e059033c24a,0x4ef3fea47da4b09d0a05,0x66859ee8d5dcf80e759c,0x70f7c3a897e9c235be12,0x6f2b681b802232e1a97c,0xc11a0dc79b00bfd21200],[0x185a79debb69602eed50,0xc8134a1e660ae6baf7d4,0x347769ea2f76eff27f0a,0x46b601c6e96f519013c3,0xaeb48c4c1457c63d160a,0xcf9b00725e16f3bbf02a,0xaf3ebf415c06d0d1a237,0x4e0b99479be879f58561,0x9fbc3b2d24b8e83dff54,0x5cdf51352eb58c45e861,0x5da0639bb24954d152c1,0x978682e9567c526163f2,0x240e13dca35350e5a983,0x9ad99c240576382cbf3b,0x28939546a51a60f31200],[0x893ca6f06b16c17fd0b,0x49f8860f0183f5663f04,0x6e4c751e681b3201fbe4,0xc4c9e5b9e8c038eeb73b,0x243a34e534205bd89951,0xa8a08c2f0f34a2b26baf,0x45b25f48e3d3cd8fd224,0xa4e9e318bc5438c9c352,0xf26f9a44aab3f107d0cd,0xcf0f94176ed4a864a451,0xb00f904c73ac7bf1c8d5,0xc0ba5b3336a1a1a4013d,0xa8cdaad89abe9d6963fd,0x99ea3d4de4075347525f,0xdc363b13297fc3c41200],[0x4fd94911758eb6d189,0x23e8c45fe8ae8eb828d9,0xbc37944e21412cc4821c,0x6d2432eff90a3148af59,0x35662b856452aacbb72e,0x7db7b850ca3387b7473e,0x7110f53f86c80917b8ec,0x7ac7139a332b76cfad3,0x7ad6edab34c56e06ed38,0x1ac6fa1572243b20a935,0xa73c3d5a721864677b7e,0x3476a032f5c7d5df4b86,0xad40beff68a046cd8672,0x4368abdba0cfe8e391b8,0x10295e9bf7222d851200],[0x57280ea48559f1d,0xba4f033fc81fc8ca6a64,0x2a6c675833a26bb3c7de,0x8c0b1b6b7b4bf39fba5,0x786940d97bb77246af2c,0x6d5af77873660261f3ca,0xf79ce35f2dc30997bf58,0x406aff45c203bd55475e,0x8ab89fb11da625fb4af,0x227d7539dc6b03ebd538,0xe2e10dac2864bd5ddbaa,0x6615099e618f5128d4a4,0x6c7e7672f8d67c8ec827,0xafdb9c4e278aeb4073cd,0xc65e50f88cec80061200],[0xc,0x7c3564a716876560d015,0x66cf9dd2f7196e11c50e,0x5101485eb9245f04e71,0x359a34909772430b867a,0xd028a5a4b5cc54ea6fee,0x3c3d8a02fbef492f807a,0x8d3ea41217ccb0d069df,0xed4ae2048370f4ca3bd5,0x560b26e810ef4a6f8f23,0xdb8e76b182c83d9d47f,0xb06f25e451e0dd86a01f,0xf3735e5fe6d89d92e8a8,0x1e50e6cf3de26ec1e13b,0xd8c4e3f93d7b49430050,0xbb5690e422c8f6d02200],[0x7,0xb1a5f42f519249c6770d,0x38e192b328804a589909,0xd52104b9ac80866bd854,0x66b708333c3f3722e57b,0x8fe6c331903cdc8cd041,0x2913b3147a2ca0dd689d,0x8d7286c068a0f65f1a09,0x365b74d4ee073bbc7a92,0x1e664ad4cc1d6c302f47,0xb878230fa894c42d32c4,0xfb1d97cf843f8a0fa368,0xf412112aacdaa79d66a2,0x585ae47f8178fa3a6037,0x3222690bfabbb636e1fc,0x82926c36706f4c512200],[0x1,0x3d2cb7337ce3f312c044,0x3af19ecedea4ade6ba3d,0xe132d27affcf9cd68e2f,0x6e4c0ffa199075c132cf,0x8736ed6c107c9cfbd7e8,0xe3e1d69a01cdf4dc389c,0xebc7d9941dcbdbb3bc70,0x73d8236a3f8977abf91b,0xa6390d771d9ebc2a9a2b,0xb139964517edd48f9523,0x4a13c0126e796536fa85,0xb0f0b0e804e7a22ad855,0xe9653b900cdca72b251e,0x4b5d5cd054a266f2a2fe,0x2810febbd0312e722200],[0x1c7ffe512096c1fc240a,0x583ee1431cf0927f4c42,0x5690c39b1f1332477e3f,0xfe10695f4e1ab1d7b8ff,0x19ee1a4b23dff2c3b2ab,0x418ccdf5a9f01e3e961b,0xb0460126c5cf4c2c7282,0x7997e617973cf7398e5b,0x6fe6304b41bc881b4f2,0x3a1e07c7bf2d69cc694c,0xd8f4b82d2ee8472b7cc7,0x2c4bd7d3b5f2d0eb0766,0xe21058349e863da1b9a2,0xf123b1ebd40ef691236f,0xba6c75c7a0a190532200],[0x6bfe3cc83a3057f938,0xfc0e5201851a718d41e3,0x403bae01c34600f4c04c,0xf95ab1651a28c9b010f5,0x1698c4e9566c9f915f88,0x9bcb4be35a1842f7725e,0xd5d015eb4a4ee601be57,0x91742dab0df8c80b6ba6,0xe2ac64f9830e064d9e1e,0x7b93e3ccd37d7f41099b,0xbb682c94b28464d7d67,0xc07641b9d3951c9964d0,0x50a82c9c29236fb86db6,0xecf17653af4cb2567d72,0x415849e8fcc41d142200],[0x24189d6e6a45ed,0xc83bd7eed048d5dcca70,0x814f1e1cf3bc8e193f29,0x20f0b76f04e95a778d93,0x282fb4a0a7cb45dc151,0x2510537413720444c179,0xefec57378992972ccc02,0xe840e1d01e5778e53464,0x87c19da7d3cc449ae7be,0xaaabf897441b1690a943,0x50487e6bfcfb1795c6f8,0x5b006d59046c66debad,0xce7fe69db05512286deb,0x3b148a01cdc365d6d608,0x480cdcc3cd2e20052200],[0x1,0xe06729bfd1c1a4e3c6ff,0x486c10b4883e24648bb,0x7c04c80a6645305ca95a,0xf134128a4e6224bf4336,0xce1d10f1ab7557342574,0x3669eeae8df9ad3c64d7,0x643ed9b050ab1dd01a69,0xc22cc43298243aaae188,0x6e18c600e0a2ffb79196,0xc65afab7bb56c491a2b4,0x1458e2414214cff38d09,0x78803cefc43a8b694053,0x6a82a98dbb8c024c2fd3,0x14faeab3ae3ce5c46486,0x28d53b30759d51d03200],[0xb81a7082f6b2e84764e7,0x64dcfe62cd1f7dfb4218,0x8263da3cd9ac0b1e98fd,0xad22dfc24298c2f28053,0xdfa2356b77df0742f26a,0x50cc455383fac886a3b1,0xacfae34a9c0ea22f6922,0x2272e38b635a51be227f,0xcdfff34b2f07fd59d284,0xf921a171e41b7c570216,0xda0a2f675e862fc0697b,0x7defd0b2698406222b95,0xd27bfac9b973d9d47380,0x949ffdcaae88cfe0fc4d,0xd1087530b8cf28113200],[0x1bc8b5196901148eb8c4,0x96bde4f8a1e8ce3630e5,0xc9e214a6890a3e0bd400,0x85d23583d3868eb7e2a0,0x6d8071549fb449b13463,0x60d72460dc81e592f9ed,0x940bc31518969d3d7420,0x38aa18c3b7bd4cdd2b3b,0x817121025cde457ea9bf,0xc739697c1c1f919103d2,0xa08702686b2038d8f3,0x6c9f5937a66d1b5cabcb,0xfec0e1075bd6531fc56a,0x3ff0d4f56ddff512dc41,0x70cc62215b8c1c723200],[0xb7d2c7d46b03f43307,0x8decd97c559d88243e7,0x5da5fe2f6460acc16ff0,0x92bcaa3b122feacaaf30,0x924382c17a92f28e6a4e,0x8f2cb864d1f7ef11b78b,0xc6f9c2159ada0dbe1fa2,0xde68f9c8a4094e33b7b1,0x92a5f874b69bbe20b03e,0x52ed021366f3b5fa3276,0x94823b06e497a8f21256,0xd383256ad1f0dc747260,0x96c32020582eb4b689fc,0x3577fb8253b5898919b0,0x1a5e7796540bc0133200],[0x18952f73741957,0x2d5bf9ab5a4351c49bae,0x762d2af21e7bb12c1844,0x27e112c6288dc62c8060,0xcac5ea3d17c5b49c2d60,0xabe41aca5df56908b2d6,0xfec2d922596df98da760,0x26c6be8b56d6f239a94a,0xf3db339af59bbe01122f,0xae6d694a1c8fbf636de5,0xfe7f58cfeb8fdc542ca8,0x91064a60ac1b3a5dbe0b,0x8517b590a171d675971b,0x6b08505414fea02c0e2f,0xa6652588ad2de0043200],[0x3136f0093819a41d21cf,0x94c12354a35339071842,0x866a36113952f9cd82ed,0x58ef40dd13c0314b1c16,0x4d90fd2377710059358f,0xf75b5193fe5da8756a51,0x8a9164291951c469028c,0xb4a668538057fd2167e,0x3ae9baca9daaf1c8f8e3,0x91dbcdc4bc48f9ef9490,0xe91bcd6f8d88a412917e,0x5747facba329c42651e7,0xb43ddcc1f5d9ea8ab860,0xf05a81b02e290f11e3cf,0x6061281611a255504200],[0xfd36575eb9d0ccbcd77,0xbb6d214a7d3d64d19bc9,0xbbbf700d410c2f981972,0x8633b4a2b68fee90da53,0x30f1e1c00bdf5dcfc640,0xf1e5cb7070b18fec2b33,0xe92b880cbf8a33b5e238,0xcfd2c44203b97bc63fde,0xde8f7efa058b51ecbdcf,0xc7457a35754a465ccffe,0x8e5fd0a34500c5c2cdfe,0x251461ae5f0e243e0a22,0x7281e79b6781f08c8e2,0xee20d8ecf11b70311daa,0xd11b9cfdcacde2d14200],[0xd48798254077bb6157,0xf68f24a8e82590a1bcb5,0xaa72a8137fae59dbbab8,0xaf4a16ae01d42615f1b3,0x47b795adf83cff6fbdf6,0xc911be33c094bf102d02,0x3ad737bd489e61318db7,0x4d4c9447469b69caef6f,0x67e96428dcb9e0584588,0xb6fa8b71d91224e89a5f,0x144d07b5f16fe707d521,0x6ed951c05909e976b862,0x8d0739b29ee0420490ad,0x302efdb55df756122be6,0x37b3a5c508f5d7124200],[0x301201cf235c2350738,0x2ecd4d608927c6d3bd68,0xdc8eb791415ef47477ef,0x771a93989f9167648c62,0xdc97e56e0baf11da03f6,0x8f9512639702a8b055ca,0x4b7e0942adbeb505f419,0xda67eaaf59a381e4adea,0x5862a36f7afb5e40ee93,0x7ec80cb6f27d1a685e58,0xa9f243351c91a22f8766,0xc2fdd24e523530e47026,0x3ebd12eb42b7c5da5e8a,0xc0fcc108a194bece8bc1,0x80fb025e12bd9e105200],[0x70f8779e68282616b9,0x7a2b2bd32783cfd38c47,0x13da3e59dc786c1cd344,0x1f4a8558f72ba55712e,0x20219da599e1cc070673,0xaf368bdbba252de53af0,0xda2b3006b4cf5c189e3b,0xef143184864853520e2e,0x7e56b3fdcf1d80599ead,0x763000fd6629f809754f,0xb6873a790417e528d979,0xcc9a91f4979a1c99376d,0x2f841616f5c157d91b67,0xf8acf0db89ea4c587bdc,0x1d97b038f0c840115200],[0xe3dd6fb05cb984484,0x24d43499695d0a16e190,0xf6cee3f046bc7fd9d52e,0x297577f84904259c8589,0x809101021af94a5a9350,0x6ca11c86c5ef04fef8e9,0xa5472bd9820d045138a5,0x1fd15ad26576ea353025,0xf3871c59635c73ab9837,0x328f70b75d78622069b9,0x396bb648f61dbd3e77fa,0x85e5d2f57dfb6d75936d,0xc84d4a91e395e489942b,0xcee3318cfe20f0793ba1,0xa6dbad3081a0c0106200],[0x32d0551279b9c2459ae1,0x31fb5bda0ceb8d65c2c1,0x9d4febfc55cbee926f96,0xd990337d3491753af337,0x455cf057433058919a26,0xb7080dc3309fb8cfdab9,0xcc4868778d3dbe12b3f6,0x7d147585031a97559967,0x4636fbcdedff14ecb150,0xecedd2fd36f06efab929,0x9a39c084a6606a45e27f,0xa36bd3c65d1e31573e5d,0xe4319585cf9a5fa96a89,0x990a5b12eba2727a42d9,0xa0326bf46d354d000300]] ++
  [[0x3840ae97c756f8bd7123,0x4bab37a879a6f2cf1302,0x8874c259b6e613a858a0,0x69d0f21d952fb134340e,0xce129d6f31c7ca16b976,0x4b6c5ca1e9a853d6edc8,0xb42b26a0fb96745d0a72,0x6718478a140e67b64413,0x45267637a00d12355e1a,0x1e4d8db1ee364d972734,0x2374d67cf91ac766576a,0x77f29b24a895cf814f6d,0xf10eade609cfa8e7e493,0xe13226f53b849c5deafd,0xddb8ce23d43269d10300],[0x22ef6aed78296cef42ed,0xb7e80d5a7c776092fe17,0x9d634f77a22b2a8e51f5,0xe5bacabeb3866e147cd8,0x2f98abeb1d712d963d6a,0x58eb79742dd3470f247e,0xc0a96e3ee276b6d25320,0xae284c420fb7ed6a4aaf,0x2366721208b5dc3a398,0x7f1c8be0b62eb926a073,0x5ae7c023ddb134d5a45c,0x20f6a1ffc42418ed21d8,0xd68d01cabdf25da84d47,0x2fea643b562420e374a5,0x340af8ffe17023b20300],[0x3ae88c370bbf2e62b5e,0x950610e6a4c21222d7e6,0xce2aedf7791fd1edc0cf,0xea670e15bdf6b82db36a,0x88add48d9ca20da8fef2,0x31ae05cf07b7789554aa,0x3a8daa7ad084f493df8d,0x2ca41fd183df1121c236,0xd4bda8b3204ba635f647,0x45ab4b02afd018f0eb62,0x5160c36022905ee3d22e,0xb222a783a190a1115321,0x477332856d4de11e1845,0x800b98c4813429c4ec2f,0x8c5c23d7bd4b10d30300],[0x2a9eec9af9b9dbff18,0x4b18ba18b835223867b2,0x393840c3555abae6f7c2,0x8529f94413e871ac5069,0xa27a0014b8f591fb0ea9,0x48537fb1a4b60939fd8f,0x86f049390a6428b2979c,0xaadac2b698b24263d1c5,0x12f54b5d1cc01cf24c4d,0x4d85ccfa9eebd9dc2918,0x43c8ad0b3ee384b5e560,0xc771901917cddc3beada,0xb0ce096a711039f62e84,0xe83c86d315a62c15310b,0x7d95b6679f0817940300],[0x12d4077d0a3bed,0x43af0d76b12267d53095,0x305d2b21c060308e0ff6,0xd4ff69801feefa0cb627,0xf4de07f4f702cb72242d,0xbff68741d09fbfb6332c,0xd84d2119d36291ac2c2a,0x35bbd509d12fdb243a1b,0x4997e306064edff1189e,0x9dcf0b8cb402d5b7c19e,0x4605fba9b7b40909645c,0x5ec011a751392a9b598c,0xb9670c76b37698345703,0x63105940ebcdc479ed6b,0x283efcb73e9ce0050300],[0x292e186e2836116fdf57,0x45956c1bf024e1fb015e,0x48a11f6fa8d2b71ddade,0x72139af0f8c1c3c5c8a6,0xfadc1f499c9921c97f5,0x553b1760e003bc67e7d6,0x8fef6e0d0b61aa1bcc5e,0x1f8a10768b399b278a5b,0xc984659b651bf33b8700,0x32e4949965f15fddc7c,0xdbdefde22722fd779ec2,0x597f6953264c0effbd72,0x4fb4103a12f54fec4de4,0xaacae070cddc8beaf5cb,0xf253482964f066801300],[0x14a810b967ef2a9973c3,0xc9e4a4fe2238d7880c25,0x1e09f09f882bfa83227a,0x30adbb175a2f17ba868a,0x9c3ef0794b7feb1a57d5,0xc8a5884c32a146fbb0ff,0xfdd1c6dffc44476281f6,0xb26641d95c3736c25a7e,0x9a34f16330520cd2ae2,0xcdb2b75fe7c288b5e317,0xe746030bf62e6a9b2c12,0x55bb8c04fce48cf3d7c3,0xe00f47a111445934b126,0x4487458716f5f5a1b3da,0x260ec62b88db3c811300],[0x6518c2a369e053146f,0x880ff6418b1b357ec556,0x70aa8a0fffc58f768db7,0x161534ea4cdd64d398db,0x5c6bf1d6750d56425598,0xd30a2969763f1f21db95,0x4928e8915200cb461a6f,0x4696cd45016aaea20527,0x99d0edaad5f1a496fe19,0xdebe19cbadc2c1fb9b8,0xafa3355419b70e8b6869,0xd4b45810a659ac6100e1,0xf23719a38e989d551b11,0x5a65e13c1ff208133ffc,0x98de36f33ce6cae21300],[0xbc914d82ae471b91b,0x4f69593f74881a1bc8ba,0x9d28ec2a323ec9165fd1,0x8fdb510726202c79f863,0x99ad0774552b501fab0c,0x3d40888b8a6043b03dfc,0x4fbdffa72b85de0b817b,0x7ae34f1f5ada189c6862,0xf2aa6469d46aed2ce328,0x49f9f8f95fc3ed68048e,0xa0e6d2a09fa155069e17,0x2c12061a2c232d924f54,0x8cb1859a1587411cb2c4,0xe81bed736d56e21544e6,0xb1772e085da04031300],[0x237995ef9bccec2aaba,0xbf06d01d4acb053d12df,0xddcd6ef227767b8c504d,0x7ac7b7bba6ffe272e4e3,0x7cfd897c2f0964941ad5,0xcdfb21f12ceb215909f1,0xa722d758a2fb319c070f,0xead5c99199b79c5a9462,0x3683bc997e0cc70fb7f3,0x6fabcfa5e707909392b4,0x70c37995a8fee4e9ea69,0xd9dc2d9350b7858398f7,0x50f15063c764ecf72252,0xe30326173d52d218cf34,0xc612245b19e731d02300],[0x5b28adc90d18629cf9,0x46e1aeb5f90cd331abbb,0xc0d758d05ce095ffaf58,0xb450c8909d383a17a654,0xac07595bd12c1e18c1f9,0x2e14eaf3df8101c429b9,0x1993d9b5a4baea992a94,0xe9cc8807e05c90f3731c,0x2a9593240e11c23bc6ff,0x9eee17d4f805d22be049,0xe4994dbb1305acedf27a,0xffc69d09549bcee6ec48,0xa3bdc28c1c3e528a07b3,0xfa7ebf2d120d86fb76a0,0x9de1584930b31f012300],[0xfa2cc61ded6b0b2,0x5e92fa433b0fe5ed8efd,0xe001d03336281922445f,0x1aa8b88c158129220a91,0x53428f66d8f084801a22,0xa428d5b47ce612c6d7da,0xe4fdb28ed3712c098ee0,0x93ca1e69a13e539d65f2,0xb8fddc56aacfb6211ec2,0x6ccdd42f510845c1531b,0xaabc4b8e78417b9e8fa5,0x242719fdfa1f8dcdc9f0,0xc074c7abf67293f1043f,0x2b69fb952689f446a837,0xaf328cd7a6df18022300],[0x6694dce574c72137f6,0x2af7def5b0e14f862fe2,0x119e71ce835b9360a92d,0xcbf3eb5fe2460dd211d,0xe6c67099cb5226e31e6,0xf9fa3d91862db7a7604a,0x7ae22f07d5bfc67dbbc8,0xa74ad9347c8082d3d05c,0x50311287b089a5e8681a,0x7bab98649d15551adb20,0xc6306afd3d4e723449b9,0x2b0652967576314fe180,0x3afda77150093e72290f,0xd92056bbb7a0fd95a6df,0x170bd56d210bc003300],[0x3e3e2d5c5acc26ce,0x7236992c3253ae891d43,0xb28a4d8e66345e71c2a7,0x22f03cd8c6b249bdcf05,0x7ef303dd1866bd4d4ee8,0x47a0b4bb3b5434be3e6d,0x7bf2498a7e46fa3b54d,0xcb7e8bc7238392acefde,0x399a87a4d14321fea77a,0x9016fdccecf3709f7ce,0xe53aadf26237527a954b,0xc01853d2803c3dd75088,0x2d4699b840633499483,0x2cedc8783a1d04b98a43,0x46814d43b9f220013300],[0x2acd46a8e58e56c,0xaffad52fe6988105fa60,0x7774fcb10b27e34f4bcf,0xa78c5f36b36f14e151d6,0x3ca7d5236537a1762925,0xe4492ca327fad23c28a1,0xbcf5674165ca5aa4ce01,0x78f7b08e34b7a59d3418,0x1235dd49fc523a9664ba,0x8ee0cf9292afcb20d29b,0x65f221c13c50f2ea0130,0xf532071649a42de82b73,0x4e1da7ed53424a61b63b,0x7df23f3fa9a7e72484d4,0x713b61671c7e48004300],[0x1be775a461401284c53,0x64ec35c20b4ac3a813cc,0x93580fbf370393c8fcf3,0xc5739ca978baf5045016,0x83bd2b55bbaed866ef73,0xf96646d43bead836202b,0xd2dc6527c664e77d76e5,0x6a5999cc849d5af535de,0x30a624f795ca08e6599c,0x5fbb61f1560f5f1261b3,0xae49526d9b6ed96f9673,0x693b71f24e20b3a79829,0xecd364196e7178fab0d4,0xb2bc0f9b5ca9aea36a0a,0x4f579ac53399fa100400],[0xaa403259c3d445b6ac,0x9ebff93e47522c8bdeb1,0x3e29d1a5ca612aeb43b7,0x2810dbbe9583e6e404c4,0x3852875cdd6779790fa4,0xff6ca0184450bbbc0f1f,0x879261d40e904eaf5625,0x1c2bcf456de88591da59,0x59994bf53b77a1b0849d,0x78173cb09235a2f4a8fe,0x632cc236eefb08cca7ec,0xc45e6375d11bf3449134,0x3c2d3c54e0baf2454d67,0xd473ea1b2af72bd1bc9c,0x41bb98dd801bfed10400],[0xa932063517000d517,0x780fa47587f79b1d62b2,0xa12e143b08772186f006,0xbc84f474523e565b8f88,0x8440d04434eaa93c0fe,0xbb483b5aef31e688915a,0x2551a0b5db1c3111857b,0x52c030f3f9bf004f63b6,0xc30f61192db1f4089d63,0x6c96b14c6bd061c5f478,0xca1c657ebf3346fd138c,0x5b6f3da3fe3e537918bf,0xf1cfaea140090349255,0x8bb5d1d87d551cd7af55,0x4219af02dc3649120400],[0x2575832d1a4b0c3a52,0x8fd9cd47198e948645fa,0x86616816883011fde29b,0xa4ce432986909f0e53f9,0x47fc408d787d38005d8e,0xe92adac0e2a9d6a0144,0x73cd0d315594623b7d72,0x10a27fdaf24585da0280,0xf930406553c8758df243,0xc31f773eaee3f8241884,0x8c4c7955fbe8cafb15fa,0x34452f2caa29ffeee34,0xce02cdf1ecbeaeb85d,0xd80e5178f25c526f0881,0xea2a9dd3fd2f74001400],[0x176a3d66890ad1a2,0x9b70d59085b0881dffe,0x233cd9397c9fd65dcf71,0x953949873e00996700c3,0x5602688496a925a1316e,0x72aa53788b8fa4b51dac,0xeb5b4fb24cad9deddbf,0x5e6c38fb802f9a427d4a,0x2d9a85fcfa8cd819aabd,0xa2fc56058d69199ef726,0x96a20ce247dddf236227,0x96c782e808307b1812b9,0xf87d920c21f54c5035c,0xe8842843c25734351f0b,0x3fe488d87342e0111400],[0xd2f28f860936bb7,0x73b6c9df5c9ca6b4949a,0xfbec4ab6f7ad94c92fa3,0xe875aaf184f481469b52,0xa2f79a5d91d2537eafb5,0x9f252305bfe0c3eb26d7,0x4b1a7bbd85445ad594ad,0x69036b006d097d8eb32b,0x2d86bb02e6fb18b35a3e,0x8e7268e945bafa2d559e,0x85da2f8997e767f8f56a,0xbacdf6c0cc2dac018aad,0x42c6bd15215d2e4e59f2,0x761b388f0ef20bc8f3e3,0x32585f88f05c20002400],[0xa1c12ba2a53229,0xc67ddd4d15e9e9397c86,0xd4891031746d7ab9e50b,0xafde1f37142beb2ce3d,0x5599a33388ef217a6152,0x6c16ae91e8e6f2bd63ba,0xffdd0cd00f29a035b393,0xc6c6639e2c85a19e4190,0x464d9da060b18a52cdcc,0xf3233713a17280fc1348,0xe391d05e17855f7974b8,0x7d37d389162ab6f5f923,0xb0f382b0faadd9cdb0d6,0x427c9f1ff67c2e60d49b,0x5155ea911969c0000500],[0x7d,0x442b391ba324ec66581c,0x2953cc81a4d8fd36445f,0x872b72301427f5db0fbc,0x2fa241ba3bec8dccb511,0xeb513100b34073184c7e,0xfd745488924def57a971,0xc275be20c3a657df2d35,0x7471a7d361fa4148987b,0x2cd9e19ad8d27bfe8895,0x9efef1de03cf1885bd51,0x31e93a66590b47c11a0e,0xf6e8886a296bf67325f1,0x89934048e9dd8f3c4d3e,0x850b9747bfaf2a546f59,0x6ba7783866113c000010],[0x6,0x754e5912653a41b04a88,0xf622a7309591e1252e0f,0x9b6ef06c368469fb19ac,0xd0d3e6c2641572c145a7,0xe1a115c3e17458dc7af3,0x8664031af4ca0ad41a35,0xa39d03e50f13ac6e36b3,0xc0b84546ddd1b7d94b2d,0x912c98de1247b3a64379,0x6945e2993ea2ed1362f7,0x919114dd310eac750f45,0xf3fad3164c685965ca8f,0x8c9a8154d5c8910d28d1,0x90178432fe7a891d2341,0x15c1c0f35f2604010010],[0x9d,0xdf3120dd5ea00aacdab9,0x302d63fd192cee1d4d9e,0xadc2b557b5eeedca0fcf,0xa400c591acfecaf4f084,0x6a9d34482b4861c92423,0xa77bb695ef23e4cb50,0x47e4d445b28f31d4274f,0x6c89f6e6d22c3bd6fdc5,0x8eafcf4e8919172062bf,0x6716ff8b6525771cb2f3,0x4ad2139db0cca452416e,0x4c496f48688856508f99,0x371ebc5f34b01fbaf78,0x12076659700f5cb28d5a,0xfa29a0918d1ec4920010],[0x5f,0xeef4340f1bb6047ab63b,0x3f637c69b62d3c62e8b5,0x90238c5b3e03cbe5f830,0x99fa7f11f9f909031005,0xc7a5016d0080a612857f,0xdb520e745735fb21b377,0xda524b3639e582b16765,0x51daade4ac9c4a297e8a,0xb4bbafc5935e19687a6c,0xa18b77ce0a664c064fa2,0x54869c985d40678e8fd1,0xa75a1338a6754f56be55,0xf2e181699e4f6b1e644c,0x188375439b898c06c942,0x7bda583b1ba21d930010],[0x16,0xf0342c7e4fbcf7cd4fb0,0xd9151231a67133f0e410,0x4b8a2b09b516d794b886,0x55bc5e0e1fe1310736fd,0x83eb49207b06dbd49b8d,0x598551f1092127b730c4,0x49af9cea3436eee4d633,0x5bed48f033cade4be6df,0xaf32c170f1175044890b,0x89e199be44ed39677ebd,0xbc14e8f2825ffe0fa5af,0x1323dfc70596346f0dcb,0x5609e98dbecbba2056f3,0x215802c39c7bea0d870f,0xfa9f29ea8b0c8cd40010],[0x2,0x93e15c6782c7b23219d1,0xffabd1e54233ae42505c,0xe6740b4ff13c0efda6f3,0x97c0e26a0db4219c9f4a,0xd10a7ba569defe00d719,0x2641673376bf5e41976a,0x20be7573f3c269896a4f,0x4577ac61e1d60aacb145,0xfe3729972bfc3b34fe65,0xf975fd77027cc675ccab,0x140a2fdb5dc1c090da53,0xaeae54f40889f1817d74,0xbd2f3e62763417479888,0x35eecad23a9d2f504db3,0x6425fbbf645364b50010],[0x1ec1d2923f1c766c93aa,0xe185d1155997ee1eaed0,0x46cca41cd81b00d0d07a,0x82eb2ea2bae75d6b371d,0x6337c72909348e511c68,0x550acb6154ccfeb494ae,0x148a2334d311ab4c3428,0xb6f839c3e2ccd77d7b1c,0xdc9bd5456078a21db5c8,0x6f972ee927e28f23f3e5,0xcac64abf69084b6b6033,0x2a483f59fd0edb00b58a,0x7494de5d9fde267d90ef,0x7835256049ed1f8b3e34,0xbd8676d458147a360010],[0x261e26d93852afe1cf,0xd19fde059ed893c41884,0x4af19bb1155b537385c7,0x2b55c6aab5de2d660b51,0x17b69e14453096b5b8e8,0xc771a0944440f2e30da0,0x4d1940507c32e7301fce,0x8fe849946e552f5e66,0x9212123b27487cbf6e41,0x88ba7bb810111a1a5ba2,0x10a1b56fecaeeb4a5769,0x26370b515f8a10c7ad06,0x2bdab6dcf287694adb64,0x6eb4e73734606b7ee001,0xb501ed76b4fee9970010],[0xc1fa15717609524,0x1f5a303704dd1276316b,0xd1bffab1d62480e67f0a,0xbff5525ee921fdcfa06c,0xfd0310f515d68f81935f,0x80fd6e48c044133c8fbe,0xa069f6feee773a97a505,0xe0fe7eab8483488a55e,0xfe8a44f6d888474a47e0,0x6e1c19443e4fbdedd97b,0xfdfa15959414e4fcb72f,0xb882d9e342726878c57c,0x31192d372a6dc9ad17a9,0xed41f7fc10ed99dbd124,0x609dc3c4d22cc0180010],[0x355,0x324888ce0e046ee6a048,0x571eb3ac6f48c06bad67,0xbafd930c2726d83024d5,0x1ef65bd8caef3e889eb6,0x5c4b56dd886c236ee70c,0x11654a7cb740af873e6e,0xaffb0f910b09041ef863,0xa66d462ede5e1cb8a610,0xc0ea319dedefc514dd7f,0x1ff8baa5a93c443fe39c,0x529493301061b15c9e85,0xe4ee54c4e1e8dae94095,0x8297a052096ceaa74ab2,0x2b0761d20e315e4b4280,0x212a5ef2664ee5001010]] ++
  [[0x259,0x35235c62337ce4e12baa,0xaf6512a4c8dd1f3face6,0x3916900363d367a1f19c,0xa834e08e8031de6de0c1,0x2c31bf745c51245a29ad,0xd11f38456191132d9689,0xe392e803b4254f4716c0,0x7b5929ae5d3c2d72b5a,0x7f24e812ec7787eab897,0xfeb54dcfc8be06b32b4,0x4d8529df56afea265337,0x382bf2b7dde8d78efd04,0xd0dc920bd318bad7091f,0x5ab3dd927d049e90fe46,0xaad782d673cd98811010],[0xc5,0x3f7de23cc3a4321b17c4,0xa2d18020417cd42cf505,0x720c3938b2870dc874fc,0xf01306eb7db0a846b033,0x5c6203005303b212ff98,0x87a515bb6bd02df4fe1c,0x2e324f5e76722af60a4d,0x1de592046c46d9206e38,0xd6b2f1c7e6d30d7e8768,0xb955947daaf6be9defd3,0x823a209f1507c8078d9b,0x8ff6c96a80ea776385a7,0x3cbcedbc06860366d194,0xb915fa4f9e6faeaf2e25,0x6546e513c3d60c21010],[0x1c,0x4e9b30dd4f448597e3c5,0x224ce0bd9713ed8a3038,0x766e6d24e7f6209fe14e,0x6a5a91956d95d1046c8d,0x62b76c7809906bbc074f,0xe24dc51838bfc7135ecc,0xd57a59187720343e85f2,0x261ab3c8a2e72e5e3700,0xde82c07411f46d33adbb,0xa561612f5c745140ce9a,0xa4534549e710abe2764d,0xc146f826d75298b94d55,0x6af010bfdcbcec8f6120,0x39938a10d8dc12d928f8,0x231520075c68f1a31010],[0x1,0x893918cfe4ca5cddc070,0xc192b4e62b2ecfc927a7,0x3eafeb3a4a7f818ebe0e,0xa3908c9c515f48c85398,0xb22af0868a87d7ca05bb,0x9a35ac5ed7694470762e,0x56e154b7b7fb2f8dd05b,0xef5df8fe832ef0ff57e5,0xfa0af138e0ef94a73c24,0x6e63646f55ddc3c4e505,0xb256b59ffa5810340945,0x2a4580eb393e1aa606d6,0x4df564e6ff3c3f7bafaf,0x3c5fced453a9da7d7945,0x2c11fef577e43be41010],[0xaec12c1e47885e797f8,0x374a5de0a6a0d6a1b596,0xc5d9d196d11ceb198bf,0x30a81acf2dc33c9e52e6,0x5b25cf6ca1c47fb8bd54,0x7f0297f3fb5eff1588da,0x7c78b1c8b5d9f090c718,0x595268c91abd88f0029e,0x2e123c23593e8b33fe43,0x3da4ae82d4b3ab134828,0xafcaeb6f2208b14a9b77,0x6fd5fea4e95ca21bedc3,0xb1b6dd267496755056a1,0xce14b2cd6c7564383a0d,0xce4ca1e3c02415e51010],[0x28b3c300fad05eb227,0x89892fd6dbf73e9da209,0x9e93cc85c8841511d78d,0x4dd3784d82fead3e5ca0,0x56a6ef4aa574b0cda50e,0x82ae7e9b63b9568be499,0x9290bbf5346ae96dfe90,0x216efbfcf02e41b398de,0xde0e928cc1b16167cd9f,0x773e7c753e6285af708d,0x2094c414de1539b1ba68,0x84a407803b61e1977b22,0x29c965daed79db6ef23d,0x90a5f5ad7b5bb703b53f,0x3b6469c3fc7c54961010],[0x9078a8b327342a1,0x6d2bf39bf30c9e3581d,0x713a9c58265d60db4bd4,0xc738cd31b87344eff439,0x5a8ea7490af5cab8f9f6,0x5fea8c078dffcecdb8ed,0xf9345b8a2abc37f1616,0xd712902d31b51a3827ba,0x349ad5d204cf70fc0b60,0x4f1e2ea75d34c1b63780,0x920de856013c38594ef8,0x8e4d6aada4d1431d2f33,0x17f2ab614dea6f1f89d4,0xb7dc79cb97e17be293f7,0x608f80fe18a280171010],[0x2e,0x7f497e8cbaf9546148d,0xe7ee1dacf1e376c5eba3,0x48bcf635ddbc71dc483c,0xe7a9c1731bae6713e987,0xe01d897555bdc0457f14,0xe75291bf7a5b3a29eb29,0x2a12a58c75bd8b09d44a,0xb1f09187bddca8b4f9e,0xb42d61eaa85a0b152cf3,0x4ff4c09fd26d509e3db8,0x3f9457dec69c0e9f8967,0x66bfd13aa375bdd79525,0x6731a27606140321a09a,0x2b1a426f09e01b359f54,0x62f4b9e086a2ee102010],[0x4e,0xe981c4f53878be0287ee,0x4288a88fcf24c17b728b,0x107be5094a557e81d8ce,0x8dde5f2dcc4a571ecc71,0x91f4d89fb2264d77552f,0x49a938075581b73fd595,0xa762821dab63b6548416,0x22babc4c8ba8d10560f5,0xa576e243fc3f8c0de284,0x870c2935791282294193,0xc7a4fdd40196d6a0efa8,0x7554e89e39db93fd9e05,0xb03fb9a0af0705d4f76f,0xc537c0ef952278443495,0x37b92fe9a02989412010],[0x1d,0xebcc9d9c3bb287078e52,0x6e8dee02825c8017780f,0x91c34d5bc6c63823c43,0xe4309eab0262e72b9a3e,0x4db035eafa24af957aa2,0x247ee15cfa0bba406b20,0x9c5b0ef0659c6f64ebb,0xbacac1b5398f1d3f28b3,0x2401fec1056f3edee836,0x3e700f4636b3df1e6447,0x6db509e9158567a7eb97,0x6951f8d4db6b1f7bfc58,0xe22addcca966f766aba8,0x5b57fc623952cbc1a10c,0x7a99d66569f8e5022010],[0x5,0xdb7fb9ef99364d0b21b8,0x3b7ca623c2afd656408f,0x884eb3d34db56e054a09,0xaf454dbcfa1010940cfb,0x1740eff47efa79313d31,0x850558ea3134510becd6,0x91659a6a9ad0c8786d87,0xa77c0f25143b3c46a66a,0x3f660cb924d80c47a7d,0x11ec9fff5cdde33f194f,0x6050eb0005e9d6660d47,0x239dfda2ba3beb852d96,0x336e8de2ac3d07dd78f4,0x9aaddeb4d7ac41ea6c53,0x30ceca898e5b5c232010],[0x78ef3527d341be0ad79c,0xfaf2b6649b5d544ac2c7,0x753111c55714ad85d844,0x63d1c9af06b21b01b6fe,0x8e379deb202bf2256ab7,0xb74bce5fd5951811d93d,0x735285e90f15463c82d,0xe9ba6072e78eccba781d,0xb0d2a2feeba7bd88fb28,0x3e6835ab9b5777d4c7dc,0x280f1d5398ba0c0329ea,0x420bf09791c84833336f,0x498d470a863b1bb54882,0x791065a5d2822d65c28d,0x731786ad3f37d7e42010],[0x29d08afa4d9ded25295,0xd8ec257acb46706b40b0,0xc6a7fab1c6d5a4c0ed64,0x484b1d8d0680f126c123,0x2e0dae039de6551d319b,0xa0d17f9c1ee7962e63b8,0x20d3b396c286c05790bb,0x16d68588b8f3d2734a26,0x6f61fc2f23439420bb95,0xc28a7c30c40ab7baf165,0x651cbb68a899411e66f7,0xc94184865fac81d1b8d4,0xf0ee9f48ffdf3401faab,0x638b232ec9de62f2c153,0xd921934da45614052010],[0x24e60c7cd11588e,0xa62afdf34c6ea5f47ea6,0xab09c38cf27e77441e45,0x132ff5a9519a6dd0af8e,0x5a96369a74232485c20e,0xe246be6694c4ebb3b8e1,0x8383ec8e89081b337862,0xfb582a53fc963cea2140,0x64612be8d7bd28dfc6d4,0xfd9a139aafb0cb9c6d59,0x779cc403eab80f84321f,0xd3b8f9383c0bb82fb4f6,0x1ba0911c5a2b544219f9,0x3f25f29b6d2406e4d4be,0xd00715d94d0a80062010],[0xd56654f03a10a637c5de,0x87a8ff66ef4443a7de0d,0x10938cc39d6d37675e3b,0x6f3c176b60fc71b2da05,0x582da140b08106338733,0xcfd4eca3515becc474fc,0x9b534e946ae287043019,0x5b1f3afe4490f26c6520,0x7d16dd23b2441bba66ec,0x54c15c4bb1531625a93,0x3ebddff560d8275c8138,0x8d1b8519027dc1b658d1,0x36604b8c68ee916ac7a7,0x936c0c4bdbad10bfb4e0,0x30da560878a110103010],[0x3,0xf8170caa7662f5140472,0x54e4de0a999719798137,0xb1111e379a583b5a520,0x8af82b7fc3ffb261f97f,0xb680bfdb26e5e759cafd,0xb7925705da75d172f83b,0x3dec4363ba166cc39f76,0xa028bcb8d32f5c85e1ac,0x433ccbcd4ebb01487a8a,0x6817b3680897334462f4,0xbbfe7d14461c493a20e,0x75957ff88175007d501a,0xcd5b904634fecb98d9c9,0xb4a096bdf4565b680dbf,0x9a3654cbd5fd1de13010],[0x3,0x20cbe720ad7fcbaeb6ae,0xa36c8e332cdb87ee3ef8,0xf58639161132c5937bfa,0x7bab1cd9141bf26684ac,0x8605e56bf376645d29f9,0x5c831c9c7192388a9345,0xa8f3551274661b2845cc,0xb6276f838577cf5c7d30,0x286a2f15579bd95e82e,0x3ffed48490b164734031,0x7184652024e6df5f8d65,0x969290329322edebd083,0xc7d8a20dfedea29993b,0x19097301a80e779a3608,0x955ec282ce2811423010],[0x52760e8dc19d31ebc0df,0x56befa85267736c1c027,0x7a3728f35e265f34d02e,0xa5b8ee96bfd814fbc9bd,0x9319ea930b0d12c876b5,0xea2b49fe7c7857099875,0xdafa2571dd773dfa9cc6,0x7b4768aa60879a91612f,0x5b839bec351a85aee5d2,0x8ffccb5670a9554440ad,0x4f4ee127f082fb16144,0xec79c3a298d30e1ed327,0xa50d3c0fc6bf103d362a,0x45cf21478fe5297ac436,0x390c1e0e1acb2ba33010],[0x1ede32e327f4e5a0ec8,0x84cc6da3b5e94cf9834c,0x91fb774ffc81b46e4ac3,0x3631aae87b9fbc7627e9,0x2a9f7e86817034ad9b83,0x8c845ab875a1801e7f84,0xd6ae11740fed759f192,0xa894888aa4d28c3f0d91,0xe99d3bf7b08b43580c79,0x8f00c02e1f21f94e80be,0xa9fe52a43fa89a50cb8b,0x308e7fb4c4fd933e0f1f,0xc69e6fd84174d84f2f2b,0x621aaf6250a1dfa3852c,0x3a3a0286f8acf8043010],[0x1ce493f7d28bd4a,0x9b8bb6d9d4ac2661bbce,0xea308f6714dbf06cffee,0xaa584bb6f894b5172da2,0x890c765715b8728b0acc,0x6c3851bbce7c05cf086b,0xee139d426c14058f601c,0xa67bfb2baa0902f77bd4,0x125611b112e65ba0fc73,0x8a6c40a799d0488cb292,0x6dc13ef30917f4be6916,0x712fe758bae2c00b1d9a,0xd5efbed01ca099a8603f,0x36b10b83a47ea0a72b75,0x7f8a8fba3230e0053010],[0x1,0xb82ac914814a7e39a5c8,0xf23ab0a02ddd87defec4,0x2dc99a7358130ccf3bd8,0x4debb7038448d369abe7,0xed98df2a54f25acd1176,0xd31ba82042dbfcafaa76,0x3fb800cdb06b59a29367,0x785399c0a35aa3e5ff69,0x71727c2d0acc9945b0b6,0xf5a1bb5c5bbe6bf4b78c,0x7e7be02d4c526e9ea4fa,0x5cfb0c563cb8a4606abe,0x997a080c886197787644,0xd80369e5f94df5c68bd9,0x80491efb75b461704010],[0x6ca96d2e941683335dc6,0x566499f3aea1caf3a47a,0x6fe774092a90e287ee65,0x52adc13a75e9ee27caa2,0x697665aa644b60a21b15,0xf0b7268a7cbc222d49d8,0x3354ef28c1a904ce408b,0xa737a97ec04aa902496e,0x7f2ef9ad0cd2f519691,0x67d5f50384d275c0c32d,0x96d9c86867f2395ba7f7,0x1fb158fec55c4c6896ba,0x31b4ab9e0c0087f06c7c,0x120ce7c8bf1383d07079,0x12332784c8db1d414010],[0x196486cf44e5e2448276,0x7966374263d5032475b9,0xd2da8c40c79ff1845e17,0x924c00d35643f7f8807b,0xdf5d9267d52b5ff3aa6c,0xcadb37bbb0aea8893995,0x9753922e62020e64398d,0xd2b7b2fd2e85ad5402cd,0x5b98bb4da63922ce751,0x72d7509653f758f6c0c7,0x30d583f3bb8494b00880,0x2ecd9bf0c7a50db9cdff,0xbcbe4cb41aa096e410ca,0x62361c228ac5c660168,0xb4b8f011f494a1824010],[0x182fb2fe48881055045,0x7c7878ab799b97bdaf97,0x5faaa95e7d02e49b8385,0x478db41572115be35c72,0xed8c9a10245374826abd,0xfb3b1daaea3b8df2c19b,0x7e1d884acacad9f71013,0x8ea8aa138d5f28595f70,0xf2da65d37a4b4f4cb151,0x57359f3b223cb26c42b5,0x354cd74d1fb14ba32fe,0xabaf51ae9423ab515e01,0x17c65e3a7ad8ed0491c5,0xd89376585a4247ad5825,0x220161d9b4593d034010],[0x7b6a8911f88c1,0xbfd024c3f2286ebcff35,0x3a3f94a82ff1d23d4e06,0x9bbc564df9b48c511ed2,0x4e4b70400e2475576835,0x9a7b31c7efbb5a3abe58,0x2427bd4bd76b3a61702a,0xf359c0ca1aae5c6017ef,0x5a3a6c06c9519e0fe1ef,0x3193035ce0313356b323,0xc350700c81e89f22163e,0x1fa83551712ada77ffb6,0xd6b2dce629eed51ddbb0,0x3ecc1ee2349123540958,0x7bb3c427850800044010],[0x34a785f63149ec6589df,0xf52194cbdcc5fcbefbb3,0xbcd917e6c0c3570a89d0,0x5a6dfe110f8f3617bb27,0xebfcf3d4039a2b272b39,0xf10a6a7a2ce34c4d8d67,0xd06a3c862695242c07a3,0xbfd472c43b8e9c35e7f4,0x86bfd0d8ba883b303164,0xe472fb4a14ff5c130b27,0x6c12f2167bf4e30d134a,0x3296b771c26857070163,0xec58d56fa590ae3867ab,0x573627665fca99095dc2,0xe7bf4e8f0e0f79905010],[0x60bb4b2ecfdc299f5db,0x44714ca36b403b2ab3,0x8258088975ba8eb415dc,0xb7e02662c4c39985bbc0,0xeaa39ebcd490beb63e95,0x610ce4d81cf4c21c5555,0xfb599bfd871965769c52,0xd9f4efbe9d6c8c98925a,0xf46d8c31922f56b5e711,0xb610a6fc150df6b569e7,0xc1effcbb87828b21c89,0xd181e1b64be52b195f96,0x75bc6ecc88fa80c9f4a1,0x5c5a99e5d6c5b5ff1cd1,0xf70f0e7fe70d85115010],[0x3bc9c2353a328cc9d1,0xc418614a8e444e59d406,0xba5153d5f38186e2fafc,0xec4dd17a4454d2ff300d,0xffaee0980ed5ca1e9bbe,0x7ca164d80dcf9bfcc6c7,0x81602a2aebc15172baee,0x91c2e167ddc8bb8f809,0x8fd89433eabd8366c21b,0x22c8c19c8c21fe8fbd57,0xe72980b39e5b14c0f20e,0x20fd354b7315a6a6908d,0xb7056e9d4620cd92fcf,0x30608d11ac201614b69e,0xaf00564b6afe6d025010],[0x3078534451efccd44ff,0x59edd86b247d20973c8f,0xaa8a9e16dc7adab88153,0x9cb3bc14216c865d9194,0xae4158804f185be053e6,0x5992dac7573c8f1e3b7f,0xdfe329679fc7a6b6c18a,0x4f51feb59c98bbee3208,0x699eed8707f8b34b76c4,0xb761ac5ab8f3cdd036d5,0x8feee5f35c8b2fb0aede,0xb3534df52a7186da8864,0x82115c7f4f0719c7103d,0xf2833c62c401fa8c18b3,0x12ddd42ea68e8e106010],[0x535ea3f9c178e1022c,0x1f52c98c9717b754b232,0x7f3192b87659cf8bf5ce,0x24dc1c539544ca88f987,0x5ec972109897a6c2da4d,0xaf0d7d24c97e1e747dda,0x48bf5a4a6b502fcb0d1c,0x4b1722140cbb2424a298,0xaaf63a54ff5b2efec69,0xaf22a83fd85ab04753b,0x94571ef89554226240b3,0x8b47c11fb7bac41bb222,0x74600dfebdad620f8d18,0x63d8965c0ac4724e37e2,0x41c4155f447e2a116010],[0x155cc27888b16466c6,0x373e4ee61e0b8f225259,0x723655e86a1abfc6bfc5,0x3e3033f46d86386ac84e,0x40d981832875ef87dcf8,0xa2f1aaca28e6877e755e,0x77eac1c643138679d4f7,0xafba083b98325f4fc838,0xed4aaa86150aad816452,0xcbd729130c3493309e95,0xd621916d712c9bddb3f7,0xc8d8bc703cf924305d24,0xac73efdad560d6ce5e41,0xb654ca537d3168b5d972,0x7a4983c8c27120107010],[0x4,0x6e27303cee591831a4b3,0x9b3ef3231563f7e2854c,0x939a8271c1617cc1f752,0xf2c115034873b9c12618,0xb7830d5f1bde7b7494d9,0xd3eb71bfe7f8c65c3cb9,0xadc9bec1b5f92adfa3a7,0xf5ec3d4f5d9d0c7150a0,0x35d12792cfcf7e5ab89d,0x4ad44ea97ba6097c71df,0xc8f9dd9ba2c46e61fcf9,0x3a1f585ae9935e863d20,0xcac31ed53847a05ddcd3,0x6aedee480bfa2ab1d99e,0xca36804e9471b8000110]] ++
  [[0x4,0x4515ed9cb4cc1e934096,0xfeb22e7eb8f70f00482a,0xbe3411982a90611cc8d9,0x4833d992c2d842ab609e,0x79024de744ee97ba571a,0x1efcf6b132d4fdd2ab65,0x76e60d31e00add6a75f3,0xe8f55ff93d684ba3adfa,0xbb4cccd3332a33d8c97e,0xf590942a249b058b2558,0x283d84291d9efab61030,0x6d1d7eda768ac8d50ccf,0xceed19ee08883d3683c,0x34bb05525d733f61fe51,0xcec5c90e715037810110],[0x9e4031c95a506ac34021,0xdcf56178b6699f0d8819,0x3c06f84de35ddb7ab607,0x2c76d0c63c6ce8ae852,0x87ad31a760b285e3ea63,0x782375d5e5fe5c31408a,0x4c35009024063cdb5277,0x8a31bbfbcb2b6bf7a5f1,0x7fc2790b4beed95908e8,0xfa61d48e8fa7e2da1161,0x18f145f703e893ce3989,0x236e256b00c6112124ed,0x9af67f5f832a206c9f18,0xf7f9ba375567c45dc2a9,0x372991845e6770020110],[0x27e7a82a0bad9f813e2c,0x7716b4ebae77c9e30020,0xac734769789db2f6900e,0x53c2436b225b58b2b28d,0xde3df9adcb51061605a4,0x7dfbd74b4bbd08089373,0xc4c963c51a02928e1c89,0x7fe949ccce5830f79982,0x38993d39825f555f2afd,0x5393694317620d4220b0,0x3fff3ff4a00cdcbc89b5,0xb27dca361d96731ce6bb,0xb39963b1e90549eeb20f,0x7d46b44a4fb1df270fdd,0x243b67840cd024630110],[0x71882dfb6ef302949ec,0x803f479a28f6f3ff047c,0x1b013601b6dd60800f3d,0x935bc23fd700cdec94ea,0x25bb13b49554e906bc30,0x40bcf48aac33e06a2b4f,0x7bda3ee923080b79b0d8,0x917f02dcda059f778638,0xd4aa7bfafb6d748fdf95,0xef1f46e268d927585140,0xa026ccdf2848e493afca,0x48fc13e2d3cdc27c3b8f,0x4c39a976ce4ca2dc7dd7,0xc4d3214e6b9998a4ff57,0xfea525f4ea48d3240110],[0x33b83eff3e874ddf3b,0x49c9ec19f8cbecb8f864,0xb459f44985c7ceb84afe,0x3877ead719bc48440935,0xbafbda87b61608a90d49,0xec09bb1ccba553502fc2,0x39abb71367aa9d98cd76,0x3a68b831dfaf7c7d1c0,0x130d1652f07744e60d08,0xc5f96f2eaae5f09ef334,0xdaf565b880c99dac72bf,0xbc567a9066c2d38d6a30,0xfbb742df51b2655fccde,0xbb4bd5f472b6b0217b50,0x875fdfb104ff96850110],[0xc0e7bcc8b7dc08,0x7530c0b9a97f62358039,0xb3862b0f35557a29db1b,0x3b8f817d46aa4f28d086,0xc2c6976a9bc1d09727ff,0x61b0308adaa1a10e5d52,0xc86d18a65cc9ceeacb74,0x72a754370f81d1a09edc,0xcf7a77b35ce292304035,0x5e7791682c1ccc8da88a,0x1acf8b60cd7f63855258,0x5f1199db0c177037bee0,0x7b36de74c4372d1ccf61,0x1b70c9cb94348e9ea57,0x2f71d847a01540060110],[0x9,0x5db437ceb8a13d444bf6,0x583821b9876eaa06c141,0x12aca7a805e93d2e891a,0xcb35718d7106ce73fb30,0xa8a7b56fd99cd21cc47f,0x86bd3f0a34a063391fe,0x76a66ac4b6fc1041fc01,0x31e79b91bb0bc234b250,0x4b98cab7d2543e901de2,0x143753d8775b507f415f,0x628709ed4e836c292f31,0x1831ef7199d8e0bc5324,0x8920c6e5f3d5fbba88b0,0x3a02d751a752831d89ba,0x22b6ed186fff9e801110],[0x49a94dec77f3cdce214e,0xae059acd1730e55cc226,0xee261a2b02237be1257e,0x3aba05127127ca34dd1b,0x8fcb150d04b9d20cee80,0x7415a3813367b73d51a6,0xa8146ab879b339ff982e,0xb4535a3ad5536d0deb40,0x809b953aebb1c49d741f,0x693bde73d3a2ea761c15,0x538b887ee6329522b5e,0xd86f17e41e4d741b70b3,0xff7542917bee6d8132b9,0x7629f8d8ac447bf436f8,0xda2cce94718dbb611110],[0x2fb6787aed80c6ba765f,0xbb9d8600c94946b3e795,0x6b677fc210d46e3cba0a,0x6f655e6baa1c0a288eb0,0xcfe866b9bd59f1ea18d2,0x2ad50d88b755d026a4f1,0x9efc554bd4d8397b151f,0x4db4b06e02fcdbd80f4d,0xc529e590d0d47ab06923,0x4a0350425ad44d44a9f9,0x130cd47554aec1a096ca,0xa8879dbd5cea5e760c5,0xb1d33da4396c82e90f7f,0xabdab21f46751358d91e,0xafad02f2bdda421110],[0xaaf097c3931a680fa67,0xc1eda9d6b55a7eb7d308,0xe0d6e0defed4db012e7,0xab5d3f0e84c311980923,0x68b0ee12d3e95efcb319,0x5115fe13c969048952bd,0x837da509cef840e65f97,0x3596959118046a61a7cb,0xe7a14747dadedaa701f8,0x246c1c91fa4c764ffcbb,0xc9e6db46d835b3eac00e,0xf90db0fa8c2c296d5c,0xaafc22205d5610d3e4b5,0x2e7379fc6827266a7924,0x9aef799b6c5cbed31110],[0x9518f73cd722122377,0x8440b32221f900f07f1c,0x26c7b60fba5b78364085,0x90936eee2f085d0cce71,0xb8d9df47884331384f05,0x901d1c9ac312b8ac181b,0xf40babd7893bb62fab62,0x72c0ce658197eaef860b,0x47904162e6028013213f,0xf994b9b0da54ca78095e,0x99e1a84a6d3a62725816,0x6cddff6a6dfb98fb6860,0xe16f14a9442f9d8a46f7,0x959727e5504eadb67586,0x30f302fb6fe8f2141110],[0x219371e544c0acb,0x3a97000f78a85a9bfc08,0xa42d493c58bdf72b2d39,0xb5e848c426b92a2b70fc,0xc042b4f442112ad07356,0xd66541b8fb08fe18a674,0x20585af074b4807f2227,0xbb807c10c7a463234397,0x48b80bb791ca2ecc37ef,0x341566a3da3cf08def44,0xf55550e1b6887b8d6a54,0x177e084917341fe69586,0xe0a34ef7417a19c39f46,0x2932573cdd5abb17b7d,0x5561858e6cdd20151110],[0x1,0xafec374728a14e4bcd87,0xde4395e462d982842ecd,0xebb4b8ba6afa62173cc9,0xd541e6491b00ba4842cf,0xac0ac2d5695c29a5682c,0x2c2c0feb071aa55e40be,0x335c5cd45d2275007a34,0x78b17a59f3e623f71c37,0x5fa6210f683b1f1d9190,0xca912437115815b9affe,0x3ded15e6de065da3abc8,0x137316a6f8a8d638fe97,0x65f14445a0146baf34b4,0x3c375f3b01f145b119f5,0x8b06d91740e58de02110],[0x8bd6911f665bd3b9e4af,0xf14252f9a436c76adc3c,0xc89057d888e1503abb4c,0xe9faabab26164463d986,0x28e959fb4d57ce6d1f2b,0x4bdac4c74dc41900e1d9,0xaf76a773585d93d628c6,0xdcc58ac47b258fa2ef7c,0xee283893ff60ef539f4d,0x1be9dcb8fd16c347ab3e,0xc2434274b1987bd29488,0x2a200fb6720ff9b3d116,0xe9d171297ef58d188fa8,0xd412eed31ee4624fe189,0xb29c97f1579392a12110],[0xabf8a26731855a74689,0x34263664a8df32b7862e,0xd3cbc9d3261bedcd00f9,0x75626184f412b8ac9428,0x1a6371f85d0338ddd08e,0xa6ff063fa08695823683,0x746161e6eabcdd85c3c2,0xde807d89184e48df270c,0xb3bb15c84d7db80bebfa,0xf85d562a307b9ec53f6,0xf68682c0cdac6d74cd3d,0xf77f9e9065a0b232b5a7,0xd74788ff7015a4299165,0x99b3ee7504130e74b283,0x987be50dc6631c622110],[0x68c41f6ec2bbf1e07,0xef80775dc77eb73be214,0x9fe8887c5318c236c6ab,0x538ddd5e5b6e8f8551b3,0x8211dc633e941224aff7,0x7825e4246de07c82dde2,0xe9a6a96e30a61e580ea,0xd206245acfa9b698eaed,0x257c1d8d58779bec5652,0x7bd7ab2cc99c8658b5de,0x598b4534bf67b2739466,0xe3f938f495f92254ef46,0xb58105bd8dbf4a97096a,0x95e33355555ff3153d2,0x7be8b7054355e8032110],[0x1348b483c21b4bc,0xcf8e50135e7017f68085,0x1a245bddb6cdbc948924,0x32ae7cb5ed8df250ec69,0xa98e26962123a3a65ecb,0xea4ffae14f541d09609a,0x3b0cb5456e6611d9e7cc,0xc1d71800788cc2606c32,0x7a42bbac1b496752b5d4,0x1774d97581cad94d0909,0xdd1a5549b62c247c58e9,0xb36fcc3827fa4264d634,0x541ec6dee9f23e9e20da,0xc79073b16a1428fcd324,0x316c7b32ca2e0042110],[0x24eb7a360205c112852e,0x58a02bd8bf0e3df13a3c,0xfbac06e6d6728de4004a,0xc3961128956cfb208784,0xdd2224e9e1c042b205a8,0xf37bb79679e22923ff31,0x3b7048493e111c76a910,0x918a4d44e8b2e6e23462,0x852965bdd00ffb06f2fc,0xc3e1623fe24bc42890da,0x413ae0a0177c5084e4a0,0x571a90a146158cabfde3,0xa2a5e5570ccdcc6281b6,0x5b9e54bcd0ed69d6b7f3,0x6ad5fc350da2d0a03110],[0x6e1da69e61242fa5f5c,0x5f873e2a05d38642ca01,0xca74417da633f4244062,0xa0274b2438874bccefca,0x7b173c10334f2d1f8f94,0xd22ee1a8fef0f0b61757,0x40202f1c299bccf7712,0xee46aae38820cc91e481,0xc7e5ad621e4b0c537553,0x8629ccea0b02eed317df,0xab3c5d9a91d0edb9d64,0xff3f535afb01db5bdcb1,0xb2f514aaa3f8e14b871f,0xb44552eb026ccc40b37a,0xa12aaf6e0b4c4c613110],[0x114e98329d391321aa,0xb4301d0c78a50a8ff12d,0x6a6170e8173454ec2e5c,0xc9b25992b4dda40570e6,0x486a4cb147284505c79e,0x640714cb5870d844c0a1,0xa1fcc50e8d77893c7d9c,0xd222f02afdf1342f680f,0xb90254df0624f63be7a4,0x19830144deb20f683dfc,0x99fb005b360ac61273a6,0x1fc79954d62f1835ea9b,0xb7e7334abb9e13dd087c,0x95073f18a13c29b1b136,0xf4d0ffe75a0ad0123110],[0x1370bf12b468d6,0x2d1367e0e285d469c35,0xa4ad7281fe8525033995,0x156383e7821568a1167f,0x413e4a1263ad6661e7e7,0x9a3ca44513788236de9c,0x3bfdb0451f267d4cb1ee,0x2f359359efb809f99956,0xd0996411a0fff4bd0e5,0x8d60bc6187199d29a123,0x7c49b8c794f4c792c87f,0x269626d50b53fe0dbe3c,0x4b4b224c857d4861af50,0x96803bbd4748889eb29f,0x53ed4d6e547de0133110],[0x4627985a9e1f0f611a1,0xdd2d33598a3187a9443a,0x5b7b656a63a94f80e9b8,0x5162936af7322fff4442,0x3f3f40f6768043f0e75a,0x704c822a07e9076ba8ff,0x5468e9bcb8a83c768e1,0xcfeff1169bacac3830a3,0x2e1edf911cea3446bdd9,0x7700300481bc9f90898,0xfcf221bbe7c68a648e8a,0x9e38b7d0ee96a8cda64d,0x50f0a2fdcd64ca0d9f1f,0x8b361b27f23956ae23b7,0x402ff3bc74b9e6c04110],[0x294c691729f9b66a99,0x5aefc9ebdf081b166e47,0xc1ade0de2dc0b6ba81b8,0xad9f65d6d90fff49151b,0x8d7a67c77c3812585c86,0xaf939aec42d84b6a4201,0xcce24b9e7f81ae1105ef,0x727bc66b61087d69a2f1,0x5cf4f45f1e4d07c0b83b,0xc57b27162ea346121689,0xce1029d79a23d9e11f46,0xbff834b5293aa2b5d749,0x5252bc5d5c33af25c449,0x4acd6681a2045fa6431f,0x69b961e9dae96b014110],[0x241179629b2b36137e,0xe77973acfd0c06ce2e34,0x7638ed9948b6ad865645,0xda44bc5b5820d4447024,0xe17956e8c3d638e5ebd2,0x56ae0ee3afa9b9ca4541,0x921c3444d172361802cc,0x988c5cd575af9917773,0x49345a340c50206ac049,0x8c458f2571f74d41d3dd,0x98cb1451d0eb0d3a0810,0x5f53ebb847cad25e58a6,0x2c172d55b4cdea7ad7fc,0x77d09bc5838e379b68b9,0x1b6fbcaab5686c005110],[0xb12f41b43f360c7e1d9,0x84c746d69ca78c5cfad7,0xcce18e0bc10dd53f08ca,0x9ad1a8866fef992d40bb,0xfe99872b04a2471cf8a7,0x1a0ff8dd41424e7eefa4,0x6d209c1b403c54bd8f7,0x89df5bea215095afe741,0x1b98a387dd0a16907fa1,0x8f815edcf193667f225f,0xedf03b8fad49c86f7b0,0xa4ae4e2e8a7f2bedf2c7,0x7253d6ef530698104f84,0xe78ee55facc43a6cc78f,0x40485c2af5664b000210],[0x1a27a63fdad826f85297,0xd7fd9a9b31f0350e89fe,0x77aa7353361b7118d1cd,0x9855f1b6e59541634395,0xb0c61b24a5bb06f6b2e,0xecedb1a6419a37d7f476,0xeaaad6a95a757761fdd8,0xb6ccb510b3304e13bce6,0xe9d22ebe1f2f7d5c8933,0x839f1009366cd8b85af5,0xc8019b5d2f3d7ff513d6,0xdc7681f56a0116127824,0x1cc99179fb03ebc50e53,0x6a49efbc3876b22e2dfb,0xcd47d8d05c1863a10210],[0x36282c808bae78f1d06,0xa39eba46b3057f0c5148,0xd353ee848321b037aa10,0xafdc859db2a78efa7498,0xba139b36bdfd75f272a0,0x1c26f9b8eb32571c81f1,0x6c49b0cb693c576686f2,0xb04c90d1c13169091927,0x916ef0774d86ab7bcf8f,0x6771111e6345eb742b6b,0x20e31fc4b952f15c87e4,0xedd7c354e323c271271d,0x7654abf2a213cc822b34,0x57e8fcb87b40802d02c9,0x751a66ad73cd82e20210],[0x2ce377fb72ef9bbe12,0xf37aa211a43563ddd7f4,0x96f20f046537a77e55a3,0x451eb858e5794c2144ac,0x37d2c03f17920b97aa86,0x8ebfa38ba53bf7e15766,0xf284986daa34e4f23fe6,0x67cae35bea4a42744fd6,0x45509fa7d897a8c32102,0x51aad93e90b4f6f7344f,0x714070b4463305d873a1,0xe4362f7e71f9b97e795d,0x69c7c376e75602724f95,0x917913e467e69e00c258,0xb64c6d7461c79030210],[0x3f799da508fe5c,0x825b6a27e1779c41228d,0x995fe908d24978febb19,0x320a38621fd492fcd8ee,0xf0088630cd30fe32fbe,0xb6a3f36f90341b7ff62c,0x205d435f7ee5fb64c8b4,0x3b1d49054732057d2212,0xc9cbfd4b90cdbc025dce,0x79efa7480d5e0c945163,0x23aa813d7421766a187c,0xffb3c8736441aa5d5710,0x63e730755e23d16e5ed5,0xfe32d6bac7df8d90f833,0xacb00a52bd5360040210],[0xf9a23de9345bf09d2e1,0xfbfd6fbd292206ae65d7,0x332541abc7d0d45768b3,0xde4bb5c5d6951eba7645,0x59c23de0cadf4bc26ec8,0xa02b4a5a680c8d261356,0x8b7b40fff3bdc7e24776,0x275e191bdb4a7c0dc80f,0x80c29dc97e1ae54e6a3c,0x2a0c8ca18485ef7d737b,0x8b379b442f50a7f5df5c,0xa27fabb5dab1b52dd4dd,0x7949ed771ed4b047e6a4,0x62ae11873e19c8fb3fda,0x5b9b22b2a72d0cd01210],[0x61638b7b6325df188b,0xda8bbd67075bb00055e7,0x5a541c0599b629413271,0x8ce0fdc7b806a19bd62a,0x67c90b60a92cd1ca447b,0x12520e8310a33b8fc410,0xb1434d440a38a586dd0e,0xf8f1ec550eb0cd2a00c5,0x556e4b23046f5993b1f4,0xaf1687440d5b1ec39a5b,0x93c6a3a4998391b09052,0xf939efc1ac03eebd4988,0xdd4c906d331a8afd0cab,0x86ab20fbde1f643cbf1a,0x709f4a49a4bf5b11210],[0x1707fb02bbf77b738b,0xf0dd623537d730e9b178,0x5c91f7b459feccd9b392,0x86635cf97dcdec8c4e24,0x83758a4a79ee4f3de114,0xc24c513a7d75efd76095,0x78df0254fc6184d8b3d8,0x6f815194107b8af9c2d2,0xea2afc81ca78712a4d3e,0xcb6a5dd0a1175869d384,0x52b2fc0f0257f62712f5,0xf7a2298a300022730e24,0xcf60dd728e648e931911,0xd8753dbd8cff543555c5,0x874ce35558221d121210]] ++
  [[0x5be03ee24f1c7dae3d,0x2bc671e158ecefc58c8e,0xb0899107d85eeca6d57,0x9dbf526f398babdfa694,0xad83c0e70337585a2ffb,0x7a1c5e646161a2ba2a13,0xeeafe72f3b38add8161c,0x7e9b8c04d858b3eeabf1,0xd1b4a35d9f4c74b9551a,0x4c69f76ed607f8aca97e,0xaa57327a44ad422c423d,0xf90f675af9f98392c768,0x20e3a931547a9e39acc0,0xed11d5bbe4b16ee237d1,0x5d9d300809e642c00310],[0xa9eed4647a45d740f,0xf211fb4b0cf9726e380d,0x8600123b7c0a029aedd1,0xc09c042c24985f2afa7,0x4743e134b9b070b3a196,0x40b954af1207e772d5df,0x8b8bc7ea50a21d03a02a,0xd39e96ee321f3b7ff15b,0x75ae0eb764994073a81a,0x16c1e4bb6238d705a660,0xd3b90321dfa031a8d5d0,0x37596f98aa5298aefac1,0x571277509cf83f7f94e0,0x1d53fe53da150ec054f8,0xfb40483362cd89010310],[0x88,0xcd41359dd331b1f9202b,0x518d5b28610a957fc8f1,0x2618ffe6d09212e25fcf,0xa104164ae1e8e5bf6c8a,0x331e20c2d90a6afa2f87,0xd91c4e07273fcc7a5f2e,0xfc6fa81609e769d5d096,0x20244d6d2ca2615e36da,0x8f9e50a792f3f4758825,0x7791679c0e679aae2fa3,0x26a3575ea67448d8878,0xd28c22a7c002dcb74b44,0xd39bc7a5f942ce0ca1db,0x87f7fd188b5bc63274e8,0x24a33f9adc3050000001],[0x4,0x81f8e1bd1e2c4264fa96,0x6af370a7876cac247cba,0x50abf8ce7d513bb7a002,0x2c0ea9c67cf52bd9f2ed,0xcaf4affe7da5635ea1ab,0xbc132c4ce66ca57cd59c,0x91c709561a1f0491553a,0xb57e61981411b306672e,0xdae346d70dc321dd67de,0x4d5905fb696e02a19316,0xc8377e8973509b726c0f,0xf42bf1670d70d985b49a,0x1e6b784f90bb4d98cbc2,0x12809b5e4981b44a133d,0x436d267455d4a8010001],[0x8f,0xc69d11e9f7e8d4989ea1,0xe0703c0643b428fdf33,0xfcd645c0a786e0c2730d,0x73986cf32fedaf97bfb1,0xacf97d7a551118d4529b,0xd0e6c23295cd40072eed,0x5b9fb733b23d6ad4f8cf,0x627b364e457be1d27a2e,0x730ab7704dbca8867147,0x88908961149affd2cf91,0x83f4471dac9acbaf6ce7,0xd79df4b03c36656a32f9,0x31cff808f29bd4d16fc3,0x9f75e9fcdb7ddca37dac,0xb9fb3b2216882c120001],[0x50,0x64fffed140eff029470d,0xc799434506c0ab6e541f,0x46d01dd2b0c7361cf6b5,0xab24a9a6c20c3ae2562e,0x92c3889f50fb457ea89f,0x545b309a2b7f0181273c,0x78fd5079c0404a7cbeff,0x6ce8fc7f6535f33701,0xa79ee6d24f03008fbae8,0x37e5249fa99eccd336d3,0x7ca91a471eed2d427123,0x6804238863e16d3d8752,0xcfcd9d257110ca7d75b6,0xa7a00cfe1ceef650b9f5,0xd8864136be9678130001],[0x10,0x94a37e63393340030887,0x7b6c7efab495797e4583,0x66f43664188b6105055f,0x6fa32a35a662d3642b4f,0x9aa2e5693a87843af6c4,0xa5754cf4472e4e2baf64,0x887ef3928f7193dcd0b4,0x2542659da6792a8ed741,0xc677734be3266de75167,0xdb77bcacbfe283b858d9,0xe8095c688eac44746259,0x942fa2e613aa1180f8a9,0x63060df4117bb6b6823c,0x2eaf3b0b1610f086dac7,0xc3fc3603f56486140001],[0x1,0x68461cbaf10d9fd7f853,0x41d9388ea8fd197082e6,0x2236910101bc9f27d9ae,0x9469bcdb9133ca344019,0x51d864b974c1da35f62f,0xf16695e2adc0b3bde142,0x192757d83dbb0c49b40b,0x521f6725c83fc82ac6a8,0x302210a902087b35228b,0xb539b70ad1446a221a98,0x245feb3718daf144ca86,0xa875a7db7a701a59ab7,0x872bec733c1f20895889,0xcab1d3c43da3126efbfc,0x468aa5e69d73b8550001],[0xda3cf3176177b8eb26c,0xf5644014ed9ad9caa204,0x1714eb534df5b38162a5,0xacb5243225bc274e5fdc,0x4beb3ff49c80ad63df7c,0x6d7e1b97bda9c4b39241,0x2e703df1d719bbaf19cb,0xd765272de4f8574444b9,0xa1dab78309b0cf3e4801,0xf59996c56234e8a42242,0xfe5127c4f17fe7cb2eff,0x95893a30d6588946d047,0xcefe09fdbfc0dc48e5d7,0xbaefdf72255aeadd4ef3,0x71363dbf2969ef60001],[0x85f048e900ef4a2412,0x554dee9ebe4733fbb51c,0xe2714aaed18f40db6ae6,0x6d422ca7cee2e669ef3e,0xa5a19810131022298c75,0x32c0b516e1d47177d879,0x1de54441cb811d976c36,0xc0c777cc092ece6141d,0xd98e1fbe96d074d39d08,0x8d1d52616e8bd654a672,0x40c7bb3bf5a57263c7e2,0xe8047f29759731b54078,0x2f4a5bc01cb703a36a04,0xcadf2e6173b8bec5de7c,0x2b3b95a2cab863770001],[0x1b98685d4fee7e843,0xe4bc24e7d959adaa6ce5,0xd82a5c2f3d394570a9a3,0x61a1a4c28df44874430e,0x69d6f6f464a6d90ad50b,0xd4680935a48ec2102335,0x909ace5b035db65f1236,0x60b9f5ec9287af6ddf4f,0xf012f752354b54af3518,0x7cfbae1be2079cb9d3d7,0xed0c62fee6cf1e42e85f,0xc46813811bf8231dc19,0x56ddf332d34c1f881ca7,0xc2473b556f256eae0ce1,0xb68fe982a8e08d980001],[0x29361fe7bb2d4d,0xf500f76c395865d721da,0xec4c1ebe82ca2ca8acfb,0x126e409d8c1edcb6e422,0x3ceb9193652235821425,0x648cc804012a3f59056a,0xed14a881ce392e45fb81,0xf5ae7a8c46f0750ebf3a,0xc5aebf8d8098b828e1a3,0xe4239c9c0404c644d944,0xe6efb3d877eeeef6aa18,0xd5c17c82ba2014739d0b,0x203943bb41b5f80defe3,0xd57fa4bade61872dcf03,0x2130d45ae666c0190001],[0x237,0xb6b4d8e1d53ca750f20,0xbbf7ccc2f8d86d998d28,0x99768d79dec470ebf07e,0xa2bf00d8f648ac4d8b60,0x5c6173686647989810c4,0x3ecdd3a3cba7397ae76a,0x16678fdb7e3c8a2de155,0x97af39de6fc722f02416,0x327c7a02f1763f0dc46a,0x1cfe45f6817b95219b1d,0xd45b9c917a941d7c0241,0xc1294956ab51adc396d2,0x7f1d03d2f143dcced0e8,0x8627955d97689a3156d8,0xf4d729b5f12b18001001],[0x1e1,0x7c84068fa8c1496f14f5,0x1870eea7c80113d9784e,0xeb3f1403ca983907572f,0x611362a0d0cfd4179ff9,0xa8e9028d4a8b8f2cfbc4,0xdfd340ef336f8bb2c0a3,0x9e5697ddb8b35c5f2e48,0x414e684275f88701694a,0xcbc3791e7e110e12ed62,0x107a7e6b637e88a3a337,0xedc89c9b1f72aacfa3b6,0xfe30f852e53a04ba8d2b,0x45cee3700d8fcebfbd9,0x4d7acb63e7554fdbdd02,0x13c5dc7282a602011001],[0x12e,0xb7983fb75478af7a40aa,0xe3165955845e0b6eaef2,0x5f07441443e8a45d61e6,0x282c00bb6fd51fbbda42,0x37794198b979a029b4c2,0x699d17924e444ed146c4,0xc64447cebe44fb75ab7e,0xbf0b107f429906f87a66,0xdfe2df744e709b3f8e2b,0x16c1a13999b778ea4b2,0x9ebaba76c0da6d4dbdbf,0xb981b77051dc10376de5,0x94770c7d2ed66cd771ab,0x90db6cfab3610a9f3c65,0xd664011765695e821001],[0x6d,0xb13bfdd0111f665e1071,0xc2a7041d8e96fa13e89c,0xc5620489c1a388ca93dd,0xf8d12ca70f8e01c6a2f4,0xf106ed0f7d19e0fde998,0x625b7831c90cd32f6777,0x888554ee47e65f6c2933,0x7cb2b6742feb884e08bc,0x24aca094537b5a8f003d,0x8f79df2c5e8902e624e0,0x17153dbe56ea8b56d49d,0xded4bee7cef8e6d8f447,0xad8d247b080d7cde0b82,0x4896b8754e2bcd48c137,0x59216b9e91ad8a831001],[0x17,0x6589a57d9ef3587ec0ad,0xa7eb662ea7ec0fdffd4d,0xf5331bdcdb09aef7d252,0x16f195069dc7254679bd,0x1ce264f432133e0a7196,0x43061e4ce4addc8564c6,0x2f02ccbbbe9a376870f6,0xb83bb5bb1901d63e25c0,0xc3ac08cdc539833b7ad8,0xb0d0172498b950d4d4c0,0xd618d91363683e9b4dab,0x3e260d794c5d8ad6bcbe,0xfef8a626b75dfa535d68,0xc600917118ce7b366e4b,0xd6fde3b27bdf3e41001],[0x2,0x9c42012e3717289db95e,0x8029354411702b7801ac,0xd07921b96c1f6ffe56e3,0xb9923a5f4c80435eafc0,0xaf6234e1aa17e8256a7f,0x2d153cad5392b2b275fb,0xb3b5cda15afa115b89dd,0xc20d5d277ef6fe530c23,0x9094020a4bca1e6d1fe7,0x306a807d2f0fcb047d49,0xedc23818b34aa5cc281c,0x5612b8b5bc4a39723c94,0xd570e1ce6e07d174bc97,0x47b901adf98528471504,0xcf074be397ffa6a51001],[0x1f402427534432196d35,0x747d82e0ea12b4e74b26,0x85a3b5ed0421c3a97073,0x9295ca44361d21a6761e,0x982f5d5087cdb0cc1b66,0x2fda4c8cbcd9b9d9d62f,0x8198e90092920c6e5a,0xd1119ae178df474786a2,0xee761bcb58d8cfdf22a4,0x2b93314457cc275fbd46,0xc817b68781d2b2e68e0a,0x44534b1226b57fd4bcab,0x87c184e2abc971fac369,0x91a1984ce18b5979327f,0x3b165a64ea92ade61001],[0x26e789d0a3d725122a,0x936a70f5289720d094e2,0xaddfac0371f8c9350002,0x1bc2a038adcf710bb5d2,0x3bd69614d9e1c958336c,0xf834d2f0064da86b0d73,0xa423fd49242d1fbb4a66,0xe6f729e056411e282546,0xea483a5f14dbcf212823,0xf46c6f4683a0d73e2b8,0x3174bb18a5054df2df5a,0x2c400932f65788913a62,0x2741846a2548e10de60c,0x884d06ec7ff88ca571f3,0xcabb93e293f456871001],[0xca39fc3353845fc,0x3e94a6f602a131400dfc,0xd96f66bfb7ead7fb5452,0xe9db89268f14cedf0db6,0xbac853f3f7e5f0389c9c,0x95df52f6d8132d372825,0x448e1b383f35e84c6417,0x35c03eac1694d432b7b2,0xcffca2c23e2101cf8c55,0xa4c7022e9b3e06d8f00c,0x15eecaa8e7d3ccc6ffbd,0xaaee816055da56ee4bc5,0xba8e587db50c5ca7ecef,0xaf41f22787ac3c9b370f,0x4d6074b3cabb80081001],[0x307,0x15ccbe4ded54d3aff1f4,0xaf2a2e5c19d586a6d30c,0xfa9ab4ffafbacc2186f6,0xb20279c1963056a38340,0x52bbb36eb7eaa6d687da,0x73a2a4052ff73049b2b2,0xc3608f3f311c245fa10a,0x648b3e7e778d310f2caf,0x8149cf0c3d7f7b769aa8,0x97cc75747add86259f1,0x93055f098d1d292eb7c8,0x978fbeb4c148fe4358,0x2071c722343a0d4e063f,0xdc19e8a785bd02f83a99,0x32f577b9f4dce102001],[0x1d3,0x6093022fd9454c9b49a1,0xe9f9b4aa2671f0fde2b3,0xb42dbeb3e4b60191f029,0x46ac99dbf4eaa406efef,0xb134465a4c525c87cdc6,0xd9e8b73bbeb1693d7fdb,0x21763db9fa51b14680ec,0x60948f069fcbac17f4bd,0x7073a1f622e4f8492f68,0xf09960f717e7f1712938,0xf46660d8defef35f4446,0xadfa80526e073637a2be,0x96d590330fb80ca06de8,0xb6dd1ed8936596da4ace,0xe9e65f567ed551112001],[0x9c,0x9db675957a786dcf6c1d,0x7d8f42ea6858db5ea98b,0x5d04275d57e2ef45751d,0xea3bc818b9afd6e62e2e,0x4c79c053eeb1fd9d9bb4,0x1b7e97a7803dbdff4d54,0x7a6406e8a69c08cf83d7,0x2046a4ec316845596e9,0x3d0e1602b00df077f94c,0xe069108b3a457f6fd84f,0x5e78b7dbabe847fb23ec,0x914fd7c1c8e1d56e37bf,0xab650a860f82cee6891e,0xbc18266c7b4785432c0,0xce8608024cd7a7d22001],[0x16,0xaa86f50e1aa5461eca40,0xa31044ca6014566939d3,0x9349d57ab8accb8efc76,0x4e1826efcd6560cece74,0x1e8e448e16d1584f0835,0xd6a74cb559ccffdf57b1,0x2a31a08070ba5e7ae8c1,0x34bca641cef6101a2a73,0x79505e2d04fd89d994a9,0xf3b99acbd00bbb431d47,0x4b2f7639921f7f4134b6,0x1f3dd137e40416fbd7f5,0x806cae84a2eaa91591d9,0xdbfa4a6067619655b21e,0x2c37fe7e51f551b32001],[0x1,0x91ac7315c201c4868196,0x1676be0fb8b5b001173,0x8632f2e275ab2dd3349f,0x5603aceac01f39354e7d,0x9109ea468e03b7d6379f,0xba8aedb9365737ccecac,0x5b3dc59787778a540893,0xddf46b2218e15021c86a,0x532c218592e0cfdb04ce,0xc99e853fcffbef823cbf,0xcc615dde6f1f13400ae5,0xbe34050fdcfcf5b65022,0x80d3bc32d02f64db2a7d,0x52b2fe4aee20705918bf,0xb1b08784021ce6f42001],[0xce473c5c9af2b3565e3,0x2f997d56b9389070d460,0xad47fde27e71e05ffe7c,0x38829a7ebd40a1daec48,0x98e61359c60c99be4e86,0xe1def60bc93abca08ec3,0x568a914008e224c9696a,0x5b3006bdfd0d13e1a9ac,0x872a89e75d819293c2e4,0x6e47a2d87f6039203ca8,0xed7e4b84bd6520f85b08,0xc48ab3a98bb5eded529e,0x1ff2cf696f8b57e0aca9,0xdf0708d7ed54e020c947,0xdf9bfdad1a9e8df52001],[0x29b3fcf50af365c40a,0x7d5f1644526bf7735d8f,0xb74ad4d53b7dfb1950b3,0xdb43fa1dbb25a5d0c398,0x51de2d0376d6b501c618,0x3cc5502565ef33b58b9,0xf6f30754134afc3c0a0d,0x624678744f39182e7ce5,0x8e065475006b88fa463a,0x55a2abe521be07d89f69,0x546d3d74f001d29677be,0x4128868e6da764c2a80c,0x46cb00829b1567507d04,0xa5f8d0da3334097f3bb9,0xbbc7d4927305a8862001],[0x9179e078667e4bd,0xb922c3fe63906bbe5318,0x64c34924a0cc1c8fec46,0x84792dab521e27590938,0x398a206e2aa9b4097ac9,0x790b3c7aab732e4fac08,0x3bb12c2123f017233de3,0xb14add1189b2369de6a5,0xe0beb36c9be6f8aa2cc,0xec778140c433dffcb83c,0xfe88ec2625b5f3703801,0x8e41b9b0cece219d7c0b,0xf81adc4c3857d53f243f,0xdfb19d6e38aacde2e83d,0x54aa7065b3d2e0072001],[0x35,0x897b21aedac6151ec2ef,0xa25da6ea65f0d8976442,0x4649d3e1465f60979370,0xe147c75f57df63db0dfd,0x26e1c1f7a602e07c7cd7,0x2021255f3c44fce97c6e,0x96e206a4416ffafecfcd,0x13dd53e7ef52355e3611,0x6a21c0a4c52ef1f4f266,0xa7cbb890e59a0a7deec7,0x336a2a52943fc22f75b1,0x3060976493fe4a175ffd,0x3acacd0625d2eef01b80,0x3cc73a0cd49538952d0,0x5d2ceaf275ffb1903001],[0x60,0xffa42ca94cbf00fd527c,0xbdc13637170a00284f70,0x95d85af8e9290703c23e,0x6845d5168ad3a628be2f,0x69645cbde38772e7e936,0xb0a90a778ed9dfd8b710,0x14cb8a62d84f53d4cf79,0xb7dfc8a6388a15b0879f,0x72af347d288b907a592f,0xf26a842487cafec50908,0x541e8f6b8ddf59810edf,0x838915f22a9dea513c8b,0x974727190c888ddff231,0xf115f1bc965d812d536a,0xb0a63ef9cf7d8b913001],[0x1e,0x3fbae68581f68bfc0466,0x178a5b2da1ea323f6c23,0xaf7ce1646239272781cd,0xdb8c6b11ae23736e651d,0xe053491bc48710856015,0x50feec55da5d5b49d260,0xf9e74bb2a2c263b5a649,0x820d67324fa662d9be68,0x4b81af2083f0b0b24e2e,0x6961fedbb948a49bbf4a,0x82e618d6ec446bd44891,0xfe2c51bfc8d3a5c1fd6c,0xfef619b3b35c78669382,0xcc9874463b73f525c4a,0x9a5f0cd14f9ce7923001]] ++
  [[0x5,0x278c27ae609b1d6854e5,0xac678694bb18cefa8758,0x793da6d5f0c31bd9885a,0x6b90172cbedb05d9194e,0x74a27da6f94c000b01b,0x478bda1e4e3cdc838c39,0xe308613d724ef2f49fdc,0xdcda6d119ed528f2d414,0xf4029398f510ecaf4e22,0xb87f4be6479d43af35c0,0x468fc45856aa2c2ce2ce,0x39e293f15a4ace29a24d,0x38a7a5c5aa68f2f31e00,0x186e1bf1160118d1c4c1,0xe9c1fdd268b3533001],[0x6b58da65cee1f16e5e25,0x8710c9fbb6b58605e52a,0xafd9a047f6bd81e2b98d,0x10936b06dd57fd338640,0xe4439195d419d0dc7bee,0xd37617d4fe249e6c6bbb,0xc5263fc401f254c5b24b,0x166290c7410be3dc71ea,0x1ca71148df15e13ab024,0xdd6b0ef96ebdb2c1fb14,0x7978500e83e984ee9284,0x85061e90969a91da7f2e,0x83b84e0592e4c95cac77,0xb1b3facd9ee473452a2d,0xa1edda6a3b9b0f743001],[0x263b33f072ab180b128,0xd40ec302a5b468b94b64,0x66f4449d86728f11b985,0xceaee495236f47d28e67,0x27e98066272964017ea4,0xf731278ca4586f6c4195,0x780f033b8a3102f44b4f,0xf35e8c1b974ded099fce,0x86e8e4efd3a424807573,0x96e683e6fef2310cde8f,0xe476da7a30ec4be93094,0x6bd53338c11c5681d4fc,0xab156d2607c31d7d5ab9,0x52c8064770e82fd4a762,0x86bae3d6d4d172153001],[0xeb078d0b8b39d7,0xf1d3957941557835598b,0xa61840ff37e3b6c48702,0xabd8a38cf45d79a6920,0x9b9d00f61c92d90b4ed6,0x23f792db4f5a222d82b,0xace6b59056f07418084c,0xd6335e0ab5d88f8c7e1b,0x5eaa0a383c8381d15258,0xcbb86c1ff0e00265f5d4,0xabc04a466026e925ce58,0x15fef016981709dfbe7e,0x239b8a831369eb8067bc,0x3af5c44004d276d8ba59,0x1b256fd5defd60063001],[0x9,0xd06d37c84a82591bae81,0x26d5374a1f69f853403a,0x58592dc3ac631bbf55cc,0xb75e12ae023b4219d2fb,0xe798e6afcc3d67dc9051,0xcd9e2fcfd332161e0010,0x5ef36ffdc94883572229,0x598e932d5f72ab5131a9,0xef7e596fe51ab3ad8580,0x7fbacba1f709f01306be,0xc61df1b00992d16245b8,0x33bd3b10b97ef86f762,0x62a94e7c10e226ecfde6,0xfe25e5e69bad62ab4d23,0x6f85fa491ee706904001],[0x8,0xba0c7bdbb67b65c467b9,0x22fa450fb715f41c5b4f,0xd7f613781e453118c8e6,0x4365ca1ae911136d2575,0x2b31ffff8427465a6961,0xf820f661dbaa6a1545c3,0x31970a7655cff2a47d4d,0xb24a4065608d2ebac994,0x2a8d089319286fdf64fa,0x3d9a17c20481102b558a,0xabad9bd7111ad8e368d4,0xe83a4a70cdcf11adb197,0xe450a2b0ba5fc4f5c5d8,0x16b2e05edae8b008b00c,0x654e93bc2c2509514001],[0x3,0x173005f56fc74fdb6d8a,0x5e966bbd544983ce14e7,0xcdf90af5867a971016f2,0x5bcbe306206e9a7d51ac,0xcec8ddc94d4734ed23df,0xa0614a3225a769218a75,0xaea7f40b4692b734cff3,0x5f7ef73b6f44d30872e4,0x11df477122f11a3c2314,0x1fe9d5430f304f1aa489,0x970c867c848b835fd604,0x524a604eef7cd0c3a3c6,0x87a1aaae7050f673292e,0xbb04ef3c15ca705d0589,0x8d77ae8ffbfdc3f24001],[0x5ab605967fbe95343065,0x93d1447099d14aeb0db8,0x6c95b50ca93ef5696444,0x10cf9c4f1b00b1c96b0,0xd95c8fe41c6fbd9d301f,0xdd166e549e8a53f50488,0x1392769ebf754995f36a,0x6d1e44dfcf39d7696605,0xdb6497dd3c148ba02f97,0xb6ce614cd022109d377f,0xbefabb9e2365507b9601,0xe48c93671b0e1d2d5a5,0xbed9e40446d5e9425dfd,0x182c76046f6727ba9021,0x8830334961974ef34001],[0x29667fd9317999967a8,0xf16ff01237d692adf309,0x50a55730bbba809dc27,0xf0a75f6e6bc0b096d56e,0xe1f184e417a890b8a48a,0x3e8569728cc01f66b7fb,0x2ea471b7888c02ac2fac,0xdb4cb31f03967ae27a63,0xd25e0b6d9fabe889171b,0xc6d2958a08e38991bfe3,0xb3d327b6a6d355fd1ab0,0xf2b4f096a772669751b7,0x3879922f5f3f32871bc8,0xc62df7b65719cacde3f4,0xd8114da986fcd3144001],[0x1b2767a3d3f197,0xc2a15b420050cc039b6a,0xdeed072a2e76f740879b,0xb11fda357bc9f4f23551,0x8f89ba5271d1dbb9501d,0x34b7d60d0333dc719cf4,0x60256d90f691b7ae2219,0x228f54240a666659b145,0x67440247e3619d5bb2d4,0xbef3bfbe674ad0805447,0x3f9a28d416dd66b4debd,0x463e5c267c7ed885bdf3,0x21fdff32af6c1d7f8b00,0xd54c5a9f7bd9abf2bbf7,0xcfa11195d985e0054001],[0xc86085ab64b9812499c3,0x753bb6058ba1d8de1c5a,0x4e53f596bcca37bb45b5,0x460eaad70119f4d74402,0xec9f9b9f24338f4eb5bd,0x4d1fc349299ba83c09f9,0xc949a8b5f7109f6157d7,0xf618e34f5fd9f7cc1bc0,0x4ec0adbc246805b57d3c,0xa9f12f0cfb412741293e,0x1e984ac05e7a6bafe72a,0x1d1cfaaf33b7b34a0dbf,0xcfd6bd00b33355370fb1,0xfb26c7d6fd290bbdee58,0xc827c7db6bb45f505001],[0xe7112a8f3bd7388ffcce,0x2980d489bd3e048efd9,0x104533bfc2a460562bd8,0x235de06d339de3d3d69d,0x5c491810be0156b28c6a,0xb8a161e0a7acf9e13268,0xf76a147dcdfb83b18d65,0x85da9b670125f4d66fac,0x1ea7c290af48009d5b70,0xd0b442077f10ebd20a4a,0xd7194f8e8e9a61c22e42,0xed198e53addd4ac0a218,0xe03102d0e21365c23c2,0xde2eefcebcebd3d69554,0xd3b39e58c52c7a915001],[0x2c096c7fe428d87823b0,0x9dc7f3ef50079e48bd1,0xc5c90047d35e9c94a8ec,0xcdae84c21b47c8c84f3,0x2b1f22be667eb12aee88,0x30812271351b5ab5c51c,0xa38b70299302668f9986,0x276d761bfab12ba5db8c,0x8f1d0241c3582ac41f82,0x3c79924a90605671bc09,0x47028def9caf7999cc57,0x3af3477b3836e70ceda0,0x755c98cf0c29e9857c98,0xdd681d7846e1f2277ee8,0x58d8976ca6574d25001],[0x2033e58f4a3011346f9,0xafa5ece18e0a15ddd501,0x27195087e87b38eceb72,0x1a7340d1af2c705b0f0f,0xc0a027c65593fb226b43,0x7d75544ae89f372df154,0xa97ebd582c79ce86c50d,0x39a0e8c95864b0e0719f,0x636c02a1a8a89ba71891,0x4f69e5c0c0e85581309a,0xcafed0125f2f965198ca,0x7accb0fcacfb2aad5f29,0x2588458de7adb4ee926,0x527fc8c5ecf54863a481,0x4aaea6a9d60496135001],[0x6e66e311af8907013c2,0xdbda077c67aa5f810ab8,0x5020e9297e607e67049a,0x37fa43d65a88e891864d,0xcb7f9ce3170ce139c8a6,0xb96ed6a52ed36002bdef,0x53165080c5ce751841dd,0xf03e9ce390feeb7c789,0xd27fdfecec1d66753851,0x9aee6f2bb6499e8a946f,0x8781e3f4946e9b7cf86e,0xe79760911fed657739ea,0xdd99c29877f6af4ae29a,0x56a52e7dd7b388363eca,0x5ff1845af432ca106001],[0x833519af1ae37bd40b1,0xae4e0244baf5e452418,0x15288aac173ae4f2e721,0x9026fbfbd87f75b13910,0xf5caeefa04bc0cdbd5ce,0x8f360892baaf80c8b533,0xa0f660bc8f5c817eff76,0x3acda18db0f5068729e3,0xc6e14e9e02dba6460126,0x4eb1b1e37745ada61a7a,0x8e6841862ac6798ae8c7,0x567fb31ed455ed44b0e2,0x25ddc225030f69e6e310,0x19c40281bac4320f2471,0x76045dd3be2fdc116001],[0xcce3273e7f69a8b0c3,0xe3c578d20c51faac29cc,0xbe43d7f3677b7c2d4b28,0xf7e1a880a37e80788ae5,0x43a8cf05fe459dc83a02,0x918237311cc1f6389895,0xba8695a849107fca63c7,0x138808cfc4df9af53aef,0x90e67f1b07089603dfd,0xc6945df5a04f4508c370,0x85a879002af19f1318a3,0xdfe9e98f36a273b7f5b,0x5246fabfc7fea7c3de1b,0xb4fc5b6f83184cc10665,0x4659e12d03ab16126001],[0x401647699a142d3452,0xa5baecb25a22ad66f70c,0x56a301b93e503f543f4f,0xba909bdd4892a94058ea,0xc28c84897961ce9796e9,0xe8d5005e7ab3967b601b,0x67c04552c93a936d7ee7,0xf2e18b2c8971def58aa,0xc7dfff923f2008842cf8,0x63857b39249db991dbc1,0x8264b4485385d3991be7,0x5a8a3550b6eb6c91176e,0x55bcf908022846b1ac5,0x22fe5efa77943a218c57,0x6edc8b5a475360107001],[0x155cc27888b16466c6,0x373e4ee61e0b8f225259,0x723655e86a1abfc6bfc5,0x3e3033f46d86386ac84e,0x40d981832875ef87dcf8,0xa2f1aaca28e6877e755e,0x77eac1c643138679d4f7,0xafba083b98325f4fc838,0xed4aaa86150aad816452,0xcbd729130c3493309e95,0xd621916d712c9bddb3f7,0xc8d8bc703cf924305d24,0xac73efdad560d6ce5e41,0xb654ca537d3168b5d972,0x7a4983c8c27120117001],[0x8,0x9894c922dbae1bf2b569,0xe9e7cf704f961e1e2a76,0xd9a9c507e729f0b28062,0xb64e0455c1ba49c9a378,0x9d6eb38eba5229c84814,0xb56bd44ef8733cb4d0b8,0x437b2a1b9f7ab7bb7218,0x5f08319618bc5f7016d2,0x663a2f111491a3c064a8,0x869da19b6df782a35504,0xa15604ca0ac33ca82053,0xb82b82ab0283dc645af9,0x323159e575c174aa0bdd,0xf904666edcce2ac05a68,0xd7404e7d5f6414000011],[0x8,0xf1c56d64a5a0be79f68d,0x8f8f60e41f0d8e9aa0ce,0xa3e9983614671af45a80,0xe073451136f28d50cb6f,0x37ea22d4bcbd64fd3de4,0x51baa6e3a326096c6924,0x4a1efefad1f6fa0f7577,0xb687312207fdf9d39d8d,0xf4b818259fb798841a32,0xcb1dae6b68d48f18282f,0xd0d1df7ce106960f6378,0xa4913ad35f818c09b404,0xe3848dfb9a5577d7845e,0x1ddce17d8b05f1e65c98,0x2a76296a65f9ee010011],[0x3,0xba9e75cb4641e050659,0xf7cc8627b66702b9bfe6,0x6f2321c0e88b77e3e7a0,0x6500f35a807d4c280157,0x36194efc250d864dbc8e,0x2f9fcce004de011d373e,0x484c6b990436afc48f6e,0x614c60d8279d4d97d3a8,0xf4fd2386089efa1e49b9,0x11702f45cfe0acf43fc0,0xa52a64af807b2ca05ccd,0x99275d553b5f7f0b2a05,0x2117622d9a4dd80dbd1a,0x56a6b83c53a98ea9d208,0xa366d164a1d14620011],[0x9714d21339eab10215c4,0xa15a0feeb77367198469,0x88bd50305a3392f372a7,0xb4f4fa08eb966fc4eab6,0xf5fb231977cd919674cf,0x8deec6b64e7eaf5057ae,0x643417d1ea0d9391e09e,0xea99f681ab0547931de1,0xa112e7c2454770b6ddbb,0x8f265e00a14d5d3273fe,0x3990cbb3e5a593ad1d1,0x7bd943281cfcdf307050,0x6d5e27e1af5c5b30b14,0x79ced7c4d5fc6b31dc2f,0x3e40543bd3c339a30011],[0xc663cbf27ee86a7b6fd,0x66529ac42da401018535,0xf8c88b3b4dfab9a620a7,0x1f5b7fcbe9e341b196f5,0x57342a26da08b2891312,0x8a9121e079736ae47bb7,0xeb61392b61746d3444af,0xb4e0a728037589fe5e4c,0x79d27482b4c000a06c7b,0x675b729d855ba198b164,0xe0a9a115378f3467f01b,0x217647f1406c6b50d11a,0xbb3ec6ae0d01cb94b094,0x4d56d3be6e33187d3700,0x6f4a988a496e03640011],[0x14009f9e998fb1619b,0x58314c3c1c01eae51039,0x11100e657eb043fbcc5c,0x3ecf782bee2b970f792e,0xfeadd728ecef0bfd20e2,0x510370a69d9ad0aa3e01,0x68ab99b9d3fa8353c390,0xdee9996f476ee51e630,0x383eebb9d51b5bd07be9,0x30301994a98fb3010436,0xd001cde9ca752095a7a8,0x84239db507db21688687,0x2e073a0e9690e37dcd4,0x63c92740943a0d6f7622,0xeb5acf02f2862f850011],[0x409fe4de1619944,0x6809560864ab8b6106f5,0x32a8c92d82b4ab6b106a,0x795f66172fc1d6b5030b,0xf4e1f5de4740cbbc48b4,0x571fed9d5956cb4c9d1,0x57d6870ee3e747526b61,0x376d0e72d2a5e4df2158,0x952ee0ba717bc647b00b,0x2220ab7daa05840f8a18,0x5d6b2eb6dc8bfd21e872,0xad9fd94edca94c6be437,0xb9b0b21030e779c25ddf,0x392df91e1837773dee05,0x6edd00ed0e59c0060011],[0x4,0x871ad2b05772c98b85d6,0x72ed84682efcba30e110,0xf314ce3a63142e59acd9,0xf9b94b5ac66e8964cb62,0xdf721d6c3e351cf52068,0xffba51a8286415b5df28,0x3f44997c4b242f362152,0x2a09a819a4f115c19b95,0x96baf3eceb96fda5c4a9,0x9dfa8fb2611761398d33,0xf819ac8d8b17b7d41988,0x9bfb0f75d189111cad84,0x842e547e97a9826f9326,0xa11868763a675d357517,0xbf2b8effa35b66501011],[0x2,0xabd7a62c5c989f7e1a5d,0xadf214300fe68c481c2,0x2219539c1f5ab7462055,0x6ee77817ed9e6ede0101,0x2e9e9f020be910e40270,0xe9177792b4f2f9a8f0eb,0xe4f6cd699c70b3564e52,0xc03ee35235c982c2e18a,0x1cf3ec6a0e5a481fb07e,0x8e2fb138b255d88f2d0f,0x4805df84492e8c4d21fe,0x2d7bd3330cf70623ec8a,0x14f6bc9e72090c7470f4,0xfa2b2519e494411c372b,0xec07680259fdc4511011],[0x62472a2d784a993b2f58,0xb048a24f0033b17660ff,0xc3b70bcd3213db411656,0x1651fd9b45f108764a37,0xd8eb21306bbc2d43072f,0x9dc9a5ff27626094395d,0x1b4db727288a7c5f70b3,0x4623bb18b2962bb1c959,0x539d3fa0739da6ec6031,0x76fe05b1b300c56966d8,0xd47d9e614d02c1e12d08,0x1a6d096c1af7bb2c96de,0xc4fa633f1bce2bd3533b,0x29ee58c0d8d208808439,0x3d1669f5018b70b21011],[0xd6796a2ceaa6be8f068,0x1707b57954368201bb76,0xd408f28fa4826a4a3e37,0x211c8d730536c191207d,0xe8177458c49c4a12274c,0x144cd49320ff12d1b250,0x366accfbf40f8535a0fd,0x708b0679796ff691c08b,0xed5957eb325f08eec6e5,0xe5f05b09e65632734a22,0x2862250cc97b7bdb092e,0x435ec88925e722ad163a,0x97cf595e7bc230d2f2b9,0x834989b52ad7d9aafbfa,0xf16bedcbdbece7b31011],[0x2d78e815c59a671c56,0xfe81e8bf1128e495f207,0x577d5cefb3476fdf780,0x7a4758d17f71afa69988,0x996eeecc88651a41e551,0x238cbbc8b1987e7676fd,0x3a6d27c3025edfaecb1c,0x23ad16abb8d860d48b9b,0x3f09adbf2cf64968ac85,0x9acb69bc53d9dd5c1550,0x6435eb4508e9c7f9cfcc,0x495dda7739913c832eb0,0x1887f348dbbdedd63f17,0xf29bcb65f513cf24443f,0x4fab57c2b4b11941011],[0x1709e7ac291feb3,0x1c4457401d5c4210d707,0xc1e737ad59d63b69791a,0x1a07feb1184cbd1546c8,0xb651b3b1856056427a10,0x556267b7a550ddf96bfc,0x898ffead3095c65b2c9,0x8b195a8bd934710e06f4,0x3dfac40c73d710f52528,0x3bcda7977624ab5bb60f,0x509aebb82a093ca1f6c7,0x38e6eeb5f249f4bf9882,0x6dc6bb828784b3bb273c,0x3cb960f0f65a69c55fa6,0xc6a015d83aff80151011]] ++
  [[0xe8dea79d82c15b361af8,0x21cb902e756470d73dbc,0x6504ba10545265c566f0,0x2134b87a35f0f7ab7ce7,0xfb42e6f5697049fdf84c,0x27eecf27ca6f09ef83ba,0x8fcbb3c258961f4cd66d,0xb2dab8da019df6be0094,0xc3df8bac01ec18df72b7,0x78ca92e44669ebb28849,0xe713d0e51262065c2712,0x23b104de1c1a832702ca,0x86e1141d84c01c45d896,0x1d5dc6dda5b4f521e0dc,0x650ae849c9ea23d02011],[0x3984a8d1602f360f4dec,0x84b7178a727c4405f032,0x25812bbce931b073f03c,0xf2bfd4560f40f1943c2c,0x241f413500d4e0f30360,0x9f321e707caa6722481,0x85ac27e26d8e4b667c54,0x8dfe047afdf6174195a,0x5360b1d6620b53e23011,0x5666bb17939968877ed3,0xdcefeec1dc64389cafa9,0x82fbfc751d32bb781bfc,0x707945cf112bd8ce3339,0x999d0804a0b09eb49c8b,0xfce7096fdf748cd12011],[0x863113389eb149e31da,0x3274f02661bc5b58c187,0x2a5d63556044f24caec0,0x90e012606de3fea6d801,0x463664243d9ad5ef0dc9,0x7a190e26b94ce79f6c95,0x4cc800c3785e6aa51279,0x789e2fc6240d0ef5df9a,0x45c8e3cdcb9eac8c2e80,0x4e6d48f3d6db75dd05bc,0xfde43e56cfca028007e2,0xa2356c249f67699401a5,0x2b9ec3fd608bcf99297e,0x8705d32514e8b857d435,0xd6dd264947eb9cf22011],[0x5a14635ff0f7678062,0xaa47d47e9af8eab27c56,0x8f098440913ac698a818,0xaf3a3aca20398a031878,0x20c2ab003a6ade1cdc6a,0x3eed86c4106f85acaba0,0xc20932ab0ec17c96cc50,0xf21715e0e24aa9502da5,0xd42a26585cd426f7409c,0xbc620faeeab0870bcb6f,0x2c50a0e6464b7e43aba3,0x68c0d04048c63d5e4ac1,0x6281d2092960d352ad18,0xe5c57dc45ee236e03cdb,0x3b60583285813f932011],[0x13a344dc702f37e,0x999af4129e73941a0adb,0xf43fd0d20e5c11c7b9d9,0x707889619b9ebb0f359,0xa599d1985bd873fbed71,0x7de69752268b64beb4be,0x14453f204bba52688c9f,0xb98cbd3b19fa4dcd8b6a,0x806dea549485dd0fff8e,0x1d02d9a772e5d55a117f,0xe82ff5abb63f2d7f8a66,0x4c886a25ea4510fd0465,0x8f8ab76a8b38d1a00ac3,0xe0f75c2c45137940b0f4,0x3a1680b8450860042011],[0x18386309943a2de195fc,0x9814f14446fa56869862,0x19da4dfd64d4046e6753,0x99c6a7c718ffa5efb6ab,0x4e1aad4cb35cf215624c,0x95f3bfcfc134d16c5612,0xa63a5ff753a2bff09eaa,0xa22bc17cfdc8ddce6057,0x65ba11d6e5bfc6d1af8d,0xd93c6b238c0d648bde3,0x8f6e16153c2e38d1452e,0x874eaea077f8b3def0e5,0xce5bc6ce2984a7d3498f,0x9a1162d50c1a36058e4d,0x526b9ddf58ffed303011],[0x7c6fa683db1d7f737bc,0x5ca0b95557fd348ad8eb,0xbefd0997485cec7fafc1,0x4746fe26c812fe1b28f0,0x890bfa6bd122aaa14c70,0xdce8df83153e08c5fb8f,0x69811e20f5c4eafbaa00,0xc4bd8b23b56a162640b8,0x61e64910811c8fa5829c,0x137d7ff531254c7eb870,0x49ef02caa7c25709ab4e,0x9192ab4a5fdb30519ec2,0x8f39b7ad034ba903a9b8,0x1646e0f89b90cfa340e0,0x2681648929c0c3913011],[0x70a506ac0e70bb997d,0x1cb31c96fb1ab427921,0x85417bbb100e0035e7e0,0x22742248f57ebf2c5a7d,0x9607bb443f2db2685fea,0xefcb9cf2f952b5608d75,0x3695850704a2eb166fe2,0x2167a76f86f81991ee45,0x513b1252acce2eb993a2,0xfa9d2ecd19279726f27f,0x63d2a1bcb5848139d84a,0xcf7316cc7bc4bf78f278,0xf22cb02c54997eabeda8,0xcadf8f5c852cb6c3a95a,0x4cf8d28af20d84123011],[0xb8d75609d3c97,0x20f32ea6e626f448e901,0xa3b2d5d11d03eff064f2,0xf95b5a30d942124d7fa0,0x745c1028116805322f,0xe1f112a94fef4c0479c0,0xf14577d9bd489c436b74,0xc5bc51033a32c981dc10,0x4399d795eb8016abe231,0x77b37eb749e28b783d76,0x15442edbdbaf0d35d434,0x8c71b20629db263dfbc3,0xb068da602e05ab3b5af5,0xa3a4396a699260a0d767,0x807fc541c53a0133011],[0xf5aef64b08dcc0d078,0xc05b35cca28e2142379c,0xf2ea37b89de801fc35c,0x83c9c7ae65d54d914268,0xc24cdd881b8291c6343d,0xafaff754553ae1f3dc19,0xeda180a0bb4aedd3d54,0xcd1ca29c667ebbf21864,0x33ebe70106e98bc472a7,0x13a9b4f986a62c94784,0x50bac4476e6ff3b13d6,0xf79a68725cd201e51552,0xaccb559d80735f2ae65,0xe0c2316a33824d2596d5,0xcd2985fa13ef88904011],[0x2e28b28789ed21ab6a,0xe7bf6209a8a9778fc15c,0xb3c93feecc49edd18243,0xdacd4a93b65f46349e52,0xbbbe0e9931a8ead4e612,0xe272ef65ec96fbfaa4cb,0x31f650dfb62b587f14e6,0xcf9952adb1fe1943147,0x824d7afd3632b30a8b40,0x26a5979ca0e027a3880f,0x28a341d846fda4e5715c,0x1d1ae6ce94e91f35a8ca,0xdb637ebd20a3f4f0002c,0x3358211f06f60a2701b9,0xf4fe03d99d85b6114011],[0xd,0x6150070320fd549453be,0xcfec3031c8749c251f00,0xb303d5eea12760445175,0xe15107251259e2ae88a6,0xc7dbeaec706ca6e87d9b,0xc83882490a5d03b198bf,0xaaf3bb7c5b1b8ee55d09,0x6b80de259c626251a716,0x6039fd3f1b454706a12f,0xf144380984e3c3661cd2,0xedb38493dc0726a5b838,0x50fa54c292a878132f99,0xa92d4d31648b8e7a4399,0xe661172a5c13a06c1686,0xb1adc15a3ecdc4000002],[0xb,0xa658db39446ecbb5ec89,0x859a6a13d9cc8438dfc6,0x315bdead962a77b0a8e3,0xaa286c6d173357a19ee5,0x1428ecdd98c8076ee74c,0x9130f7c5d79b66bf32fc,0x5f0a5ba8766a1fdfea0b,0x79c644db8348cf08ed96,0xce2aa2be12b43aec14fc,0x5a956d11226d43b868d3,0x2191f3c00d806a87743f,0xeee48a0e1128be131aef,0x7883c11d3adf342cfa69,0x1dc2bc76fa83560b8710,0x929c460db21c12010002],[0x1,0x6198253c0ae30a8c2d57,0xc275d535f0d2f0c5351b,0x204d1020c10e7105905,0x32da7fe4c0becbe44d86,0xa6ab61c7385d017821c2,0x35d2a2153311705eae5e,0x1ef980960da3be8695b5,0xaa594b38f0a02f8448ee,0xc78d84fd2cfe93bd8d16,0x88837f6e81ff02843f06,0x73834f32d3d33f6bccc9,0xbb83fd30db73c7d26850,0xadb8cbb1a39334d9b814,0xfdd137882f15441e5e46,0x5c70baea013a9020002],[0x53de07457beb6029ac49,0x98b896b9600b65844a2b,0x8d7f07ef7e3e0dd77e38,0xaf05c0543cd4aa5b0005,0x83c998360ccf16cf44db,0x3fa251ea4333a2e47d53,0xe8a7069d4b4cf2245b42,0xc467fcbbe4e2425322bb,0xbbd94fe853a8d549d40,0xbfeac3e45d39350f70a2,0x80cf4a64f2e628db4a25,0x87baa7fa00553e5c789e,0xeb200154c17689710306,0x64551e6434bf6645c06f,0x7ed6ca0594cd5f830002],[0x10ff9e370172e10267c8,0xdfa812c6d9b64ff80b65,0xe8c10a397e7f6f168c15,0x247bc39688d9c0b28ba8,0x5119dafde449b1b25c27,0x716760f67b237747101e,0x76775fa6bd5dfe47328b,0x291be77dabaf3ae8fde2,0x2035c4fb2479e2c28ed,0xe464d757c122bcf3be4e,0xaf53b27d05961c03c5b5,0x5370ae6bfbe5135e4b8d,0x84cd3ef7b618962bbf0f,0x286717a1ad0b1c75a6c6,0x39c2b76dfaec9c240002],[0xd9c9e48169c5b6b6cf,0xf716d835de49402b1bfe,0x9c0c381947743b9f8691,0xfbae82711fd0db4f3176,0xd34fce0b62904c305c9e,0x5c80ae64b7384bb0ce8a,0xed5194f1338ab72d4742,0xf6a7cde0e7bcf83d1997,0x424fc2a06cc0ecccb707,0x1e54b37368d2008a3266,0x7a89cb1c75c36475418a,0x6ed7c1de1befdf86f6ae,0xe3eafc6ef4f83128284c,0x770e746a751059551ea2,0x58b80ef7396746650002],[0x232c7342415c8ff2b,0xd7ab806d50536bba9105,0x4bc50d212235af0027f5,0xd53bdb5a8822f93836c3,0x25c931d22d8efe1f9dd3,0x7603cf46ea71eec66d6d,0x13573a2304fecbfb51cb,0x596d614182ab3e18b957,0x1da141bbef35a84cdb5b,0x7b0fd1f14418a94c5337,0x39cff39f778d5ba64df7,0xd621072c09cb01e8ae78,0x100be688f7cef9b3a649,0x523e6887c829d3c1a921,0x495b6f426c3cdd860002],[0x29361fe7bb2d4d,0xf500f76c395865d721da,0xec4c1ebe82ca2ca8acfb,0x126e409d8c1edcb6e422,0x3ceb9193652235821425,0x648cc804012a3f59056a,0xed14a881ce392e45fb81,0xf5ae7a8c46f0750ebf3a,0xc5aebf8d8098b828e1a3,0xe4239c9c0404c644d944,0xe6efb3d877eeeef6aa18,0xd5c17c82ba2014739d0b,0x203943bb41b5f80defe3,0xd57fa4bade61872dcf03,0x2130d45ae666c0070002],[0x13,0x23ac59f0265b28f734ea,0x2f11eab77b486e528370,0xac9825a3fe7b12811440,0xc12444733e31671917b,0x1f7c2d3ac6894300512b,0xc7b3ddb95abe09b947c9,0xc90e8b6a29fda529c3b8,0xd5b4df546fbe8ade9c09,0x3a226fe9622a189af7e9,0xdce1aacbbbeda4575090,0xabbf54acf99b8c6c9587,0xdfbbcaddb4fd4d6823f5,0xa8a370ea829604c4ca4c,0x637791fc78a557d1d78b,0x1330f49fad26af001002],[0xb7b3fba4d4380eed61b7,0x8ab425f4b6c0317bb4b5,0xa63cbc7bb7dd1e6aaa60,0xb8f260bf1430405a1470,0xf82f723d9309f7c4f3ba,0x1d1878b2cc6bee9c87dc,0xa4dc94ded1b197bc73f3,0x68d4beb52485e9d36c59,0x5a83117fef61af78e406,0xad0f3e4fb52fe8587912,0xb183fc8cd477e9589c4c,0xe2a504d32890e81ded59,0xd77de689f26fc3c4321e,0xc68707d76bc3719a2a4b,0xf4900eeb0d3fca811002],[0x1,0x6a290cfa21a0243b298b,0x52e75b969594e800f44d,0x3e09f1a74646bfa9de98,0x53e1f71850e1be92ba28,0xbb28d298850986e625fa,0xce5329431007494837f,0xad1c343f9fa333a77fc,0x994827eda529b9c6f9a1,0x35a1f4d419e2520ebe8c,0x9a0d0f223b28c35b1a39,0x19ba28b940d155e40b47,0x4f9f68580e31649f5461,0x91a9627dea14b0d54ecb,0x14d4c326a0b1ccbf8bf7,0xe31adb00aaf696321002],[0x870a34d42ca1220a46c4,0x168b0bbe0d9cfc44bcd4,0x5adbd65d1dfb366ec220,0xacefcaae16feb7d5e3c0,0xfbf10b09d734402325ca,0xf334463c3d66b3c01467,0x1ac712dfbe18742ac5a7,0xbd3d7b4b1fac5aedebe2,0xfd22be424f2cc2735e88,0x9053249eef5f95761843,0x935a509c6bc208cd215a,0xc0c785b6c0a9da482d7a,0x1a85e29a4a8b5dbedb60,0x1b368b40f5b2dfd3eaf7,0xeec1c2dbcdc0feb31002],[0xb7433ee878309d7fffa,0xa890d4ce36943efdbb4b,0xc36eb7335d91ddcf363b,0x8a7bd06c7d4a5af27aa5,0xb2a35fb40424600797db,0xd3112d2ee65e620ba282,0x9c6555b5bf457be0958e,0x52320f53858c7eb517b7,0x8c0661fafa77a941fa11,0x7dc743dfac0f27e710bc,0x6774682c7889298bfb19,0x8e0422fbfc55463e39be,0xec9d1d9815f5282fee8f,0x32dda10adf74b7414aa0,0x3f7f81f2417748341002],[0x10a920a036ef3e740b,0x80b623f144905c94a88e,0xa409c1186be0eab6fac8,0xbb9a18cac87c88df3240,0x2c3b410bbc0dfe8b0fc,0x90a91c47cd1400b3b8cc,0x86303b84bd708b178bd6,0xe89aeabcb07efec5287c,0x533e165e5747a385bbd,0x59035d36cdbdcc0a55f0,0x87f22b50646233a9aaac,0x7eddccfb760a94cfe2ac,0x305b16de9644e7b86a4,0xf55307c6bf563ce633a0,0x49974f9d287d5d951002],[0x41278f4f56ae284,0xcc385dbc967d403d6e88,0x844f02524f072c4a6da7,0x89cdba5f09d23e03fd1d,0x71dd16f1c0581b9be9df,0x3f2ca0d28b666c203374,0x163b9e4d142439b03a12,0xf895cc98d1a02ed91843,0x8d8e9ea6bf5f2cb09c6f,0x5ce944f7418e2469b462,0x24bfb30a8c8676820a0e,0x6bd62a2e807651751cd9,0x59e5caf6835ab0c8d67,0xc46b1e92fce740c49f4e,0x657fd677249180161002],[0x6,0xd7d5eafa3319835947c1,0x392d3e850733d74bb847,0xad6de420a32a3ceefdd8,0x4cbf0d22651ab27d5f7e,0x4a8171465c994fa63723,0xaba98748ea80d253814e,0xcdfbea1dd2c3f524f7ce,0x910c6ef24ef9ef0497e9,0x4daae40a0e86ef57dd18,0x18a7a4ec09c81382a67e,0xe823f11984f86480b35,0xa7ea6948baa63df57030,0x8e3b21dd071aa54da80e,0xf93fe80e829f9135d80c,0x2ac9db2b8f6ac6802002],[0x3,0x3002d1aef327fd86257,0x6fc8ee9f0f4d305ff5b4,0xbcd572adbdf5f95e0ca7,0xbc1f5481c96ebd967193,0xe582bb5d02433595912a,0x5dfa2c151dfc902cab8a,0x2a4c389f2c630587236c,0x6fe7d9b40a5fb3560ff5,0x6e6de28e862c03ec94c7,0x27d621a63d3e3687920d,0x52d46ca01b7eb501001b,0xa80f01134c7dafff93ba,0x9f9fe75b6d7204d8ddbf,0x294b176998153a40a955,0x3dc0c6b49f7868812002],[0x5430e5d611ddf88ed13e,0x45e04e4a0a2d21187c53,0x6c388d1ab926423c9d1f,0xc17156ee162a727a3ae1,0x95e7ede10b7bb7c5eb7a,0xf6f907d6e14f21f0531a,0x1d6bfa4b1bc9b1e9feaf,0x1e77a313c28c9c9a9d15,0xa0faedc8721a571a40b7,0xba99e50ceaad14781551,0x2e55f8aa0590791c8e33,0xcf69fdbdf0e4fed9f183,0x1f5bef746e20e28c1106,0xe807244dbb0eefdb4e26,0xeb00ff566d752a822002],[0x9ca0c8c2bbb1faf162b,0xb7350cac484e8216fa81,0x49a84cdfac2ab1977c5f,0x37c2ed89d115fd1ad46,0x27295d568dafcb5d0ab3,0x57a11409bf2f27f38ffa,0x77ad3d411412eed6a553,0x259614f225c22061b71e,0x11ebb0b57db6464ffb50,0x3e34f4e861a19f20c980,0x9fa099ac65d5a1b5a9ad,0xea9796ba6d557f056b17,0xb9d6330a5b7e605e9962,0xa24189c6d298eefd0e8,0xdcbf36aeee710f232002],[0x21b6ddf328e3410b02,0x889e9cf2be56dd0243c1,0xfc5729e4be815a0bf2df,0xf9d01b95b1029d704405,0x50eb4611dd766879af83,0x4f542ee73549b20fb86a,0x92f13ac29019b836dcfb,0x630df91f9be8e42e4217,0x5a98134a2184397bfc7a,0x9ec9cfb8da5963078a7e,0xc13d3d74fcfb10d21ab1,0x786d79003ac3bbf0d302,0x70354a24c76bd8621d61,0xf0a6d452aecb329f3a7e,0xa18cde6ea0d03a842002],[0x1e6f97e389072b,0xfe2f33ef904559b94019,0xa733a9289c2e38e60e74,0x4c97ab8ed8bd611786a3,0x6775047cfc7e40832ab,0x9179b7033c3abc8f6d56,0x16b3cd5cac3e569e272f,0xf08b3c957ce9ed78152c,0x81966eff5a8fcedd9e04,0xa51df86553001a83a0cd,0x4532de09fce80e92957b,0x6c9768e7cdfbf7d5bd7c,0x9313f6120f0e7f268402,0x21ada186f2c41592f838,0x110d23beb4c8a0152002]] ++
  [[0x1,0x85a028bacbc41bcddb26,0xa2969526558e68707d2b,0xcc2716a3f3ef71c3becb,0xd44d5a403fda3bffc389,0x4cdd2bf0517f71c0a3e8,0x969522d5b0d4cc0931e0,0xad3601e73337bec9112f,0x8b768e57b3486db263d4,0x1d373cb07e5fcb9b5a8f,0xed5543c3a1f220dcb9b0,0xbd1622e92e5709652314,0x231d8413d0ae8e031ae8,0xda12ea704fdf26dba68e,0x30136f962aa10e37c5e0,0xe1967de2cf008cc03002],[0x66bc1033e88c3e31221b,0x84edaf47279762711545,0xc32be2abf286b4039bc8,0x70e359509f82342570be,0x9f6cc9dc5c79e56bbce6,0x1695e3bae9e03925e018,0x27d095981d24dc340d69,0x91daba4bd0bdf46560c9,0x750153136a65226fe657,0xc6b9b3e84f20b333dbf2,0x507b570e108377b870a6,0xbff447aa89c0320fafea,0x35a5f56e917ecfc22f68,0x343e5380d7d0df6f2fca,0xf63b313455f93a013002],[0xf06958df7ac724424c7,0xf42c2b9cdfa05ecd5500,0x6351e8af8f8330e7b7da,0xd38e38e82d7e3f346d1e,0xe1922efbeeab682881f,0x3a55931652f4b747c3b4,0x2ec692d91b80fcd473f3,0xc47fb1ac29a4eba2384d,0xbf9f7165aefaa5faaf79,0x389d32cbf2c476aec10d,0xb708b2de2f69674ac5ab,0xc3f1146d9f75037c8c84,0x9db0d745372a7ead84,0x56513809d977aad5bd1f,0x487f93256310d9823002],[0x59756eb943144993c7,0x6ddff6957557179fad87,0xc95f1b56646dd57ed5a5,0xb058290edf1ed24d08ad,0x6e95041f78b48847690d,0xac3223f11fb4430aa5a9,0x20613f33428c60c4075,0xba8e809291626a5e2c48,0x9d0ba450b9f4802e47c3,0x691a6ed26ffc05c0171b,0xabb7e2191ea95a8a5d13,0x1a4910915bdc8fc8bb9,0xa53a4d2917bc06707836,0x26fb7aeb20a75302b081,0x444f4448cca13c033002],[0x10b1e5c15ced18,0x4b7df1d43241e8c6e87a,0x75328e413cfa7c1943a2,0xbd8e90f7fba6fd8e981,0x89fbfc3adc29b63f77a8,0xf398892e9a6c32d64dfb,0xb40aa0b6f790188460e6,0xbd4d7c34a151b1c1ec05,0x2a6b74efc70bd561237b,0x98c02b9fdf58adb20a38,0x9779cee4324a21f7385d,0xf6e1d591caa2628dfb92,0xea356da449fa394f42c0,0x782c4e013748782e32f7,0x5a7fd46e7503a0143002],[0x260a9f65fb3ba5d04042,0xba01be25cca5d30beee5,0x27316198386c7d5b1f48,0x7a3440d8ef091852c75d,0x4c178ec84eec2d883535,0xe3fcaa127d0e7614a8fe,0x21ab67409d7bec5e4f00,0x539b4d8c56fe7d573cc9,0x7174b853396648b611fe,0x1ea5d849fa51b40e2e56,0x6f43105f293db771596e,0xff9a513f514b9447af8c,0x48ea31252216286e1dff,0xf583ce57000ec06e186d,0x9ce816278058a1804002],[0xae3174367991094904b,0x139708dfd1919f26de6a,0xde4071e65e6a8e9e92c,0xf723d5a963591ed0e318,0x92d100b5c72ea7be5fcc,0xa87cf680a44eb23dcefe,0xc6191a9402e337fb341c,0x9869399f7bae72520aeb,0x4c805e4bfef2c19d6207,0xde9392eaeb4785de00ce,0x18e8c0b36a84047b8213,0x4ea0fbae6e963bfbb381,0x61cded8ce59322f0a47d,0x918c5e4ccdd46da9aae7,0x211daed7d322b9814002],[0x7d8d13e0866312b29a,0x367480a91ad8e36bb56d,0xb29cc1bb4b832afb44b9,0x8c0e50c63cda53bcc90,0x37572f73917e4a00c929,0x24c72af13b45875bdc19,0x53ebad190d2afa55281c,0x86782ae102fb004114e8,0x7b52a0ed918992d97ea6,0xdac47813ea52fd815861,0xd6896305197814cdfe1c,0xa473e5ae9db3201dec4b,0x3107bb42d44bd2b9d3e8,0x914f66027acf2f41a452,0xf373a0fee2d2aa024002],[0x293e88742aaf5a71c9a,0xeec7c133ab7dd834daa3,0x2f1c51eebdfa0d78ceea,0xd1ea1f3dcd220463ac4c,0xd991e88a6da2545b0ca8,0xc1fa03fd27f19563347f,0x44a1cfd5e6793044e5b8,0x173bb158fed9aab8670e,0xa0d9ef00751ab1a08d78,0xf9432b4474631c9bff6a,0xa518cbd88fe4113d3a73,0x33841b05d53fb5004733,0x1e9b356f3f147811b168,0xa6d086ba7af1f5cd3945,0x71717cb63b5e20005002],[0x4ceeca8cea25ea3fde,0xc4f44d10b325f40cfb9,0x333726b784cd1d017407,0x1b6eb34a6707ef41619e,0xbd505320e56b8ada2323,0xc4dbd567e360835ca743,0xdef6088f28f8d64968bd,0xf4dd4b79a115ccaccea2,0xd5fbd257ba1423be9afa,0x435cbaff5f14133f329c,0xf315aa61caed73ca39e8,0x2f86f9b0668ac1a59130,0x108bf609a7823b5770c8,0x8c12f3f727fe17ef366d,0xed9059e548c20015002],[0xe3dd6fb05cb984484,0x24d43499695d0a16e190,0xf6cee3f046bc7fd9d52e,0x297577f84904259c8589,0x809101021af94a5a9350,0x6ca11c86c5ef04fef8e9,0xa5472bd9820d045138a5,0x1fd15ad26576ea353025,0xf3871c59635c73ab9837,0x328f70b75d78622069b9,0x396bb648f61dbd3e77fa,0x85e5d2f57dfb6d75936d,0xc84d4a91e395e489942b,0xcee3318cfe20f0793ba1,0xa6dbad3081a0c0006002],[0x1468da9f8dfd768a78d3,0x2f7091d4d015411e73fa,0x634474ae92054df98ba7,0x70ca6cf40f3c98f81028,0xd7fc3d9a87638b9d9a09,0xd2cd0d620a871953bac9,0x9c54ca966fb99635292b,0x678bd115aabfb2b98d1a,0xc3d5cf598176e5705515,0x653647726edb94541093,0x8925c55563a5e47b6d12,0x762efe5d8997a32367b5,0x9c7ef6fa0ab2e56dbb6e,0x5b4eff6a34d7a7bedb26,0x7296677d7d4e7d00012],[0x6be0bb45f2c4beb54a0,0xa4400e0bb2d4403c6084,0xc7a653e13ee4b0de967b,0x6886d8e0f14c3b47ac9d,0xbf91f367b64722573a4c,0x860ff1da893fc2bf30a3,0x88a1f271059370157cea,0xce6d462e0b76553b4a43,0xa76c934211d4aedff71f,0x2fdf9b781558bb4d6079,0x6cfebc6f4359514e4974,0x1bc18234d04bc1e434bd,0xcc8268919c254081edc1,0x194c4c922f0ff8daec67,0x1c248bcd191c06910012],[0x11da345e904ccd80182,0x2c569e11cd10da63bc39,0xdaacb6c83202ee7dcb7,0x492703c5b3c944089023,0xe3048bbd97a459947ddd,0x12cc0a91aceb224e936c,0xb45ea615ccf6d69ba88d,0x19348220d4b1e06f20eb,0xe69018cfdd489f327c02,0xca891d4ec43cf0e62e96,0x3a02510311e243a29e16,0x8bbdb2e9ce73ad0a6475,0x6995a3126a71be070086,0xd1d0cb8ae362191d3f25,0xf5abd7511c81bd320012],[0x1fd5cbadbc1870ad0,0xdf5775344537a42a125a,0x7af41eb06bd90a1417e2,0xf3f891cecc42c045e52b,0x4ddf7ab1caba9fbf390a,0xbf01c75bf9005a087fed,0xcbdf9bcc4ebf9fa028df,0xb5f4178d29a81de11a16,0x94e9ee093e99d6dcd64a,0xdc9172ce5e4fa9d016f1,0x80c47e62b0e643bab47e,0x545220f8fcda7cfe8456,0x821348bbd99cda645ef1,0xd1c4e4b55264879444ee,0xc1b6131829ef31930012],[0x524da522133a49,0xc60a779e929a04165322,0xc9bd142a92a9a98ccb10,0x709a1e23fc38d098f16,0x3de905803d5db5553ec,0x769a7ab160d3db362958,0xf8aa647952488d10f4de,0x70d91e0f1861e0a15c2e,0x1363e051971c9bf3766d,0x17beb2d4c160e24c1301,0x69b07ce72bd57f737cd9,0x5e73da1ab57ad4f8b09d,0x1d4e3cec119a69a2b5d9,0x61432ffbb3ad520ae59e,0xd4ef0709fbf040140012]]).map tailNat

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def suffix8 : List Nat :=
  ([[0x7e577b00ed6a1ecdd5,0xf2a7a2ba87ac8cbbbc0e,0x9e4a70eb7f7d38c8d95e,0xfd32c3f50b66a2400e22,0x741db7aacb18347930ac,0xc1d692015b8c9b2c3c3b,0xf30d1c129b416b870b28,0xe7e3071861c74eedca4,0x9f61c5109dea264c312c,0xb9cc1450d4183e000776,0xfc8b17d1f99d84fb8b96,0x1b85bb36fde44902d51b,0xbb16a2c8f91102cbdbe1,0xa83bd54f423453424d93,0xd12e401a7d1800001000],[0xb06839e548d1ce60d6,0x1287bb41a058befdf443,0x9429d7382374e6b6f6bb,0xf3376bc7e2b00384f73e,0x317d7318ccba69fa35d9,0x351651eb6b8f8c6c35fe,0xf95d81c326cd773392f9,0xaae2f4da487db5bec50d,0x9b68330824c9a1615971,0xb1d70fee18b37e7d7ae9,0xc3da6ebb1f5802acd10b,0x51f3e7a787d43e432fc5,0xbb1939ed7f061f83e86d,0xf80076a8330d0458cf6f,0xdfe5f5f01d0000011000],[0x54617e5f8a347c21d7,0x84adecb52c4bb8a01614,0x9d1c474ba6e665fc905e,0xa5895217a2fbaee1ed8a,0x760d9927d3c89b05dc79,0x315af4eef74415896ccd,0x5e8d6b799ada6daac2,0x3ecd9dbaacef1ed68cb8,0xef4a56c58db1a599a18d,0x127e37fb8ab6b3ec804e,0x3b6d9492386e65babc9e,0x19d287b4170dd71be3a1,0x3e4fbe2653e6cedab301,0xfa250fdf5b1cb2789d7e,0xd49cd2d4be4f00021000],[0x4f5e2d052f99f8b7e,0xd5649430cfb9408200b8,0xacce653cea29866a037a,0x1db4d76bf1e31c655fd8,0xf0bf3eccb2477065e708,0x40e90e6bfcb5b32a0f18,0x71cfac1e35d623ef111e,0xf14eb62e84c74317d054,0xfeab2dbb1d83e899467d,0x791c37ec6ba6d6c8d4ae,0x7e4e3f9f1dd627839be3,0x9b857339c0a588d08f46,0xdff7fa4a6f402773daa8,0xe670958ddaed189c0d47,0xcecb19c358e280031000],[0xaad0845c7c3157741,0xc7769483426f961be659,0xa8530d32755e703862c9,0xc0ff519086faa7fb6ddb,0xa8254c6d46053c93c598,0x5972911bb89a532e1a1e,0x9effdb0f6711254eeace,0xb9061ee5d49e77cf1ce7,0xb3365b5c02a77fb4fdbf,0x2173df704b2da2476511,0xbb7e8f111a1c40fb6572,0xac75d7698d4030faa2d7,0xe10e10351efca9ae9933,0xd737f8e2ddd364d90dac,0x3714f98af9d540141000],[0x40ee927ff3f1afe07,0x17fc7b19f64adcfcab6c,0x4617891073823dc725fa,0xc8f6abbddce180183f4,0x782726ac08a5f6e2d2fa,0x5af1370581512da5def2,0xbbd832ace55b38270080,0x83d0e81651f4805e17ac,0xb2f02a2c88227606512c,0x8826607da1c0449e40ef,0x10c891ce2ddcecbf1652,0xa1938114c661b67ef615,0x7b2832bee86fdb7be278,0x7724424d5c300ecfe017,0xf465a7c3c71f20151000],[0x95efab40c5476f59,0x8ab1ff5914a49bacb4af,0xf88c7b9ea3179221ce73,0x919269c299a88a2671c2,0xf15883769a37dc2f7987,0xa875b10dc5bef31afbba,0x882964f352c60eacb6cc,0xb96414ce980e7eec6929,0xcc08700bca2a71b7888e,0xef27866583e315e4452a,0x6fcf5228a1937db92b83,0xfdcae1f28f5170c42c50,0xd4577b1cd68857b3ea1e,0xde6c238f7b906fb957a0,0xb18a64978fc860161000],[0x891b4582edfc841,0x41d1a64be8e30cf740ce,0x3c94f01a72f07bced46,0xc109132f9d25a9a627fe,0x93fc240f3058e737cc9d,0xbad7d24e141dd76ec225,0x64a63a035edb523b48b0,0xd21e4067944a1fa16bab,0x640626815583f260c11f,0x3efce25fb8cbcb1ee0ea,0x34703281132c89d2074a,0x4fc158ea87aecd61db40,0x71abaf096405057051e7,0x9b497334f4e3b5a1ea84,0x861043d6475e20171000],[0x1c6d01759b1ae9,0x16e6b3dc1ae838de6bde,0x7bf92da6bb6b9d9d92a5,0x9ecf0cc7b2d0d7f574b,0x94c14532c3135f9d8ed7,0xe36f7132bb9283d03d6e,0xbbb6fabbe73ccfd28e6c,0xd3e102c2cdb4b2a8636d,0x346043269da1239796a8,0xdb35945cae12164f2ff2,0xeea7cba1968a591ef5e7,0xf6dff65fbb0ba26abc93,0x2254993deb68fd5106b4,0x9bb85ca8785b0ee44691,0x52616d272943a0181000],[0x1,0x1dc89280a7675b8571d6,0x83c5d3aeff8eea6f2dee,0xabfbc42bef9a32043aef,0x9cccbb6a87209fcea021,0x2ed3a17db134b9615352,0x52da7426cc4cecf3ed8d,0x5aa613eb2e5fd3637504,0x43ac5514cfe3dd43a588,0xeca2815b0f2f5bd8aeb2,0x3dcb1ae9e5356d62cccf,0x7584bc52fcb2494288f9,0x3e63e0cdf5c990df625a,0x4c1b4270f5c0cdaf760c,0xf62ff4e5946deacd3b0c,0x520a84408c88c0002000],[0x1,0x7ca3d7a082b713a71f2a,0x6863a781eaccd75b42a5,0x52dc2f7a83652f0fb6aa,0xd4b06157e706723464f6,0x2e45f63e1f55fc3e8d9a,0x916adf00270f84796e5e,0x4c9cb4807ea26172d6a1,0xadcc1538c91bf9cef35a,0x6d3cd08237dbfc3afd4c,0x217e64904cd10d8ffb7e,0x1ede10f8ab4814e7416a,0xbcb002a2866529511f5b,0x1fc49d1e6f6b45ecb227,0x6dd0003e5f4868d030fd,0xe685579ed267b8012000],[0xc64511a2da2ba0d7f44c,0xb18c8963f3c0fa307728,0xcbc9eda7e60c0301eb0e,0x392b59e78ef481b0b037,0x2cfdfe714a17564638b1,0xdf829d9ed7f491555c29,0x6a4b5cf804d0bf435a7a,0xe5877bfabdfc89d4df76,0xc7c2e0019a5347331a69,0x6e2df8369e38d2b03be4,0xd5a53b21be7856036442,0x626f9c4aaf5a2b487d71,0x2ea0f3fc3a2aad79f76f,0xb2c96954dbf06d678625,0xd32bf84de411de022000],[0x3288a5d3d7dffac1ece7,0xaaaac206112e4101cc52,0x86c854f2c24bdddd2708,0x39950b534e39753d0322,0x175ba014f08f53f24706,0xf676706310f9338b4b6e,0x5c290667260f0ee591d2,0x68786f5da4e361c6abbc,0x712456500be48aa27d1c,0xdce8950e5a9908ede1b5,0x3ab360ef8973623f090,0x8559ccf7c3ac72322aed,0x3865ffa621a5a6208034,0x118248434ef57d72b098,0x3d9b3b6c419787832000],[0x6f03e0a7f39034d0e24,0xb43f18fbf2b67d03e63c,0x93a685f74ba4b6c05f65,0xebad2b7c92027cd050a,0x70d47d4bc3c584aede24,0xa223b1d51e2e041e9a7b,0x37c5f8d3f23b480905e2,0x4b8d77400771de9fa9f9,0x51674baf9f4c08dbc510,0x7b2034ec9bf14d0b52d9,0x6f00652d85053b04be3b,0x2a85a10f7e9552d9404b,0xf6c23338eda5e28a9921,0x3868c4fb01551c5492fb,0x99d132df78e261842000],[0x7f5b817dab8a2b5f03,0x918279037084c5b08043,0x2af962cbb710a7e144a1,0x38cac4a5206c86238fd2,0x50bc22b682c1acd3ec82,0x67128c392e3b60d4f358,0x3f3b2274fdd5b4e9393d,0x68224b19adb86bef769a,0x8a7164e2f65f7b133546,0x9c9aeaa5928d9a5f6663,0xaba5a7875f013c16bf1f,0xabe5589abbfa8b7da5e,0x54a329f3b6263f281d3e,0x580d9297a6bdb64c45c6,0x1fca7a18df9740452000],[0x3c7f14fb688ee331b,0x196d2774e843258e0e06,0x5c1afa5072c9dfca304c,0x211d7dd769c8292c9a9,0x7c1f96fb4459190855fa,0x28e3cd86713d7da3b4fb,0x50c5372d7af381569f06,0x6edb4019bdb99ded691a,0xbaa2fca60d0526000478,0xd08a10bb2b96cc5435f3,0x419277c865720d91da65,0x11380e5e7d8a73dd1f00,0x9bc11fe3ec38b3b600fc,0x33691e9c0dfeea7d731e,0x1771cbf405af74062000],[0x3b51d6e3ac571e,0x20a848d95589828105fc,0x594dd6a6b374aace431b,0xe853f5913464e16f929c,0xab482827b20ace233426,0xf07b5609f5b7eb55b821,0xe7ba81b1e4bce201d0bd,0x7dac5b1e60ccd4c64cc3,0x714a5bf519221d6b379e,0x8f3b73f819e9220dd118,0xf906be21bf6c71d09f33,0xb1515b54c4bd0834d2b4,0x7ebc293be7a678c81914,0x25518e18024782e9c32e,0x6a640602473360172000],[0x1,0xe1212d73444c6c747fce,0x3ebcfafbee1ae02283df,0xfcc4c4d2ebd84a08c250,0x7c80a923201a9710d632,0xb74382ba293bb98bde74,0x7f62a2f852826d8547f0,0x71fcc1e80b1c8f26e4fd,0x56071f92785e298f8733,0x421143baf4e897bdd780,0xb1974f658eab4291e714,0x2f6fc4cd32e07ecc8c92,0xca2cc9cadc1a6cb7ac86,0xddafbc2dd388750c0cf1,0xf4fdef07339d80b96022,0xc36818ad3d6730003000],[0x1,0x6aac37e8c1495a83ebba,0x627bc8ba8b01a5df001d,0x494aa091e7cd49afb4b3,0xbfd915b778e10fde6e35,0xab4d4a1a7d9fe4918a01,0xf89af27a293f39bd713b,0xad9b843543d5c157181e,0x9bff1b6950a217d5596d,0xe3f1eb9bb98ba16b259c,0x1531d4ee2e17a7cef9fe,0xb23577634097392a50f8,0x73a947c567a1ac5053ea,0x351b913786d9b2828383,0xe3bcd6ebd98d47b599de,0x91eff40a734e65013000],[0x6987191a67b40be178ed,0x6f44d1c4a6d3806bfdbf,0x27ae5febd890ca134968,0x41dcd6629ee498a091dd,0x804935327a9aef09170b,0xff44512f59a437f8c750,0xbed493a1214db1cbb1f8,0xbf523e936839e034b9b4,0xcdec75c30ebe999c2004,0x67a0a94338ee9d5f14f6,0x1ed0e3af7e6628b4b1e7,0x7d4b9013473436f81775,0xb4e3f695c413377adc29,0xf0078c3bff1d3edf0578,0xe9743b4d9454ac023000],[0xe82d243aae654ed9094,0xce715184108be66a8eae,0xebcf638cec560a5f0726,0x891ee70392171b07265d,0x40e2c91227fb08a07942,0x45d29a4d2ff84f10f392,0x38ddf9122ec69e75f0c6,0xa03c4b3007e9b578b185,0xf41eb5b71a56a786f8bc,0x2175c42692e41cfec42f,0xd9db3cec5563a2df0521,0x4a059d8e22a968c3999a,0x9a41b857eb089d5cee5c,0x262b001157890ef18bbc,0x29039fadd281b2633000],[0xe50cd594b557689f36,0x1b7cc99be261900e5baf,0xa358119684b62a1f56bd,0x21c3b479e9eb671c4c47,0xdba92b7039e1222248ac,0x3d3f44cf602e65d46b81,0x586435a91ee94d0edaef,0xf7f4311d4c3d3bb0492a,0x792bbe95a1051e8c1b30,0x8870516ed3500a41a894,0x2aae958eb1354a763a3e,0x12bdb15f11b823c87eb1,0xda9c6394453838ba67ca,0x9de7072de8a71cc6072b,0x525afd60b10333243000],[0x3c619ad8b0acbe3f4,0x1d3cb7668467c60d4cb9,0x26fd9fbaa50f9b3e71fb,0x95541517eee5273a3963,0xb64ff3c3a378ad9a6318,0x80e739b586b7ecc6dc60,0x669ee0e96f6fe95f5c46,0x4903dcb39f35810be49e,0x725f9b9e3097f56fc32c,0x698d9dfd454713f38ec0,0x244b1a3b59e3d7e39a0f,0x50936cb6af4e4b77355d,0x269795b1eae790155b7a,0x871ee68296a46b1cf903,0x65aeb9fde29035053000],[0x10c9adc1c2c671,0xe76cf93ccdbb85409ee5,0xc0ec8aaee504db80f872,0x2a22d5f7f3981acf7c73,0xed499a2adabe1f9d1f49,0xbdb2e1e4ef89a5fe2cb,0xc25bcc1e998e3f25bd3b,0xce7278c609b76976bf68,0x9a76f268b43d94414cc6,0x258b64446f42175e63e2,0x5c89001fdf93bfeea5e2,0x6428144e295d2499e3de,0x66ef839f97fe6d77dea9,0x98d35e5e575472310341,0x90cf8a469cb400163000],[0x308634ea1682217b93c,0x8ea0754d743f6a7c072,0xdfef52c9d7bf99e566bc,0xca668b57fec28cd1ee69,0x5d13fb4739f3c7489dff,0x569cc632b885b410fa7e,0x8016af3dd5e3031fd05d,0x784fd632867f7102dc92,0x32798949a81afea1471a,0x4d16e515e34b29d2d544,0x797ec908ee115d9cc8ce,0xd1317b744ca379a919e9,0xb3b9811f192d82e091d6,0x4dc99c05722302270171,0xbbc86888feaef3904000],[0x2ea02fc36c722e23181c,0xc70d4323c382071c8244,0x8c8c6a4ca3cfa0713e46,0x8833b650b81172bd0bb8,0x1879aa1cf9e26979aa23,0x6230f13b05bacc13c5b1,0x88de42dd2268f14ab540,0x55e08d49b6d9a685d21a,0xf2929e44e65c45632c43,0x7a24043e1033da5d38d0,0xc5aa36dfd222c01df011,0x309c241de4dab62f0812,0x3420fb6a3bb956cd4d2e,0xfc3664a7d9d6f7032367,0x64d8f27abb5c1014000],[0xd8f888b1f5d70c7b183,0x2c89dab4509b3c54d9dc,0x1f2f611ded4e96d0fa02,0xfbacf35b2e9efacd6b9d,0xdf84318f90071a2e76cd,0x36e8254147e47d3e095b,0xdf693c625b1baf1c3446,0x671208f8656aa3283f76,0xea0604a15248b48dd976,0x4fca5204e4024be8e4c5,0xba94f3bd6d13a36eadf7,0xc110d660181478c70536,0x63f81d82bc9884d33801,0x36d1cfa066e82158bb84,0xb0590888fd7409824000],[0x16d93da00ed88cf8e8a,0xb36544357b92817616a,0xb1afb338a48d8e48a17f,0x9e0b5d99e3b2b8461f77,0xeb1d75a33ea19d5954ec,0x45cee07e7fc752f44631,0xbdeab1c83f8ad066f4c2,0x277d8856252070b49671,0xfa0a031803a669beb882,0xb6430303f47c08209efd,0xbb76e84176ea966735a1,0xf79a9f4928800b07b124,0x74182659d51c4037e1de,0x763230da67bd8c41e070,0x8a1e90670b3686034000],[0xc774fbc079f50596f,0x2ec572b6203686db5969,0xc1f4e978e99c6c3a1e29,0x3b64b5dfd1a3629c8fbb,0x864b2912d8fdf16ba46e,0x8348519ac8e89d0ac9d8,0x72facedc5443d361a423,0x60f7a9e8af104b667fea,0xdc62da9966690c04c361,0xb5cb222f9438e5df06f2,0xfe2fea14c452334120ff,0x8222401fb854eb20f87e,0x22baf20f523d573fa053,0xf72a8242270b15a4a4e8,0x28eed45986317d044000],[0x1685f5685b3f7,0x8b984b02789e9f3b7f22,0x1f6b76858caa28bc6c1b,0x14e6fdbed2cc33733a0a,0x2b0a7ffc1a623191686a,0x84e20584bd0bb5756ffc,0x8c0e52ff022661efb5d4,0xaf121138baf29279df7e,0x6fc1e1ead08a9386a912,0x3be254346583dd4e2df6,0xe8424c53dcf422815c20,0x37f267dd33078320830f,0x2c73e7282af88505c495,0x6b5bee691b48a51e4a58,0x8540e1f57155a0154000],[0x4ba079ad2208becc306,0x999d765bef932561840e,0x904da01248e6c7e1e237,0xd13bd9ec730b5749c41,0x89a0e291c344b6482d32,0xf2445fa28f2c5ebe27d5,0x5d5e7e9e941e79d9abf2,0xa6635869748ca6c30545,0x4bfd7271c9b44952a418,0xefe0684576153c24f867,0x7533b575c47922bccf84,0xc27273a9d156c96ad512,0xfe6c8c12e0c94f0032f4,0x1bd9b45ad7eec4596c3f,0x59e1771fe46a805000],[0x287c2264ee6a5130df1,0x2f4a7105c639cc3c29ec,0xef01334576cd8a271bf0,0x6395adfc7255d5abbf9c,0xeb8da50d78db69648174,0x28c395fbbb8430c627fb,0xdd49fd3ce0e300fbbbbf,0x6fb56c7b7f46a2b5c679,0xb1015b547abba3ab95f0,0xa70e6c6d6928244a1e3c,0x7abff80e08604cc2218a,0x8e1f27d736abf608bcce,0xd84390adc7ba26f8a38e,0x8542eb8c69323ed381a3,0xcd99e6196616db815000]] ++
  [[0x75055a556cb369d0ea,0x39cba6453e05465cbc8a,0x44c64b105aec8f7ecb25,0x80d4fd1ebb3de7eb55ef,0xaa7337e4c8cf20f92e83,0xb8adc7ae5ba8978cbf70,0x1818897be19253b07e15,0xd3eddf0d956bf9e2c99d,0xe0a5e8417927619c5816,0x190f7d71d438e8ce73f7,0x702e05aee00fd2dc3a68,0xf79536f2d0c9944d3dac,0x19dafbcfb6f34d404615,0xe48dbf5910ca1764ac53,0xf4e14f04f8913b025000],[0x7327662da5484f5cb,0xb48291cbdfd6c4d1ac98,0xa545df10968765988448,0xc63484b6465d112c8abf,0x3d2ac8c931dfb180617c,0xa897aaa9664b03ddb8,0x522c501c6239a8ca66e8,0x52cf7ae1a929dc0855f7,0xae13a2cdbec90d6f335b,0x8d62aef051c28ddecfc3,0xc50e606703a35103f612,0x86eea44a16af56581bcc,0xc7142cf74cb69c6894e0,0xa90b5212027f2ef46dcf,0xf855923e0f8df3035000],[0x23f3c22bd9cfc7ce87,0x7b7e55eae97b12818c73,0xb7b91e1fb4efd89541cb,0xe7e30832758bb9a663cd,0xc1c65a2f026df1ece23d,0x36479da9b06ae19fd4df,0xcdb9f0d96d530250bffe,0xaacf90d363fe7cb9613f,0x61d3a16be292aa71bbb2,0x31d3c5201d2004a7c27f,0x80c4358934271cd82bed,0x9c268f394b43b6d0d6bf,0x13dbaaa1c15047ad7fab,0x3d3499c228f2837769c0,0x232bdfb056ae0e006000],[0xa1725bf7cd58f3c85,0x90ed76d655982c5cb8bf,0x5a19dbfe63664933b85d,0xe940c1cd19c2cb26df76,0x6c34a7d14e71ec764bb9,0x8723f6a29a8a5ee5eadd,0x47e03f19daf3333db9d2,0x1284a02a06c18a5b9b11,0x33976f8411fa51368ef3,0x926b994b8624b41e1037,0xfd7c954d477a7b0632e8,0x784620e6e75d3b105a2b,0x3df718017598cfcb924e,0x264467d385b50ed6f45b,0x7a8745d963f244016000],[0x11b3dee79d788c0e3,0xe91ac7e95ac7c6ac73cd,0x7f46034847103db9f702,0xff7a6734ad03aa28c71a,0x7cbd7ea86f0a0846531d,0x9baee4eba71fb4f952e0,0x4858625a0a44950082c4,0xb7f657df1642bc0b5960,0xfb558d078dd6b1502c90,0xedd19fb27d11614c1341,0x9374d07182265726f51d,0x7442e67f8d4e19464064,0xa4702f364100522533ba,0x2e5d2d8cb45a92d08f2d,0xa7d2dae30074026000],[0x47f065c636e892b6d90b,0x6c9eaff467478577a5d0,0x2800114524361501f37e,0xf3f0bec94eac42857e16,0x77cc70c246a8ec675138,0x888c2cd6e2940747ced,0x54df033d83fa067c5143,0xb8115c29ca994eaffc29,0x581d2fbf732558d16a5d,0xf5c4babacf0fee46089a,0x84d6d07e622437d2addf,0x44d181c0252e40f023d6,0x13daeafbb68fca2ca0a6,0x37352c18486db5400476,0xbeab804018a230000100],[0x9573766ad9bae15963f0,0xfe843be98fb7e8bc5479,0x40a4a754ed04aa8f869f,0xafc9a494d9b8c139e3f,0x4f831085ec3ce0bb922e,0x8e3cb976bf50d11b9fc5,0xb519d91db8c91cd4389f,0x8a71c03530e8bc411652,0xfe19770a23fe8e18923b,0xed43fd39e6c57538f0d5,0xfdaf88287a9b3397fb8c,0x93876d6765187ac189ee,0x7393a5b87b8b302eeee7,0x54def13fed6ecc5ed070,0x22e9d8742d3cd2010100],[0x708de678fd87c97a05ab,0x5d56bd8d09554854fb17,0x786c5912737b44ea7036,0x37d4c698d9ab507328b8,0x19ad7549d57e0cdae6c2,0xf48f9463f05173f854c3,0x58d43578cf879d84290f,0x8bae4acfb33f7189dcb1,0xbad4e30f41909c9db64b,0x8998ae79b2bebf7d1b27,0x4a98e81fc603cbca3c24,0x52eca7c7933cf0c11757,0x47b2a28b91839e18e0f8,0x8e791b1db161aa557248,0xe002c8b0914494020100],[0x2750e77edad95acefd20,0xda9cf93904d3834bffe0,0x1bd1a747a572fc12dd13,0x67f4d74fe3a2232225,0xb2d1a35af00e19f58efb,0x27503643dff2541a84,0xbe4aa29a1e6c4f4fc93b,0xd7456fe7eb62682e7a0c,0x42d1407b9cc931a63b88,0xbdcbff4a2a9bff32e950,0xde8ba1944e83b4b729aa,0xd32dd1d443b3ada2e7a8,0x219cb3164c40df9d4a6,0x8d0a5f9a9fedb5ae0c1c,0x500d855a2933fe830100],[0x68023a8824f03ea4582,0x8d8116675a238a83bb65,0xb4b84ead0ae4d133694a,0xbf3e32b312b2f7434c82,0xc473d57e01372eaa05fc,0x3e1f22ee1519896a284a,0x9b2d4ca2899e9862e557,0xeee55373471e6850e406,0x862d24c8a80554afdd98,0xe18e293f465e9cf9e630,0x23ed07358773984a8a8e,0xf8655f83004020f060fe,0x4e43cdd04284027fbc3,0xb93d33f3ce9c515d9467,0x5b64ccf3ab1b11840100],[0x81f0c0f29604c416ab,0x10f498b79b0b19fff922,0x6319647ea1c74b048f92,0x5bc8ead0cea5c29cfae8,0x3fc0235fc225791d2002,0x12ec0538ef39989b2d24,0x69bd89a9c54af313b2a7,0xd3f7b29e44bddcb99841,0xc8de078d075a321a15c4,0x7776de5b1920c3234c67,0x9c3e1adb6464ed1b8f4d,0x7ac2c2db99d75c450cea,0xa8ad319c03c051a20533,0x9a37456c6ac3af5963f6,0xc3cdfc46db3610450100],[0x3dc297f7ce9e58562,0xb920949ebbac463d2651,0x5ae446d78c209732af50,0x8ff06a5b31f04344b618,0xcc94308a58cf515af85,0xcb581f7ab44141184cf5,0xd1eedd187e936a1f0b26,0xb6c819325086023311f0,0xc6d9397a7bf7b2201cf7,0xbb7a4f865bf9ef88cfaa,0xf41efca96a1fe6b920b3,0x98f1db60a363129e641a,0x2cc1eaed7e233c758b83,0x381a31e4203841cdd2dc,0xa7ec6942140604060100],[0x63c4d662f0a05d,0xb355b3bdb370959f12ae,0x78bf5d7f958711e663fc,0x804dea487d1c21c52b03,0xa0272ec963fcd55b9db3,0x6a5c03102e9380f266de,0x7520989c7077862fa719,0xb6f30ab5126f69b0cde2,0x5c192bbd27571c97a6df,0xfcb7d9fe8cd07f42bb3,0x5a68aa1dbaacb13fbd10,0x7646374da10abc1a0876,0xab71e7e7f261733cdd91,0xbddedcd82d3dee91cdee,0xe4bd158695c9c0170100],[0xc36e6f3aecb4baacb052,0xf0c818ac4b8ea21fa943,0x5ea8579cf1183aaf69ea,0xc27a4b0558ae091eeca6,0x6a57cda45dc68e37a948,0xe4ac69eb807699d50c95,0x92e6239fc689ae05e6df,0x6148fbc940f60b86206c,0x26b6e2f2e575d145623c,0x3a69350d9495b54a43bc,0x7cbed695c620b8969a07,0x72b34d4f6a4b55695fb9,0x334977a89cb1638c9cc5,0xb9a56007aff8addcdacf,0x44dafb4aea41d2001100],[0x1,0x15dada1ca10a964cb80,0x9b0ba44ed89d6d4adfce,0x4d3127285d24e04c0aca,0xa6f1d1c11d00d3ca5cd3,0xad1b9ab32f370c9517a3,0x345e7cc49d03383859e,0xad410c3c7ed9d32b80ff,0x4a12343c95e1a9e70a04,0x146f7cb5fa8df1859c6c,0x7f28b2b97b46514ed20d,0x5c5a2bd16051af6bf674,0x3d6d1573bc1a16b02dc,0xc3d80b345df3322ef6af,0x807305fbbb24f5d71c08,0xb4d1d4663c57e011100],[0x6afa4700f857da2ac1e9,0x5147446c8ab30fec3054,0x2f92573cb5b062cb7dd6,0x198b4001ffa139e3f6fd,0xf542a59046e3f2612c7c,0xc9b3f43a481ebff46dcb,0xa53b39d2e76fb77bbbe,0xbfeb6b854bd8438af5d1,0x1e15acb05d036392b2e3,0x22ac8d39dcaca6aa3ca9,0x867bb6e59f869f9e6cd5,0xb6ec28f3f656e5def94e,0x1bbb3b88152207aa6a9,0xb877356ef8636ba6193f,0xff34673fa62f821100],[0x12cfd350c1b21db82b2a,0xa3b1748b7ff7dec57335,0xb19f675b60d0474afeb8,0xc39754122bf39bd216c0,0xf7d942b6fc8217b886ad,0xa7b98543864c169f7080,0xbd87fe3f0f5b3f038893,0x2de2539f76a16c24ddf6,0x58b2dc550bf550008826,0xe06775392c48df803a25,0xe5a334c00a94c7e54b8a,0x2001f36ff25569ca8c2e,0x90493104a78af0c2e6e1,0xa7613653398c1ebb0a68,0xd92e07247a396b831100],[0x15aa0fbdeb330e99bb1,0xb997fe55929d870b0982,0xadc61bb05a01edd27e27,0x74f2ad4b375422a2d8eb,0x5c93d3a809c5335a74f3,0xf26a0b54f67400f45460,0xa8fad7d916dd4728abc2,0x4d409190fdca8da9e79b,0xe6fdad66beafbc004c4b,0x18a3138d6b91ca904dab,0xcdc3e88ed87c682fc5e0,0xb1baa0cc2620ad73033,0x6174a447093b603b1bf1,0xf56b1bd1f661b8f72bf9,0xc412024546424e841100],[0x835d2e59921e646a4,0xd8375ef4eded19ff8d77,0x2283c60127318b50761c,0x1d6007f80dfd804de440,0xf2151b90b94ca0add6da,0xc5d7012f2b68626a2b76,0x8d079377607f6fa8a61f,0xda4b841cb5b9ff4efcce,0x2a902efb40ca7d1a7e7,0xf01766db63e1128f0b87,0xe38ee9e71052df6f2f9d,0x87c276715103793e8cc8,0xf681a84e5d60b6b6feb7,0xc78b91834633e591116e,0xcda48598aa42f0051100],[0x6d1f627b259cf6,0x78e1d47a2b2d12bfef45,0x3c1e725a50916a5822fa,0x1f19505221dc760999ef,0xf6e7873203f3ee73fe56,0xf42f1af8d72c088cc2d4,0x1c11ce08d2f1f6ca51a2,0x6679103f59244cd39531,0x5f9c47b74f72feb26c95,0xc839d199ebcbe3791853,0xd3e1cc8ed98fed5af77e,0xba9f071cfea642eb38e7,0x38d4f45d719bf5bd56ae,0x85a5fe787cc6a4425fee,0x4f0c3c1eb6db80161100],[0x84a4d26df58ceef1b32f,0x76fb53b46707d578b16a,0x41b6d107f9afceb4b740,0x8ebf0c21daee6546083e,0xb49e7d2bddc7bf2e8f3b,0xeec6975132b9e528b222,0x409d56b3dfbf0f7a7e02,0xd89717b47c26e4c69379,0xee0b7c4abd842516f0ff,0x7bcbf3339dead4b57185,0x501ee4b0943606b96da5,0xd5a0c2d53e915638c225,0x1f3284923a20b2ead9b5,0x3ab5f5b0e4319d9748be,0x72256e2ac22075002100],[0x48bfc05be0e44f9e7ff3,0x1356c050fbb74995833,0x817d951e3fab9a190232,0xc71d140bc7bdfe7b26d4,0xeb9ec3d91a51f5334c55,0xda69294b10c1575af171,0x3ac22e9ba1c50a2875ec,0x225fc9eea5cd9a0efebf,0xcc44b67928af729fc1cc,0x43ca57f573b01f68cb30,0xf3741677303981902bf,0x74acb03ff2d7af77529b,0x111fd4fc02fc32e00d15,0x5e9c579d2d3a277c56eb,0xd6ce9446d0a9ef012100],[0x191b35dae9e73292dad0,0xd972fa1560a43642cfd3,0x515f572b9cf38f5a7064,0xed0fb2d7458501ba67cd,0xa98ceb73e89a19c98676,0x77d3abeb1ac49fcf1943,0xed85ecc4e5e6a8880dec,0xe272b1a19223e4a702cd,0x5427d548e5b43cc13e7,0x15616383d3d166d0bb02,0xc4d45a6d214fb98cfa51,0xce9051971eb371895253,0xde1664da599f0d9a7ef6,0x49977357a34d3173571f,0xf14d2812f68bccc22100],[0x290016869b3f135ad4e,0x5f27a13bd9aa493f1efd,0x9296cd32c73c3cf295ec,0x59a552e44d9dc8ed1db4,0xf790d28f820c1f8c35ca,0x6666b78dfd1a74a5f672,0x3b972cffc7d62227ce23,0x9d38c03d40730a6b0b5c,0x51b694f4c73bac2b1262,0x91626b412cc07cfaf2dd,0x7bd5105f63c46bbc4923,0x1a3e58fdfd90c49d73f,0x316ad20a5d53972fba2c,0x1cc45e48518b0fb08ad0,0xbbb7f4ec7eecc1032100],[0x12a0e3635c2810a25b,0xa5499fcda71b9f8bb9a0,0x900285213d9dd75715a8,0xb724e67f2eb9b6ffa246,0x3fbfd74ca30cb5418ff8,0x138ad79f28b63751e76f,0xffaeeef7262a9402fdf7,0xc1949205873bf474dec9,0x83c8a215cf0d3e847ae9,0x70a19e29a5b830bede23,0x760123d1c6ca967761a2,0xf9bf1a70470e1042813a,0xd197a704a890dd967331,0x45a79cddf5520e772a45,0xc15f745fb6e395042100],[0xc2b4ac5406487,0xdcbcb6c168f9bb97dadb,0x23601e5d45ea9ea9733,0xc89961874a58bb2ae300,0xacd55860d4bb7c3b3178,0x939722f222aff2853bee,0xbf0ddb6a66c7347a1632,0xdaa27fbbc9a0816864b,0xe306dfcfc931092817db,0x3032fc62ce069621488e,0x49fdbb18d8cb811df2ae,0xb43d9f89c3aa8d12368e,0xe64adac5d52b8c8c0247,0x9e7efe728619ffed26b0,0x74d0ea8303bd00152100],[0xb8d8ea4f516a84da8b8,0x5a139871f22bc472659e,0xdad25f525dff922919db,0xa3812507bcbc6611ce68,0xf90f718bdcf8c2a49fc8,0x1cb3232b8f3bc19b6c05,0xe6e60bddf78b0635c181,0xd3e0c6a478cadef6284,0x4af49cc96e9a4a6725d2,0x981370b9c56db2487e82,0x67fcb23c8e37088f9aa3,0x6641cff84713a806bf88,0x5144b68c68d93623f79b,0x383d3b6371268fcee187,0x934a5a61333545003100],[0xca52a8ee8e2c84c5040,0x969b8993353446d72bc7,0x4b0e766b91b344dd20ba,0x3913dfcf77f4416e1449,0x633865c29f4fc909eb0e,0xf8a3b6a8e249b0678f2b,0xd5bdabce2f114fd137,0x67d195b5367f08212ac8,0x6e5c55302b0e20d944c8,0x2a708cff90d0aa5281dc,0xf50821d3fed023f8161d,0xaac79981c3d4b678f952,0x8b595ad760d5e20e05d1,0xe14f4769e4c5302b5b61,0x5e789fe7174a84013100],[0x254a8d13de4e7ec1ac3,0x96cc95fb0ea33c16fb4a,0xe07856c450c7f50df696,0x13b571dced570014ccbb,0x12cb0096a096a3b2676f,0x9da62982c2d1df6cbd10,0xb0339283cb193d0718a9,0x84423262d110ae08940b,0xd1d5886fa4cee8f018cf,0xbc43b16b91038e62364,0x76fc6dd6ced0c14c73f3,0xb2fe91787568289176ad,0x859df19707f1a89055b7,0xc4604f037688fd296c6,0xa759849a8b866c023100],[0x1ba8397227f3c4132f,0x96b7383ae548f760a076,0xb963aee7a26af9a9142c,0xe4704a761f79e073a7fa,0xa77b250b2dac0b9cf510,0xd44b2fe8ea17960a6413,0x6abe19ce9b5286307580,0x35e6a0994a7bb92cc0d7,0xc46f0291b7de946c90f9,0xcde667ab41f3c34a735e,0x739df4a2311d596c0050,0xc139427efb6cb417a10,0x5d870c8318fa3e29ddee,0x6beb5cd014d0c4b133fc,0xc6d81529a52fce033100],[0x2d0bead0b67ef,0x17309604f13d3e76fe44,0x3ed6ed0b19545178d836,0x29cdfb7da59866e67414,0x5614fff834c46322d0d5,0x9c40b097a176aeadff9,0x181ca5fe044cc3df6ba9,0x5e24227175e524f3befc,0xdf83c3d5a115270d5224,0x77c4a868cb07ba9c5bed,0xd08498a7b9e84502b840,0x6fe4cfba660f0641061e,0x58e7ce5055f10a0b892a,0xd6b7dcd236914a3c94b1,0xa81c3eae2ab40143100],[0x16eb146008bbd5485d7,0x10f83a98dfa0b8f6c2ab,0x80c504cc676ca0965ae1,0x46ecc6870e6f066ed36d,0x17122f1d876e0ec0886b,0x311f5a68ff560458689e,0x94739a3d05784f0d45a1,0x59646d7a51ac89418bda,0x7010dc263fb0ab9bbdcb,0xa613cff81933bbfb1963,0x3c00ac3945a3056f1050,0xfdc64cacae1086da7da6,0xd18d964bfec5399ec43c,0x2425bad699fdf3864a58,0x746686453231e9804100]] ++
  [[0x93bf19b7c2f8414d13,0x5822eb622faef55115df,0x301ec7e29704001a0e95,0x404988ccae790e2b0160,0x640d52b6120de1fe5813,0x9f6a4b6504e2722acbf0,0xe4445fcf6cd439efd8e1,0x8e35256e9803309ba28f,0x73a61a01bef99c3cb744,0x5ee8023fcafa5ef3612c,0xd381e2a6cd0c43bffeb8,0x2fd36aca137668b98f16,0x578a027d640a58cbcf5c,0x4e1be65cc816d50c9f39,0x18975a9cc7bc2a014100],[0xd333cee19aa09fabc,0x958a9bf83a1a4449c36a,0x34e14389bc34c4bf19e7,0x3000156c541238db4d7b,0xd032963a98b6b9c0c6f5,0x999a7195a796d3b95d26,0xe9008db5cbb3a8e87cbc,0x6d5429f0da6ff188580c,0x5ad4bb779e32017a1fef,0x711ffd1ee8f96cda604e,0xef63a1eafa835bb1e480,0x3f4c176607ddf46e18b2,0x416ce645cd821eab5bc9,0xcf9178eda7f20929e6b3,0xc4b027e98cb2c2024100],[0xa1f735b67b35c6754,0x17d2f39828757f52c5c4,0x115fbc2b69031253f022,0x40849b309e9cd925c654,0x69078d7e00518c3ebc7c,0xb09228c4279becf286d8,0x925c44cad3f8a4737e8e,0x19f8970fd8381909082c,0x383ac8de1043bfba022f,0xa03f1d683088451d5fbe,0xfa9b5c6e45728e59ffed,0x5b081b8e3e5b86fe66ef,0xc278ad06c656ae99929a,0x68fd361a188df45adee,0x80a04eecdbad4005100],[0x237680ab872613134,0x1a162be83ec49690b029,0xbd93ca23c7a3ae3e9ee2,0xec353be62fe6ab34fd31,0x320433479c823ebf5d6d,0x586a084ccfb32465d387,0x2730538edadf1a2370ba,0xc61604109920dd46698c,0x13a0cea754603604497d,0xdd2c86f66266b642bd92,0x2697b7032084b073abad,0x3a9b5a9feb631e8a8234,0x740b3617c3dcd97dbcd2,0x2050f545a4b03cc9dda3,0x2d7a9e7f4388f8015100],[0x5d81a070e48e7d07439,0x34ef45c585b4ac934219,0x57f36b1582312af5acb8,0x9b1abe8452735c2ad2d2,0x410be7888cdf39fd5ca8,0x170a14fb1e609eceb3ff,0x79ebc695ea304dd58fbe,0x92b52d74c85ac74b64c6,0x7a4e3b2af3a8b96c745,0x12b23a796b094ac99716,0x43cc334026b3e8e09d09,0xe5277b543459980f4a34,0x95fdf54e201ab72615eb,0x1f6181ad9da1c9a05f71,0x5e4f6f062209bc000200],[0x54eeeeab539c4b46a6b,0xbacae1e5ef658bc742ce,0x4b3cfc06b9832ff9637,0x261986da7f56ab3cb36d,0x9ff8ab273c45a19f8dea,0x32dbccdb499b5c2c56d5,0x8c558ec6190420d710a,0x19da974c898da0dd5475,0xa705c835e90a05619e3e,0xa9db8735520e0f7d63e6,0xaa7ed3da4063332cdbf9,0x3bd7fff20cc59653d95,0x762284fe00c3c9833ca2,0x5e5e948b126f0ee21bfc,0xf8f096c120c4f8810200],[0x1a83ef72ebfd94874bd,0xb8ea530a2f5849821371,0xa963d52b2b5f6c44b01c,0xbce32232620128dd0c4d,0xd4221a0f7847d51f11d3,0x58f68f184a5c0a4a1fed,0xf82f3583a4a10b8945e6,0x1e619c76f4d02416a5d1,0xda7c16e19539ba4cd160,0xc79ef1209de2d09b55b6,0x6d7e12041b848481371d,0x23d94f2e12b9d11dcc83,0xeaa676cecf657689605c,0x33f3fe3f7ab9d21c547a,0xd086737eec08c5020200],[0x4864f793863daefa83,0x9f7802b82b873dc48c37,0xe865297b764449319609,0x62cd40bb560d66046c61,0xf1196825402442bdcece,0xb22789f72689dd6e4a94,0x805519957241c270316f,0x41430fcbd850a56787a5,0x6a92a8e0aebf954d8e05,0x9e46d38323949fb9dfc9,0xf137a16338693da334bb,0xb89121389ee88fe2eb7f,0xfa97f0622e3bdd760b37,0x4a6aeade290ecdb36f2e,0x3152cf87f94f03e30200],[0x4f32a2eb5a71929a0,0xbe60f5e8dc491243db6c,0xd891507beec282b05f94,0x2263449867d5ec6e3865,0x6b1c582a4537c34421d7,0x82578bdd28384e5394c,0x146ef34853e513784fc0,0xe0766e204da56eaab8d2,0xf01abdb573ba3f5423be,0x81883e7d5a7f4e738dbe,0xe9270b8a21b14d89fc33,0xed0ff7a7b6b7e180979f,0x50cd42b634e48312056b,0xe87010f2f0de21e27347,0x3b3a64de4895eb040200],[0x3005e3d26939d1,0x8e155f858f174ab61950,0x1987115d8692ae332ab5,0x9a8f3d9d11c64da6d21f,0xfac86b2896c741446f5c,0xfa08809d3d14e796e56d,0x7f3457960b4b4ea9e9f1,0xe1daa506dbc2683ac246,0x8bcecbb720b2c44bc2b8,0xa3733d3bbdeed0d3fb77,0x40fc5c7e07ccff94f991,0x88db837987c6a0e57221,0x67ef3c098f848269bb65,0x51c3ba6e256be6ad32a8,0xc7b8bb621d0740150200],[0xaaecb24f3b4bee59dc4,0xe7e8e2f1ece5a7a103c0,0xf55cf7aaa3fe2ddaa826,0xf8d3801715b2a1ed6130,0x2b49a491db565813b4cb,0x3cf2ae3bec8b1b109f32,0xbe25471f651b88acb18f,0xa060a9be901c71f1cd8a,0x782491d565eff5c001f2,0x7e2dcb868703883b6f4f,0xedc711e50844b0756284,0x12bed50dd233254024a7,0x487ee8700a736a9e9da7,0xcb5f4a0d5d029f205083,0x4be4fe6819eacc801200],[0x34a28ca767bd26b2f40,0xf80db76724c34349e030,0xce23f137c342b4acf1da,0xa1bc76d91df3c9e17c58,0x8410f9ca2ab71c1f92bd,0x22d9927c0b759099959b,0x95337e186d62e1a64d5b,0xe4b55bd8b64b8ab42ac1,0xb1f5bfaf2c519ac632d3,0x7077f977c73e7ec8577d,0x782a59289663641631ae,0x444908e90d6eefb60c5e,0x8add412cd95a6cf28c54,0xffd8815df4c992e4e1ac,0x2895b5b60a9ff6611200],[0x345b1671b8df2987a7,0xbbd652aaee1a88bf3588,0x424f2f84887c229ae2df,0x37d0a21195bebf6e021f,0x2235f93196a7af9dcd3,0x9f6c6ea06c92740a12b5,0xc926d17a1404db1f7315,0xb7485275f16b3567ed51,0x30edc10447e37ed9d05b,0x20387002a7a41b6898fd,0x79406efb9966c9689381,0x6b9bffa4998258e7fe5c,0xa9168ff99347aebe210c,0xb515f9b9ece8c5b2b25b,0xde6a535e4ba81a21200],[0x1b72cd0e0b3c7cc01,0xde3ba02dd2b826091fe1,0xdada61c3ee7789846e79,0x1a5c7d78b8ca829f350f,0xb499646607bdc8ed0a5d,0xdf2e8040430710544427,0xb544d1401758be73cecf,0x6527cb541b558394e9f8,0xd61479a679a53ec064fc,0xf5b4ada827989f6e9403,0x450270c7aca646a9014b,0x851538ee6e90f6b0f245,0x583e740d3923b2c1a6ab,0xb3732d775f798e0eb25e,0x5666678afba411031200],[0x344e6b594ca54,0xd72dc55bc33f9f54ef29,0x424413e7d0db037c7363,0xba7eb545ff93f6aefd6c,0x55ac3835995afac7e7,0x4007866f97408e57bdfe,0x476a47b72f16d65d9f6f,0xa8b0f18c6867df178429,0x11ffac1243835d86b9c9,0x2054d5c89bfb90744859,0x547a44e4b27d7b8c4116,0xea3a000a7bc640481529,0x1a3d9f1294a4bc3a77f8,0xf887a2670c7bb5b9fea7,0x2fe6b1569f3340141200],[0x160ecd8a2e2c10c93c8,0x23c85dea4f6b3e279fdb,0xfbe3017dedbc4fbc8a58,0x288a074525d19a6d33bb,0xa59c8f2e4842a6d561cc,0x4591a144e0159bc842d8,0xc0843360f49576ebd711,0xc548c4b0415562b1f35,0x18d1ebfc0d893ec9727c,0xc1f6d06351a3bc1f7b13,0xcfcc9387b1ed9509c67d,0x89336e4d2db46d2a7ae2,0xf9d6837afbd0cd7214da,0x29de529324699c97e316,0xa977e76443a063802200],[0x895696269442685d47,0xd1ca12a148406ffe6558,0x635f5d6c35cf653fece1,0xecb94bc6904c3e8f0f6a,0x1c8476afa6127527df2a,0xa3406efbb816b3f36fd8,0x803432379baf4db29cdc,0x88abd270b9601713b4d5,0x7d996a37391d36ffd63b,0x30290db1976a6cfd532,0x29dfd29290cbed28d281,0x3a0600c69e4dd03290b0,0x13892dee45b39962926e,0x589b1b825a14c7291272,0x76173236f3bde7012200],[0x5ced9d9cd9bfd9fbe,0x6f612d35b89d038480b3,0xa2ad90a28ffa4c90af77,0x25729f61ad3111edc72f,0x5f936b9ec81c99234064,0x9985c3080de9cccbabb2,0xd8c07d903af7a79a379b,0x693287f9aec3b2948645,0xcfcd4fd1c69d95d8623c,0xd1765e0e6bb7c1f816cd,0x8b03b25fc34c5ac16cb3,0x26eefc556f0b000a33e6,0x313f79dafc795ac1ec2,0xdd30330521a1df9a6cfa,0x2fa5bd50df0e53022200],[0x1685f5685b3f7,0x8b984b02789e9f3b7f22,0x1f6b76858caa28bc6c1b,0x14e6fdbed2cc33733a0a,0x2b0a7ffc1a623191686a,0x84e20584bd0bb5756ffc,0x8c0e52ff022661efb5d4,0xaf121138baf29279df7e,0x6fc1e1ead08a9386a912,0x3be254346583dd4e2df6,0xe8424c53dcf422815c20,0x37f267dd33078320830f,0x2c73e7282af88505c495,0x6b5bee691b48a51e4a58,0x8540e1f57155a0132200],[0x23bcc652a09998436a,0x7de099e9e8af002a2d3a,0x5edff3e5413111c8079,0xfea61faf31ba761653e6,0x86f31e8d020fa493b4a6,0x907661fd17bf2efd425b,0x69d25fd11b839b52e07f,0xa37ea666d8c4c664e450,0x5274d5fe6d21d0881102,0xc82e0ba1b09ff67b5875,0xbebd8d69c2b4cecf16b0,0x93ea315c47a045e9c529,0x1f7258934e9be4869e4f,0xed529beadbb417e50f74,0x929b9f20624d31003200],[0x4505035b0e783246e,0x16e8c10424966e22110e,0x990e670fa551b978fdf6,0x3235057754c4eeac4b46,0xf7f6c8e7ad8d88dfbc14,0xc56d275218d6a6e4a515,0xb863ac813243be42bb79,0xd3a62f2b7b9d2bdc8cb8,0x2dcad5c357aa1672f754,0xa16faa2534cb12bc2928,0x3ce907777211c6d23870,0x571d608acd34aba6240f,0x91f27d580b77f2dcb9d8,0x229c7f622617844da55c,0x224eefe9090621013200],[0x11c2a1c3e9ad87050,0x30fb63fee3fccfe43c5c,0x3e4dc6db80937084a7df,0xecbad4b182e3010c3616,0xb546b49f2d7836790a4f,0xbcbb236128936f6c80a6,0xded7f134d09a8522edf6,0xe1fac3182de213b102b,0x184b419fc68984b41cec,0xef5ae743e55554f6aa50,0x9322e6919e5e594cb68f,0xc65874205e15054441cf,0xcf9b06e182dc87588917,0xf1f3c7b8f055a9f94e76,0x2cd2cba4608884004200],[0x2e1ac10ceab0bc908,0x304f6213b54f9a9fb7c0,0xc3cb7f1108ef83d15b32,0xf69d23f746f97732f21b,0xe0f05f7ab2a7e1cfff59,0x8fd186305daa0d08e2d3,0xff550b3e6cd6b3578049,0x49dbfb6a41ac499ba167,0x6d82bc0cb6c5ae67b785,0x7fac19452973e97eb333,0x4e57a99f36f49c7bb2b1,0x9b4d7a5e4709610b2703,0x5db82580fc95f1227edd,0x9b25987d1d697f26fcff,0xcd0d00e95435a6100300],[0x1b18772a93f8146a0,0x9969d6a6e56ed3888212,0xe65e6e3d97dd523ea527,0x39d415db1da5adbd663c,0x8105b5caa29d4598215,0x59b76f35e0332bce9e40,0x666419964aa9c197efb6,0x904d97437c1a1ad0d13c,0x7a9d47bc81eaba7881ed,0x8dc266563eecefa9d04c,0xb8680d36215769b8dbb9,0xacc44963c92868af2879,0x6b040b34f88e6112e499,0x18d8d335aa26a9aa2f78,0xb5a17c82616c72c10300],[0x14866b0cb9a2796a3,0x3880cef461cd37e368b7,0x5902bb95256065377874,0x32227f458f1582c7fd8a,0xb8fa9bd21f473b3e8130,0xa7c694a66d11b80f0880,0x2ecee17c283eeb445923,0x6edfe87077471743d053,0x9abfa52d01f1d3ee3b5d,0x4618c99eb0171c0a167a,0xde3065b043c55b312d67,0xe956acfcf1cab14fdba5,0x49a48390dd2b18845a75,0xc2db6429bd6436db3aa6,0xabc2a3c30f36f3020300],[0x15c085f1a29e2027,0x328df9ce9e763fcf64e3,0x253c4b13b6ed64716d4,0x2dc07d0f10dad30595ae,0xd4aa08617885b77efeed,0x86667eabc2a78afd6446,0x23dcdb49a7d3bb6930c5,0xacdc3f253a076422dd09,0xb8dbcf750f60aaf21a48,0xd7786c0dc927cb55ced6,0x64c585caa0055d4edf2a,0xc5d08fa665d2ac74ccce,0xae02e61a5c3847384560,0x95e9ca9bc754f65a3e73,0x194e6a70fa1c101300],[0x18767546df59a9e2,0xcb4e9e1c0c23b85b2266,0x64668b7912f050792dbe,0x91928b696c8a9d37f0cb,0x85cae03ec1483b6320f5,0x6ab78758f0c79317afd7,0xf7bf1416e28ba3d30750,0x6ddb44e04a39f0acab7c,0xc25fabd7a848ceffce73,0xcbfa118e54bc0361007,0x2aa90bbbf30d99e82502,0x7a1f1bc006b6203f8cd2,0xc86c9fdb69e47c0bd6c7,0x4e5a6c493728a133e2e7,0x169bccaa1918e0011300],[0xce19c65aef9d5ce,0x633d1734c92bc87620ab,0xfaf7d6f207ef625dff88,0x34362a838ad84c68bf92,0xd71a6cfd6e462ecf52b,0xd54839358be75ff76a30,0xadbfb9be008e9fde8513,0xc79c698f0a70a0fc2a5b,0x19fb6749ed6e6ba7c282,0x429578cc5a9bfb837fcb,0x86040e37f000ae8be661,0xe31769b36f4aa86f1402,0x6f49a2c94570a9304f01,0xbd71b8dff484534bb111,0x7c2d45e6612f60102300],[0x6b30ccbefc9144,0xf8e4742b49be76d720e9,0x6cdf288b42666fadc57e,0xcd79439492d7eab93716,0xee46610bfc02e9aecc9e,0xa48944c88846ed83b25c,0x1427b3067945b47eb52f,0x47d51469ea3f627f41a8,0xe967e95d9983879b158f,0x1612cdbd778371953bfd,0xf5f83070bf90409650bd,0x65370c1460ed54540c9,0xea70e749bda5843d0213,0xfc2885829cc0cb395b1a,0xbf5fc51cf16ac0100400],[0x56fec174b6d519b293d9,0x5936a05fc91129da8d2d,0xdb4f4d643af49a30c693,0xb9d0f7e73c56ca7b7a3a,0xd7fbed42a23d8c3c1b9a,0x7688e781f3817b0eaf91,0xa4dcfc29ecde39007e1f,0x55f13f74f4e987cab733,0x4b626ebe5fcd3123dfe4,0xb4a45eba489645bbf9a2,0x6c82ceae8958eb7be868,0x4e49266ac5dedfdcafd9,0x5bc5a41e74d5c837f951,0xe4bbc50e4f1d611307ed,0x27d369b4aecf88100010],[0x5f459f742ad8b5756d04,0x81c955ce294d11d748b1,0x6137b9036d587e7ee6e2,0x9476f572a5cbeb7a2184,0x1d2efcc4351df18db796,0xa02469bd66af3d1bb196,0x674f93e5df4feea404f5,0xaae1d4420df0d13a5658,0x9e1065999305e90700f7,0x6b387c40b1e9330661bf,0xb780139573f335370cc7,0xac76bfa49378e66e655a,0xffb89d5ee69d8a28fd3d,0x1e4ce65dcd10d08b69cf,0x877a5d9d75117b110010],[0x2435d4582a6e78347034,0xd48947894790b521de4,0x4d8bce96fe07def1db2f,0xb92778f0e70f2a76ede8,0x686758b3a847eb7eb0b,0xe7d1e4744c9b578fa722,0x8b0074fe9e12f3a32693,0x829b7ffc06fc939ccaae,0xf0f60b5f6aba2dae5261,0x729957df0da9c155825,0x82db205fd2486a99d13b,0x6e147616358ed39a7bd3,0x43bfade0200d79435f8d,0x1b809500d1c002040af8,0x6169be14456da1120010]] ++
  [[0x5d4d4c66690f41f00b7,0x7c4b07c0f1a821796073,0xa4030a0389398a83e62a,0x20f31674fab8e7ace746,0x9a8501abbc3dca56a450,0x5fbc5b21928534d05c7a,0x4303ec4b28c7fa0b02e9,0x2c74a924823c2113faf,0xe1da5bc990c05a312a4d,0x36f8b5dba0380f5f4bf7,0xdd845e086a3da3946a68,0xf690bbbd3ca44f9fd770,0xf65a88d2b4a9fb1a5ae7,0xaf588aea2d1155a1436a,0x927d2405e01df5330010],[0x6dd22f5def5a767ef4,0x79b7d3c12d06bd1ac044,0xc83f157d61653f25e591,0xddbb1feaaaae26f90a2c,0xe2957689f881347c5d41,0xd5559afbd5bdee89b331,0xabbb8a495d1a15161eb1,0x6be530a86fe86c397413,0x10a66ddb8d56151b32e3,0x6342f100acccd3fc6493,0xc13a46c6c2566c1f3b31,0x24fba2ae559df3a33cca,0x9af72bd4ccdbec27be8,0x111eb02a8eb7e590360a,0xc4fe1e5d69d7b3740010],[0x377564c2f76797e88,0x163e137d9e0e7f484b66,0x4653531fba03be532f32,0xda197f559cc12e5c8c9d,0x92bf3940fbfebb8e68f9,0xef98ee89c5b1a76c2537,0xffa8fe325327c12304dc,0x1e56b561108266d30b67,0x76133fdb5fd6598c5750,0xe7bb3095905119a4785e,0xea2dd1dcef52d2c63e26,0xab30b3878c47de61511,0x41e355d58d623bea941d,0xe5250254a894b24f3f58,0x1e41028da03783150010],[0x59a43fc41a769f,0xb68c5202fb818dedf3da,0x5f48a7afb06890c0715,0xc2cfccc6c7af6da0b20d,0x7174dd8892ffb46c440c,0xcaf48b698f1cadd71207,0xaf014f34a3da4ed79e3,0xf8c286b29921a73b3edd,0x5c3fe0fe39160891e168,0xd6214d6c470fb41e8b08,0xe23c76174080a58cb226,0xe887f12c3f18b4279598,0x2b29388c375e88840de9,0xb786d78369c2d2590412,0x183257686270c0060010],[0x8342c3b36c47c4a2a944,0x380ce2614129fe6e1cdc,0x162a02eec1836d78be88,0xdeb968f0391983c757a7,0xc9cc2180007c977ddc39,0x79a26af77ded6ac7d0d3,0x96ed505f3a89d8660371,0xba12ac2f507c6dbbd2ed,0x67879ef87c6ef6b164b0,0x9022acdcaa6e78e8fe0f,0x5a63f07086eab13a880a,0xd7f9a44086ebbeb6422d,0x9620e1313a7c19d09540,0x320a7f325ca563fb741b,0xaf536c51a2bf9f901010],[0x3f490fc8362fa5e57525,0x3a3b27abe5a49d5d1812,0xc23296a56119bf1b330b,0xa7c7fba47353eba34b2c,0x32d2c9ba2489f446d6f8,0x9493efe1f3b434157219,0x5f5f42c73d64e88e701b,0x92867d18ebb9bd0ac539,0xbd5d4a3d28cf74ccddaf,0xdce9932fd25a6494c8c5,0x5b2864093440bf105974,0x4eaa04304aa597cde8c2,0xd9c3ee945c13594e7daa,0x4fbe18bd79c8fce60dc1,0x3af44b89e6f7ccd11010],[0xb11a989418e886db69f,0xd301098fe7c81d50f0eb,0xa9d92f4815bc25012d34,0x44d3393a73301bdf329a,0xc56a614cade4ad91cb7f,0xbf75d2ef57c7af056ee1,0xbcf8cd7ce8abd4d85d64,0xc39f230f0ea4e6de158f,0xf7f7819ec7b7c29cc7f3,0x4af98888092c93472148,0xe452971be6b722e71e4a,0xacf794a3779290a765b3,0xdd71186b3085114bf2ec,0xd31ecd861d5a5750550d,0xc5d1f900752830921010],[0xc62528a41c930b5f54,0x198fd9ed2a9fee0a443e,0xe2bc3ee596a8b35d3b1d,0x8b8e4593bb88fb17380b,0x6860629a8fda2c4e910e,0x7a038ace3e70c969e157,0xfad0cba1698d3aca59d9,0x598abe581633a7ce8071,0xe1ff67cf32055f9bcee1,0x925d0cf6b1c94cf857c4,0x31b8b759f3710dbcf6eb,0x97152f8c17b3a321a7dc,0xaa68c03ef521802c2607,0x33f66a1aa3ae4914fa8b,0xe61896b851d09d331010],[0xc905f80cc157fa0,0xf08fe825aef82ab1dd50,0xa16f08fc7606eceb60e6,0x7aba2b670a7bf9520bfa,0xf792cf8ca3bb8da708dd,0xae6aa829e4ae44470b2e,0x17a1623b90b066ec717a,0x7fdce40f9a458f994a32,0xf987589bfcc0630a87f3,0x6d25dc0e8b068c39b858,0x478a54d2b417c499a1cb,0x51a2d84b444b62883fda,0x93bdfb5dbe3514a0eae,0x2b1b9771585834a8186f,0xbdf9c10352f723041010],[0x217e6ef6ac0227,0x56c3bf14c3f7965d58c7,0x6b2df36f541f61a19e1a,0xfc24a9c66a6efedd1891,0x6b984aeaf3029f727c59,0xe631c393af333d56ec6,0xa28b37c725f1736a7672,0x8ed38ad5c5b07551c72d,0x741190d3408438d48518,0xcfea8501131d06d09a7,0xff51fda189b5e3239a1d,0x4d3bda82b20c55c7a28f,0x89e936dda1544cb3e34a,0xdca768c0ec7b77df2b07,0xac3fc4cdbe9580151010],[0x1715db07582b140f443b,0xf65afb02373acbd6cfb0,0x24aa10cf1850c99290bc,0xca4554a8e0f7805266b5,0xe07c4802e04a601ef373,0xeaf1faea2373918ef0c4,0xe368ea5721f3fabdf8db,0x360644d5333e78661fe,0xdbff08bdd9cff952f573,0x7f3216cd625fa97373e9,0x10ddf35c0754b5ccbb30,0x8bd47b5b880694e895e9,0x2a1010be454242c3731a,0xa1c4ae4c748693342a94,0xbe56569e87738402010],[0x8193b1f91543d23a7f9,0xaf9c813995fefe0b2c4c,0xa19f44d56450e6e8c610,0x580862c15b36f3977a8e,0xd40df27fabf175efbf12,0xcb4f528d11699378e66c,0x16151a5d06f923e5c5b4,0xfe8585f61001b8c64688,0xd9abea17810b40aa6d3c,0x312d9a9ff7bdb3f21b5b,0x81d7fd5843e9fc383ed1,0x9aa9e69f7c60fb480e69,0x7915b0815818085cc553,0x564149eda0a2db36651e,0xc129c016e38b5eb12010],[0x1cc77cea73c4b521814,0x2d5a9a84b1812d24fe93,0x45c7d671f738ff5a1952,0xe8163a1b00f76590bbaf,0x7e63551befbca9fcc951,0x512296e4cedfd038f643,0x68eafa34a3e35fe02113,0x92b1359467b24e1fad84,0x6e8b6c3fb2f63ff96828,0x1cca87610ee4029f438,0xa18eb13e0fd3876d5c94,0xdeb68ae6950c5b1e0e58,0x86dc3a34dc151b4da5f3,0xc72148835e27cf65a46a,0xf1315b037fc96cf22010],[0x165ca9235f3f2c602d,0xcfc207b86e09bbb991a4,0xd339f68bee8ce7ed6c15,0x44a07d60d953b4be4a7a,0xf76cc3b51a39f6a2509c,0x5a505b833e9c6284c5fa,0x96eed9cf5c6781aef0b8,0x7b63a3d0af1fc88272f7,0xfcdf6248d15aa64b516,0x9001e654fb4847c9a6f9,0xcd4513a0ec0bb32a359b,0x1c467d07cf475e6dec4d,0x594145d8c6a63aad9860,0x14a792baa51776e1fa96,0x73f91e7b9e4ec6132010],[0x769251f26dbe4,0xf88558252906c276cc81,0x46f7646c4932b4486594,0xefd2141f26e214c01d5b,0xfd00f3d224aaa551fc7d,0x1d335a64988e0b75e536,0xe55c40bceb834ddd6e45,0xc33a54fd085f59ba0421,0x218aa7b657c86b161687,0x85147137aa0365d0039f,0x3ae7e33e862705facf3a,0x603bc7c37e40a653004e,0x3f92bb8a6530ea2948a,0xbc006f96c235cf249379,0x31f3029017f760142010],[0x707d1d4102bb170867,0xc2ebdbc25cb96e16cea7,0x3fa1d0268ab3c5592170,0x58c2ba07e268b7357b85,0xc82541cd0fae7d662c8e,0x7b44a722f6ff036969b8,0x68b2f6b1eecf23db4aef,0xdb68b85f3f3e5a4e77d3,0x205e2671e40b769a194e,0x6761c3995f3e1beed35e,0xe8e3a61041c177e5e76d,0x3a55fd1f428eceb0d82b,0x5dceb0cc3b6d0e6fe504,0x3c363dd7fd5c73958b3c,0x878282f96f20ef303010],[0x18b46c5df7f945934e,0x858d7413dbc173e7fcc9,0x3154c51bd4f262c8c4a7,0x52a986b9bc881e4ace84,0xe123d67185a3828ad98a,0x7b30318a658622475100,0xe615bfad9d543b0cbaff,0xa4d6fcd9a2315b8c155c,0x5ebdfed6a55a39178d44,0xef64f26628ea2b3e92a,0x13000601e487c0d724fa,0x8c313bdca86ad2b707c4,0x3e5eb48788daf38b4ba6,0x58326a048331cc462ce2,0x8eb94699a1352a113010],[0x7bee3d112e0e5d9c7,0xd3c7d5398b98bccd181d,0x185aa0a567fbdb11acca,0xef1a6b20f478f1e726f8,0x6af856b7ead606649eb7,0xcabbc5b0b60c056d1819,0xd48bcaa0754a34e2e859,0x442de566c24f1ba39c9d,0x6b498f90b2479ad6aa29,0x11338c416298233fb9b,0xd0c2d62e056dc802cb64,0x6a4d45a304a2644e0c43,0xefecbdb1241029c7cd03,0x404a2d87717c810b3dfb,0xacb48c57181351123010],[0x7e349b2172c3e,0xe1de07d7280168fdb334,0xfa9cb0e1813512d4a2,0x1c0829b6a8d3565396df,0x40c9ee023b9bfe5cb5b7,0xb84b919bc389363264db,0x4ab8386b61dde1094679,0x69794256b5854077bd45,0xc96fbeab2e8fe89feeb4,0x15ad3daa3d3711b163ad,0x670589ebb945ba5cf44a,0x9a2474cee178d7cfc278,0x9ae247ec57779d26545a,0xf2dc0252ddb627fddb38,0x4be5511a382a40033010],[0x2c0f28b2d5e40d0d7a,0xbb2eb1ac2c2738899d6e,0x8f8a78e923f5e946c357,0x4fc86cd1c14b24364003,0x785427c13a7fe16d59b3,0x43de8e77c73a80883a20,0x182af46d52127059dd7d,0x606710b9ac3477d81da2,0xbf61053a4e0f0435b154,0x27e5a7da504a551b6437,0x325f4143493ab22bdd80,0xdd6c0cae9169ef81af27,0x383e2c2e30c8dd2a9e8f,0xc8217b4cbc6ff61cb640,0xb39b37748089a3004010],[0x31b17cfa72b07dfe1,0x75050046165c07dbbd4c,0x292c3109cd033462a96e,0x353884607d3ab4e4c60c,0x96c1c34d7033c1f70577,0x72a5b6dbb9c8f2742049,0xa7149f44f2c10d3962cb,0x45e96c0a8aded50c2e0f,0xc57302fe3f166dbe329d,0xc0ac764596e37258872,0x3e66c480e630dc016826,0xd6532451f41289511597,0x9b534eea8066d6027a88,0xcc05589efc4caf0c6d50,0xc720c5c3f08fa8014010],[0x1a52fc85764af57cb,0xe51009ac055cadbe1967,0x15c0b6b7b7623103e65b,0xe1ce971f1461753e9db7,0xe9bdcfbde0d05e532ec2,0x780549b66c0f80bacbd3,0x1b2395ee83e50c2c67b4,0xf873f6cb006476f2c5f4,0xa5e31e5dd84a70a01386,0x69c12b6c03a8f00a3fe3,0x7bffe331a53396449d8e,0x13be48aa2bf1682ec1cd,0xe8675674bf9f30b2ed5a,0x47715351383084e149bb,0xb74b81195ce182005010],[0x140c1042edf98a0b34e,0x2b837bb21026a963c876,0xf600328f60971682d7aa,0x99a7e8fb2d833379f2aa,0xb6a29421297b01febde9,0x7c78a198c128b51ba43b,0x417a23235ab8e8f96163,0x58d5b494fe51756d0cdb,0x6d663593d6ff2bf9cd41,0x4da49b5a381d322ad18d,0x5838ad843e1014e7a9ba,0xc2ff723cadce034066ec,0x5758c1d3b6f7623236c,0x2737d63108deaa50214,0xadd6db4bb72b0a100110],[0x11de53e897127078fac,0x6209701bec7b01904456,0xd2edb9d35b548cefa6e,0x65e3b6a93d702217044d,0xcd92990aa08fa7acc2ca,0xbc11f5305016b8d684e2,0x77040e39d2c1cadf8d8a,0xd16c1c68f435f45cf93,0xcad1066d54a3f453973a,0x10a8f55050f7de1e8329,0x865c783e58acc99fdc3,0xc8aa9ce753d986b905b6,0x9dd8039e790174e62c39,0xe4f95547e296a2138359,0xcfbf88ccd8c1bb110110],[0x4d6e976b74f73903b0,0x4251c9ecd1f76e16fdaa,0xbc4ca2a1e2af8c056bb2,0xb179e1e9e7bab2801012,0xd91640c15d28f105501a,0x502755624cc72082153,0x187360108601f3dd49b5,0x32336da5f3c915b8f92,0x81cc634e9932125dd3c1,0xb360240b77e5d1db98fe,0x9f996d69a2c3875dc589,0x10ddd85bf49a5bee94b,0x9e0671cb92b511a27398,0x6bf42dc81f687b15c2f8,0xe0e50bc35f320b20110],[0x60ecf1992b994296a,0x1514acbe0fcd88c38b1,0x415e6a2daac00496f96b,0x197c19575eb3a280af4a,0xe9491948fc13e856705c,0xb0fabc89c05b470a9ae1,0x3673fbb210746aad8e3c,0xceea03c636850411d3b3,0x513a64e8583d63b3cea6,0xf83a23ab3305b71331d8,0xdf0a21c1be6e90b63563,0x9d5141c2169cc47d9f8e,0xc1b0d98d6ac9817eace2,0x6c4942a551cc5c3199f6,0x90585ef2a0be5e130110],[0x2e295c735a2374,0x427fe52c44764a9ca948,0xf6ae73fb4261d373236c,0xf4f78615e4fe8a6b0ebe,0x257d3eec7b9017db0fe0,0x3ee2ffb262e00eb4976b,0xc3d862ddde5ada3c0056,0xe83bc4b32e4d1b9d1d9b,0xe991018fadb9fa4bb201,0xbf00bba787771dade114,0xd4c463ed3243a68a149a,0xd693eb4c3f07e3bde007,0x7a25841f25d84b350801,0xc49806703438d6117e5a,0x1d12ec00ef29a0040110],[0x24803e008e4f7d1ee20,0xa385e1f3db2fc98abd27,0xbe67777d924506d78d3c,0xdab5bebd862bf42cdda2,0xf902cdfb641c7cb431da,0xd59f6427ce471cd81b9e,0xdeef77288a54adc65c21,0x6a088b6cf588c50b5b52,0x2e4fb35b5d9c98f48c99,0xb931e5ce3068ce2e3f37,0xf7bb1b12a35f6c6b0607,0x7c6fd79809e35dabd496,0x6502a4537a9fc87e222a,0x5047aa45e53a076e31de,0x741ba8bf5b4e3e101110],[0x70b4b6e625f70abdd,0x7a9ff95823bb09709a6b,0x1376451eeb92972e9370,0x2063301a38f272f9f251,0x42bb42f63d1f976dfca2,0x177777f7baa05f9bf541,0xdf14537cdf4252a446c5,0x134bb161789819a4db21,0x660c5becd96d28c917e8,0x551422ca2f60142d3fdb,0x9cb964d967f797905cc4,0x5420db0798fd7b8d6048,0xfd78eccd744131b2c456,0x89cb266ecde42cd41a5a,0xd9d9856bf3798fe11110],[0x122e1816c311ae754,0xae157dcca9e7989b27ce,0x733363417ccdea149b59,0x602b12dc0aa2205f2ace,0xff440025ab3fbb3bcb75,0xf25085f7d586437a6a77,0x8e753d95b267c9214876,0xb89dc87dbba223f37a4a,0xcbbba8b2de44af33d8f4,0x904e50467fe076ccf026,0x28ef5a73bce653ba5cd,0xf16e0d93433e5c262b71,0x25075dfb0dc23bc48a6a,0x7b26670631c93b667d5c,0x329955a5ef3fbb021110],[0x30dc964ed51e80fce7,0xf27eb83aa69999f0c83d,0x7b0990577a9922c494df,0x14cd5167f55f8fe06b6a,0x7b428e656f8f12d22edf,0x1a153706c1052d3d404c,0x3ba21796cac693275d7b,0xf4310552348a7574ad21,0x2613f2d284b6e353e931,0xb7056c1b0b76274e75f0,0x1a26ca0ee98c982add11,0xab0d4eebb95ded84d97b,0x1fab9baf03d89c086d63,0xdf2cc91b1cab8fb941a,0xf39170032d3c05102110],[0x1c954b5c52414e3e4,0x79fedd3e1e0f5d6ba26d,0xf9f9034e1c1c01764048,0x8937d2a48091b5629e34,0x8b1b95e7db602e299ea5,0xaa4150f320b9af8486d3,0xfeed720609d353c64fa5,0x938634bba1d3a338592b,0x45cb96527a69faa1668d,0x9b925a37e1e38bd7ab16,0x75fde0a6031739e81eae,0x2b917367da0417e1dc09,0xd5abc1027ccabafc9901,0x230e2740d4c569a657f4,0x6370a8a060af70112110]] ++
  [[0xbea8b590b44aefc7,0x4187d26ee8fba9f9d60e,0x66d0362b02017f426732,0xf4ff55bee69888e1a05f,0x9a5e16bb2ea35676d688,0xa17af59339dbb482f33,0xad5a8c41cf36de97fee6,0xb55b58a5d0f56b95720d,0xa7949da3ecda69767e02,0xb68402e4d8b13f033f25,0x1379cc0864fa1ac9216e,0xb7f02166600ccbb876d4,0x8cb641a3ac0327ac7900,0x10134c7af26420b4b970,0xf605a5779bf2de103110],[0x241b01c1e493b7867,0xc6c63d30947ae660d396,0x1e342735494f6c77b94e,0x535b40af12899fd491ee,0xbdcf8e684f54ccc3262a,0xd74f620f461b923f0242,0x44be6fcda19a1e4cc31,0x2b4181f6568e6602cf89,0xd513f4e3fa07fbd44668,0x322867c2d7787975df76,0xe733878e0b5a774345de,0x2cd6fd93bac1d6eab97c,0x8d172e010a8d08148f44,0x7ca439baf5d0d4a71c6c,0x1f3778dd8aa784f00210],[0x174414243e0c32625,0x5a3aa17735088a39111f,0xcab8fd3e32846f85bcfd,0x13f0ca4256ef98030961,0x21d0e68a2013dabdc31c,0x98afc5f08f550784611c,0xfe1c756007604aaf6b53,0x5a196b4a37c4019eb42f,0x5e4f4ae43f2a2a39c781,0x30dac67e3abaddd19384,0xae67f4599452db030669,0xb26c61c11a52c4f9e6be,0xd1016eda21b8c056df1c,0x9049e095add53d4eb7bb,0xb5cbb5c63ae1fd110210],[0x4712c6bed6d366d94044,0xa537a0a610f7fc58c805,0x8d8cdeecd24b34ec0fdb,0x23c3f142b27beefdbf0f,0x5a2d57d852eb88bc3db0,0x425ef46d72581a524abe,0x94630ffcbf34c7844aa1,0x606863ffcb805653938a,0xe95f7b403c1bcb59d2b3,0x7d182b8710ea3032c764,0xf9ccdea6bcf28f286e6b,0xe37427429a3d0e717052,0x8c293788e003dcf03c1,0x569f0be2437b1ce776be,0x24a437ecd42230100001],[0x4ced6b88adf89e99b72d,0xa6b0c579420fbfb22d1,0xc78d72760c9fcadb46be,0x86a496a9b2565446aa0a,0xb282c13b63c42d4ae7d4,0x9054c092979e3ad42bd4,0x629dd541310f0617b591,0xe1bf119b6b038c3177e2,0xafa358a66215677d8b5c,0x67d526438f50f32afb04,0x5e9edb4db71c317608a,0x256bfedb8a47560be446,0x5eb74b4248f719b1ad6,0xfa7bc7a1194a4a0fad86,0x4fbc9b770f2aa2110001],[0x1c82745355a4d7933795,0x33687825d4a47fc500fa,0xc75c38d6eb74bc246a60,0xe78c163372a8fc82c25b,0xa9a9d52daf2e5f878f79,0xee14511705bed8ce85e8,0x6bebbbc10cd7ee5040f,0x7b0d9116e3af99a83269,0x66a122d22e8d920dc7e1,0xd62982443935526fbd43,0xcf401c3104b52419fda9,0xb0cc984d1c30052d5a6e,0xfaaab31e021ad6e65580,0x85ab7448de8fd61b9d8c,0x2a0c15ade67d6e120001],[0x3c19d5bf51109a36e76,0xa0bbcd4453d86545111b,0x4abc0439ba01387421a2,0x70af1492c91a7c97e025,0x403ce3f300f39ee93918,0xc64b484a75fe485a23f5,0x3e7f35ee072983b45388,0xa8ec5c0c81af3d205a3f,0x10e507f4200e7fb98bf8,0x766550b34ae4124eed59,0xfabf9f8427e432315f40,0xaf03e2caab646d7aa3c8,0xacae66fb9a0e429cb217,0x722f852ec99ea368ee0f,0x519b52e3689d03130001],[0x289d1d673d13f27068,0x2a2cc877b6b5004c08a1,0xa2c089c68ff28a7e36cf,0xfe6fe3d7a0e0dd013b28,0x2b4c2f395f95add1afca,0xfdc03e7cf9288a0a15b1,0xef2a2fa6b98b4284345,0xca12f18e915dd0df0769,0x72e8cd52e665f013429d,0x3059085d0298b2714a9a,0x51941396c5a2ad759f71,0xc334bb5bae6ea0528979,0xf7a268239c7a9f2e4ead,0x70a37052cc0d898f557e,0xe4515623b2fef0140001],[0x4cce4524d16d4f5c,0xcb4913ddae8db92a9ce7,0xb67a3ff2c71e8ba7e1fb,0xefb4f3f0f4e140d6319b,0x512054cf5f84b2d2250c,0x238fda0be48c57ce45c3,0x16ac31d473a61106d2f7,0xfa53ad14d32fd7f934e2,0x35b303a4fda278d42011,0x4ea0b0feb7c92a886399,0x74b624fd0c4276b8489f,0x4f976d8e4ccf5be9e8df,0xaea205d4ff179dc2575f,0x885a489fcfdfe467c199,0x6c047137d2cbe0050001],[0x28168a0c16920b3,0x40211309de20884e2e4e,0xa7dcf2ea9bc5b8abcac0,0x2d52fd3504d963bd3ba9,0xe413ddc6f866722c29ff,0xeb2deb36915ed863ceac,0x3bbaa969dca266485b64,0x9e388f812e7c532b4f7a,0x618097b68109386807a,0xf7a4208858860d10b9b3,0xf0c5548fa26ec8431d8a,0x9dbb3c001eb85ef05519,0xaca5412f640c306d3bdc,0xd57979246fb6c850c4c6,0x2dbac5d5f4dce0160001],[0x1f75f754fb8acb,0xbb64e72c9e6890e7b8,0x3a9233e4857315718996,0x7c359e6a335ef871e3b0,0xd385e7c15774d1f0584d,0xd6903f7db745f07b9145,0xf88904cfbaddbb7d8877,0x4e3d89f86d234b01c67e,0x6de9cf63d498bd2c2506,0x7fb2f4c2b825d8b3cb0b,0xbed435255a3215e4cd7a,0xd1ed96f8fa8affe94201,0x344e13f0a0eee503c4f,0x78070ae636482147f15d,0x36f14bb39cdb20170001],[0x2520b4fa816a35f15cfd,0xb33b7971e075101caa99,0xfc7e8d6ed396217b6ce,0x6fbc273b7afdb41a422c,0xdf1d849eb1c951bf5f1f,0x122d31b007f8484f187f,0x930b23f565ecfe34c5f3,0x7d350227774573c543c4,0x7b07a63fc855207261a0,0x3e40afb9fc805e2a5567,0x5b6afa4cf2156d858849,0xd2b0e28af8d8e38b8dc6,0x5eca62ed3d339dfd3ac3,0x7968fe188da39d189366,0xf481caacca8c1a101001],[0x1c356123acaa6e71573d,0xa02576697e689d7e80a3,0x655032210921e6daacf0,0x821911f957882857a221,0x805aad9135fce19226a6,0xf11017c9cebeae80e59e,0x83913d2b7fb5f4e56238,0x91af09333c38327a5d77,0x2ed749e2faed11e77c4d,0x62c0cec03775f836ff76,0x9f5ab85409183df928b9,0x4ecf1a9d9ccce016ff08,0xdd9357a4153fdf73abc1,0xf29d201ef363fbe08885,0xe9361c785564c5011001],[0x187ea2089e17611d2416,0x8eed1389f69c68575104,0xdfa8042b2368373ac5f2,0x68a3cc183ea237a4562a,0x8b8598b4e5be11f6bfd3,0x4882ee325e877597af88,0xe8f90c5376a6dae69d5d,0x95a90480178c12d0e4b,0xcb833b5c49c6871b7fec,0xc051e3efc337ba0e893d,0x47f8374b38dbcd1a1c38,0xf9e57b559b711763741,0x7f52f317695ba347ce7c,0x4733172a592db476525a,0xdce1cafcfaef2c821001],[0x54d05d049ed086e560d,0xb8f843dc31c97be16a53,0x3fde2e869a0fb51078ab,0x108ad9db6086eeceb0be,0x1054069688e0397d6697,0x19bbe2da787ec5c121d8,0xc1da0a7cadc49ff39ba5,0xc478821f80f92076806d,0xc0f511324bbf06de27e0,0x2cf81f17e6f72618c272,0x6201bc0f8ac71daf64e3,0x4635608ff8c73174d1f3,0x9625bbcd5ef87f2032f9,0xdf510f6abe6213e0aef0,0xde07215b600eb1231001],[0x6fb293ed7f979e2b6d,0x2f3336b1ce4ccd00d5d5,0x59adf65c316cd3d26e0e,0x97401752d1cff47a9366,0x25cffe4071d90bdcdfea,0x20badfa46108f62768c1,0xa0cb31223859cccaec5e,0x6f0aab09a9f86e7fd50d,0xfda683f342659ed994b7,0x5928d481c712d3037e69,0x948d3e76620f439835ee,0xf49e8030ed1dfb39175b,0x6b404dbda0e7ccd29b56,0xd7415aa38e50c871272b,0x9ba151d9e0b75b641001],[0x3b0c6d8bf26f9e0b8,0xfdc4df07bc7fb3f0b46c,0x19f2f1e998ba7b2a8365,0x5cc8c557311da2f29423,0x770bf869bcddeb1b456b,0x2df70ef93aeac8e496f2,0x5fd231fa8e89882cb807,0xad277a4d6ff61fb6baff,0x45081f3b820109c19adf,0x5b5b74b0152c65c4e2e9,0xeaf8b65249a953f0e5e9,0xad49493333fc71f0e5fa,0xa96379ce1c7d3b13d867,0x87b88b6022261c3bdad3,0xc3546aa126f07b051001],[0x52d4e3a5c7d663,0xd92fefa0c67e870b9853,0x79d877739b30132dffc6,0xe5f14456c54e77c3e8b5,0x38da3f9774657e354db8,0xc91e7bb669f33a841856,0xb18306b52fd2cf19e135,0x80e8f9459590a7e948fe,0xbf05ec0b5f41b0720c9a,0x67f0a1964f53c70261ad,0x6fce1739880e07706c95,0x7c2417ff8916cfb6ebe2,0x4d67704c7e16773172ef,0x8dedd642fa1d3e5e8f1c,0xcf152ec0d57720161001],[0x903836e41712dee13ff0,0xc53a22071a8d7ead80bc,0xd33be0e930f7a7eb61c1,0xef7c4f98ffcbaa39a538,0x2e43a55353267c03275d,0x4956de9c98054013b52f,0xfefe85fe405f4eb5c440,0x398f475fa1f2b03948b3,0x90bc96d4652ced1aad0,0xe8fc0a37c4c6eb936882,0x427ac7aa7f4a97063e42,0xc3a04cb965c63ac9efea,0xfc2d5ce1fc042bf61d5a,0x71e5d67f4e4e52d9011f,0xeec5711d0ead58802001],[0x3acd016a11ab1e59da2a,0x8e439a9faf9ed64fb11b,0x1648cafa02fd6753430d,0xb581b11c7687be1d0d02,0x931130adba59e5fb1aa3,0x22acfa3839ef5eb70a06,0xcd7654cdcc5b61dc1d09,0x9c74726b37dd1f17cee,0x4aadf949bb5138df1fc5,0xec3f8e56bdfb565e0c5e,0x3be119bd1e69d4be621e,0xe3aefaa1a6b4a4dc4176,0x3d0af6b6de6f9bbf0a9f,0xea30265ee536ab99e1be,0x7fc96866c6e8d1012001],[0xc3ebacfd4ff33873129,0x9bf545f61607da76c536,0x6ee695c3f33f3787149,0x2d1254310be5341efafa,0x9d35dd054e04c3cd1f42,0x36a586c9a48cf8ed7db4,0xf0fb70e37dd2dcaf00be,0x52686fe7538b78d9f69f,0x18144dd908297109a6f4,0xfa6b76a0f045e20b963d,0x9607f66200a036637c7e,0x8c6c763757f4cad3e53b,0x741b0c7ffaf6f03db6cb,0xe14a2ef7901fbbd853b8,0x1a41049b93fc5022001],[0xe2c306dc11a2b81ace,0xcb19fa2f1e96d678d238,0x8d023fe4c40e4b16f599,0x59705841ee0bc3fcf791,0x46675af893bbbc718755,0x438e48fd3c7d109ddf74,0x8348c46580b74b3ac06f,0xaf560e19dcbaf7ec9dbb,0xff2d7032c783001e490a,0x74cfd4b11d3e39caa3d9,0x770556ef2115e22eb542,0xc5d15d3b907d76021d67,0x64e46cc8c416036b5ed9,0x30f1b78c6bd247855f4,0x6c9b8b4b1ac011232001],[0xfccaf6853fdcca6d,0xa85d00e584b5d14b0c47,0x4036c82c68f3dbbc1bf6,0x2e5c3b2b6688d66ce4a5,0x6d65e38ca39c84aca26a,0xe8ed96d6dd9f7af6139a,0x2ee491362c98f99b548c,0x507f2ab25c0a9684261e,0xbe95d318dbb5643dca31,0x559117d35bc2ce2b154d,0xbfeb3e06c50303bba317,0xee859dccb58997867a9f,0xc4ed43e23d4cac79292f,0xfcd8f948e22753e0b4a0,0x3deb44c42e8025042001],[0x769251f26dbe4,0xf88558252906c276cc81,0x46f7646c4932b4486594,0xefd2141f26e214c01d5b,0xfd00f3d224aaa551fc7d,0x1d335a64988e0b75e536,0xe55c40bceb834ddd6e45,0xc33a54fd085f59ba0421,0x218aa7b657c86b161687,0x85147137aa0365d0039f,0x3ae7e33e862705facf3a,0x603bc7c37e40a653004e,0x3f92bb8a6530ea2948a,0xbc006f96c235cf249379,0x31f3029017f760152001],[0x3e821fab17c767c98a9,0x1afb75bfa8bbacf7bed6,0x514d1e26ce56b95a9d0e,0x245ebb6991941a75a677,0x8aff6e61137c570ee3a,0xc2fbbc4ba10f621cb888,0x9fa9c41a12d3c494becb,0x48e6a3d82e2696edf3c5,0xea48f0c4bf42a398b1e4,0x109215feb71bc739543f,0x41edb0af66403d2fa6,0xa52f1d38ec54688b8aaa,0xac62f31c1db33a765989,0xd50b9356fc882ac3b839,0x79868883e3c857103001],[0x81f8e66ad3aab107fc3,0x4fc5a07cbc95a3911512,0xdda8f60b60fd9d6d9519,0xcd188f716b90e6b57e0a,0x186da910627e65c11735,0x4ba4020ac691dbd631b1,0xf1733c0b7c74f4a5424a,0x468b86ba20d6415ec8d2,0x4f86e0e9d42491f73871,0xd22ff8d80320b9caaa2c,0x11d7633af8039493f3ee,0xbeaa24bf7b6574c519bd,0xbd38f05995ff238710ad,0x5702e3d4b0e86258c6c4,0x42f43680be5431413001],[0x19743e4dea1c50069f2,0xe49747cbc08f4e7a43aa,0x5522e794d18e4d3ae834,0x8cc8568833b0ee9866b5,0x272f64f63e2dbd09f853,0x302f606042c468e0adbe,0xd34d1609bb65bfdad5e4,0x918601020ce0b28150b,0xe3bd30223bad9c4be316,0x777a992264de94378c67,0x9fc7d3bd5b2bdc12ac98,0x95cef1d152f95d5be49d,0xd3cba9f8d085561089fd,0x77199b5b235d90d58c54,0x9546467a670ec2023001],[0x114a6274a992fd8159,0x92790ab424ff6b8f3327,0x3e7a473978c67b7e001,0x4b4c42df70713df32ab1,0x15eb7c5306069dd6ca03,0x718f56a3e08d37dee1,0x7b75b3df24b00434e861,0x640f56bc34942375e196,0x432f8a8a54a7f9db2c01,0x91dd978c3406a285fb05,0x12cbdf90ad1e0413d093,0x116eff1c57a00d6221b9,0xfd72e7df1631b4395d24,0x8eb1a8af5b19e5c53983,0xe225055fb89e19033001],[0x7e349b2172c3e,0xe1de07d7280168fdb334,0xfa9cb0e1813512d4a2,0x1c0829b6a8d3565396df,0x40c9ee023b9bfe5cb5b7,0xb84b919bc389363264db,0x4ab8386b61dde1094679,0x69794256b5854077bd45,0xc96fbeab2e8fe89feeb4,0x15ad3daa3d3711b163ad,0x670589ebb945ba5cf44a,0x9a2474cee178d7cfc278,0x9ae247ec57779d26545a,0xf2dc0252ddb627fddb38,0x4be5511a382a40043001],[0xba0d47ec691420b7c3,0x3569e12430304828f434,0xb2906a31bcefb074421a,0x6eeacf82afa829e0e9a,0x20afc7a449d3d891d10e,0x7b7443cbff321e62ab48,0xf2789f8b21320abfc698,0xfbc3fd1eddce4c6df9e8,0x50243055795eb051c916,0xa5cd94188f5581dff509,0x128c44b4853cb1dc12a5,0x78625f6913cb917473fe,0xb44cf18532e54b6d4516,0x5bf0a64533c728280a50,0x7e1eefb7611f0c004001],[0x6f640c054fbe631b11,0x67889650dd96ec550a54,0x4a2805057cac0735cc1f,0xe2359f4b5c4549c41375,0x75ef5a0d6a96815031e3,0x42c86802106ea0f76e3,0xba6a323b2137aed5ce40,0x65dc4607af8e582b5a35,0xc6386876565a8228bd0d,0x77dff59d4bb3c3b8642,0x3168a3c791c43ffb8190,0xa6b38cd00b6b906e5a1d,0x4a2582b4971dca85ac0f,0xd34d59b45139c59675e2,0x68516fdb217d63014001],[0xa8fd1580513d6ae81,0x389c0db07fddd667320a,0xe464ccb9f671104aec6a,0x8ca0a0aa9e913db47a84,0xadd15df27a4c795b68a3,0x8938d34395f36cde801a,0x25dcbb3b922b99eb10f0,0xe47cbe0ee165a3b5052e,0xd65954a37ae14ec06b37,0xfa3b496666476eaf8a8c,0xd756b2f7a553ede26111,0x5d28ee88380fb7f8d910,0x7599e25bc88b5b5b76d,0x1a9c274710431af201e1,0x16accd1e488f22024001]] ++
  [[0x5089b8c6c20de4594,0xbbac3cc49310bffe94c5,0x1ea89cb6cb35d94b8dda,0x63abea1d88397cbd8005,0x4d678d9ddd8764e8120d,0x8b7d3d51b4c552c99c15,0x6ca2dce9460b2200d3cc,0x49c136f29b111c69ef4,0x3b40c79251099e156c6f,0x44f02a92f22d85efe223,0x24741d8784cec7a2f296,0x439b714c4e0741d1cff1,0x2679040ed97acb37e97e,0x5890e679080fefd5ef8e,0x13290cd404ec22005001],[0x1a4094f6f55ed1e7b,0xe06b0460219adb4ed797,0xe30259957c0e1540abb4,0xa42991553909631ab1c8,0xfaad85c2b7b87ee6e11d,0xe40f854c64e35a22e415,0xbdfda1d5e5ec9e059a19,0xebf273c1f0ee240f231c,0xd2473a629dd53978285b,0x4562a650bf88987e686a,0xcaae97528cec3f2f2d46,0x55d35fa579016b761732,0xfbdc879563cd9f11a4ad,0x6f6475a12bc09f59bd1e,0x6c0a7ad3f08b66015001],[0x15532fd79efad65ad1f,0x67a4ae2488646b22233d,0xcf542615b327fdded8c,0xf8e3f616b36e3d70983d,0x4eb716cc4c81b64bbef5,0xb300bf253c15076829e1,0x86bc649d78dfed622a7f,0x36857a05fff2c831bfa7,0x6a9a815af084a4af7750,0x4e4ae127442d038d5f73,0x35a0e9937c08393ba30e,0xaf5876793b0f192e029f,0x288fbee9b52d224494d5,0x295e0e00ac2df0fb0faa,0x9d5241ac7d0277900011],[0xd0135c6c7e95343713,0x3129d8178c887c3b9284,0xae8cf2f1f0a0b491d1ce,0x810d5c5f441a5a927c88,0xed3ad3c49fc5b5cb66b3,0x7827470ee7251d2e5513,0xb0cbbd7ba482f3378e0a,0x8a3b46a409651f88e5f8,0xc8a76b8956bfa8b99c6d,0xa7dffb6a7dcf772b458c,0xdd76ad07052290ceb86e,0x85b15489411da02e1dae,0x8c663cb3e0e47aef0fa4,0x1d19b62eeccd2270cb18,0xa3024cda9548a2d10011],[0x24ef737a0d2a3cb618,0xcc28144cf197457ad320,0x8cb2e84cd0fffd8860f1,0xe3c55cef226881e202ed,0x90196792ff21784d4bbe,0x488097aebe095267e34c,0xf50e442b7b32b7edbb83,0xba01c47ee3f2f9f89649,0xc2b2501403dad1acf5e0,0x78ff6252bee72240a46e,0x2415d12a4d3fd437c31b,0xd29e70aecb58094e647c,0x2f6036694920c5a04260,0x5afececef7b189cee64f,0x8575cf5e7931b2120011],[0x16e3e5486e87d57fb,0xe34a50af0b4bb0c0fd24,0x83677d2d5e7370bacf58,0x99f55233d780d7e4cd63,0xc15e9b4103eb225cdc51,0x6ccba787fbd7d20a52f9,0xa23eadcbf6a28e8a73c,0x913467ba91c2087c2f1,0x7fec8e58e77f26cf0b09,0x1eaf4fc16cb0b34b6c71,0x2fbbefd37d7b2290b647,0x570652efaecc99f47471,0x3d9a204c8320935405b9,0xf13e7794d7435540cfb5,0x489eb563221d6f130011],[0x199a65f6a009b9,0xf25ba131e122bb33f2bd,0x3b2dc65ff707197e0b93,0x60414a8abb3062c0b6dc,0x523b91b0ed818fbebb1a,0xa7e66bb7b48288ef6251,0x30a8e7f71cdf2a7f9741,0x6caedd880817a40865ee,0x95a4539a413753d4cceb,0x3be18d41399c788f1cfa,0x5bd02db76a16f09a988e,0xb4f95f5c23915663ae3e,0xf0ca5c3d3ed30121b292,0xb9af6e775e3057101300,0xf3b4d27f940a0040011],[0x9743690ad3b02abe54,0x82178f9b7cbf3338578e,0x36f57ddb23b0c127c21d,0xec783f6c279c079b194e,0x14128bbbbbca113ac3e4,0x9498fe815f5ef6584f9a,0xf657552938a756111116,0x2621c3d0aa697a2ac8a4,0xf835509eb5c818e9bde3,0x52b02c367b7eae63c19d,0xf161f7ca5aa81ec5bf7e,0x56c479175013d1105dc5,0x1b29b9094ca2322f03dc,0x39f6af0d39e7110b9689,0x9dfbb3afc746c4401011],[0x4ac7a49bd965a42f73,0x4d48e546c1a9ea6e5259,0x2bdb5d2597c071a8d962,0x3159e601481dcd2ec3b6,0xcb5770cf319da389498d,0xe9ff218a61922588f8c9,0x583166b6b13000e23676,0xde8667637e101165336e,0xc787db65f993b2bc1c2b,0xd3e2ae7cbdf692e7885d,0xd7d8ae487d30487a1303,0xb5f5bd97f96cc69a9650,0x1670690934d53686d796,0xbb487bd9c7de76a04f7f,0x71789e70c82a43e11011],[0x23f8eacbdf1807a91,0x9218f38c222022fe24,0xcb1ca2e7aadff286d7ab,0xe851b16b739c41cef896,0xccbe0cc0fd702fb6c762,0x8e084d00fcd5f28d73e7,0x283524cc8e77bfcd768a,0x51304db7f10b06da2131,0x1f955bd05f72f6927d08,0xf7fb64b0e496add04f04,0x80399bc47d7089d04f04,0x20c5256b35ecc74539ad,0xc102a46088b33b6610a7,0x1b8c5a85955338a2bb37,0x25ec0e56cec1e021011],[0x4a5ff9b59421e595,0x7542679ae3f65af49d6c,0x19da573948d2b87a55b5,0x525563ee02748064a33,0xafbf807d4a57b8bdf1e4,0x7a074610d2c76b5b673f,0x9a8de5ba4a6fcff76bad,0xd86ef9c6291ef653f208,0xdac3c111cd94fc71e765,0x8bdfc4f0fce08509bf09,0xda8b365d27fe64ca5212,0xcdf38131ce68026efd4e,0x15998c15c160a750dbe9,0x90027adc09503e3b470b,0x95c4d59017aa2a402011],[0x200e29c82fbbdddc7,0xc01592730bc84b84f043,0x77fb968d5f88d11944d3,0xfffae2aeeefbf55d67fe,0xfbd8c4c204ad3302cd30,0x7a376e9efed5659e67e5,0xbbf386c6e11b47da0829,0x8090d9614b47ec72832d,0x4b543c2a94419a579e71,0x6d0127b68de91a2cb248,0xdd16e3b7e10ae2402875,0x164c8a3f2c82e531f261,0x38b7e238c21638aa1e25,0xb939a6d0664c35311e56,0x21acd6fd3989e7012011],[0xbfa14642c4d04810,0x2dfcb1e3e3b7d460fc88,0x9b578c23e855ff286c14,0x355fa32b89f52fc3be99,0x98aebbcfdfaa57f485b1,0xb73133ad27be63c38e28,0x2a7b491201f9b8ea79b3,0x7e4ed1be6f3a0e73871d,0x722186011d56ae3b9767,0xb2cf2cadab1270261d39,0xcf685ae45b2d947866d6,0xf9eba2abd19d92806565,0xfbbc457059f5cbe5abaf,0xabd7412c0d4557049e13,0x44c2a5fc45dfdc003011],[0x4a80cc4f4a290d3399d,0x2eb0971035bb60bf7080,0x325554a277b78c30e205,0xebba890ee17fc185a904,0xbd858eb1e4d49c6288ea,0xc690975c3a8c8577c3d9,0xbc4549fb4d06c9a7b6ec,0x1f3006f2ffb98b8eb301,0x949e22557c3262d2eda8,0xc2efa5c78f710f0a1c,0xdc0a846880696f872202,0x96be2069da9527e2510b,0xa74eb812739e9693c568,0xfe36afa0601a109fb136,0x688fe4716c196e100002],[0x35cf8435c3d6d9c39b7,0xcc4965711321e13d0885,0xb24347692a826d9a9bcf,0x5d0d49d1627df9257197,0xe1d6c041a436485c91af,0xc84f6bff383abfffeb8a,0xbdd27c9bb3a476e9e88b,0xb3ac2de79778cfa22746,0x39861a86bb877471f1e4,0xafa15459fd7824471206,0x16cca0846607818b38ca,0x65540b1403d52a34ce77,0xe11a891c0aa7742180dd,0x75ef6023b1b8532b96fe,0xedd953bb8064c4110002],[0x94c18fe78c8424c73c,0xfaf4598bc4751d0f68e3,0x74c5a3af918730c64189,0x5af57b54ee295fc789d4,0xdbfb74eb2ec6ce66ff23,0x8d8672095a974a974e94,0x6e4108b3ae2ca621fbbf,0xcb7805f6a834557082d5,0x3ebcf8876d40f05d91c7,0xf093bf893b04be8820bb,0x51cb27361989fd590bc5,0xa91f6829a3f98ef2a129,0x323a9d99368f9a7f3fb3,0xe72d9c840292edac9210,0x45eb2ec96e3b11d20002],[0x94bf934faf9674053,0xe35206858993cc7a8e03,0x485513a89e1bb5d7eb2c,0x68271994b05ca292bbcd,0x77fc1ee858a7f1b4eaa3,0xbd24fdba937ce8af9c76,0x9961928c53c8e8e7afed,0x201c7240ddba3e0cee49,0xe722948214032625730b,0x6fcd390c6fe780fe0d50,0x42e8864851735788c190,0x1b8a49fdef7012770b30,0x500d05d2efd78ea7d681,0xfd06b2b8208f75d74303,0x8d8def6c36bd2130002],[0x40b0173100b855ce,0x9519ad1321a351d7eaa9,0x3b8d8caab791a47d3534,0x56500fa04d0429ca55a5,0x782538d1aa1748352c4e,0x6077bb83ea9db59e3052,0x2dea0c1693042978b5f2,0x51a75d57a74deff8a159,0x2b0a9ff00d5c00ed47fd,0x5e20b74ace473f464388,0x3115a0f40368a63ff730,0x5bdc416faacea1233a46,0x6d82e8ffb89dd2d37779,0x3e0fae762a1ab0569bfd,0x6d2cb0d0d89b08140002],[0x1a21ea0095a730,0xa7adadc1d625818c3673,0x148273b6cd243e82409d,0xde64cdf479808a8001c2,0x98dc5aa643cf5b900605,0x3c8a7baed687dcee6557,0x3d2e24a47975956828fe,0x18fdcf27785ad28776a2,0x25df8d36540d3e0d1b2b,0x55df1786580e47605b77,0xcb1976a936c5059062de,0x43b217b9923c6f6bea76,0x27ae7a7532a4a65873d8,0x8bcc7fa5026c7f2263f4,0x90310cd05534a0050002],[0x3926e309c74b6866a21,0xc1fe04ecf23e0ee5bef0,0xb0e1e0ce46f8d6163744,0xfa533a5f826a26b27de1,0x8ab2274aa691c0c0c9d5,0x6dcb4959b888ca7f098f,0x35869da6d75e2db79b8b,0x9312474d49a37ed0e70,0x42382dfe7d0b4811b966,0x5bcb29b5a008a261be57,0x70bb309dfe0f1b9e00f9,0x19c3dea25e81292ecda5,0x9502a07b681385cc0aa4,0x7e05d0adf36007859d7a,0x37784cfd621e60901002],[0x21e162ef2d40bef8f8,0x29fe7cf5ee0da0d2826a,0xd6add34b4f34370d8a5c,0x580e571ae1567e3d6230,0xb0f49321bb0656a1c9c9,0x41d7df5e4f03073cf7a1,0xdc646adb676fcd3dc403,0x3058caffbab65e4892ad,0xdd540e7d43945d6bc5cb,0xa4f5a66b797c672505da,0xd05dbe44724631d84bbb,0x50520510738dbda8f485,0x9b9e9b72f7082c7527ae,0x79887a0f55766dfc6276,0x54f73d2677238d211002],[0x12f0599b1e7ea53eba,0xb3e3a06d4803099d9f1f,0xd667fc763e40b36a0c60,0x80c869b8700b6760718,0xa2702590e4bd5c6c68e1,0xd33b172a59f4be93f2b9,0xf107cf5e3a7e11633388,0x2a409776e7c25c5201a4,0x9f5a2fff1412329cf5e1,0xd9248bcc7977aa0ab4fd,0x7c7d28bb4f71f943c816,0xc016c2eccbecf58f2097,0x307670bd0c7b86d1b29f,0xa2bec0b63dfbbe3a05d3,0x8b155c37de31a6e21002],[0xec91ef65f1215dd7,0x69f73d16c2796d84f2cc,0x6d748dc9d935a2c7e28f,0x10353a88e1ba76a1178b,0x160c03422767ebdf4bd7,0x77748e1ae8482cd7e87d,0x8adacabc8d97e6587b56,0x9de2887acba2664680eb,0x7136ca23e328470b75c0,0x77141db6704f969be298,0x15f7e9ec63e88066ffc7,0x7168442b8e89f0d68004,0x371e3b009a6f333d81c7,0x513c03f01677419fe47b,0x5817bfb469c0e1031002],[0x878409f59d76,0xb5520c8ff502c65843b5,0xd954ad56d61d2504350a,0x7e238369be5027bf4ae6,0x46a0c8f5564dcbd14aea,0x94a40ff7220553ff0306,0xc853cad5c966ae891bc,0xac4ef19f70432e7f10b3,0x903b399c12d5ea384e40,0x19fd8a451e71ced13e7d,0x6f4948f1ccae14f5ca4f,0x8eb8b85d6eab19083c37,0x36e41e37f3d1a536c145,0xd21d112da43c281250f4,0x80f5bfa85bf400041002],[0x103b1c8a99b15c862b8,0xd95e22c15c6b0e63b25d,0x9def64e6b73030d7f55c,0x821d8bffba4c55b53276,0x8f4eb4751c004b8d9d3c,0x7c91b2e4cb13b29496b3,0xe54a664a785ff4296e66,0x3e5c366eb900ed81688e,0x338fe2e579335fba090,0x843cc8139a3b4ba1f088,0x5392822b46da775aacb0,0x993f3626ec96312ce5d8,0x7ccc8c5a1cb4fe1cc4f7,0x91f45f89b8a5ca26e442,0x54ad261ddf064f502002],[0x4f40f8f0328cada17c,0xb9efb57b0b70bd00f8de,0x762210e0de1bc81d707f,0xb325c2ae9d52ddd49581,0xbb961ef5a7d131f533b3,0x1ed8f395a5078586f97a,0xe13ce31cb0e015f91838,0x89ac7041ce5ee884c9ed,0x6cd92d08d3b55df33f53,0x8c1618a298e81e225048,0xf78ceead910b4efaf2cb,0xf78ed5f866d0e0d3ab96,0x423afa60caf16e1ae767,0x6c2e1b5fde6564c778a3,0x7381bc141fc504d12002],[0x210717b9543e2d678,0xe5ffdb19a03667e51804,0x1a26f74887943c7a75f2,0xde0d8e42e9f6817a75d0,0xd983606ceadce64f6ffa,0x9b20d18305443472a198,0x98366ad15eed72baa1e,0xa0fc416a9ec57fb6f5ea,0x5c29f38d6c125bc0edeb,0x39f08daf0f2b652d0d83,0x86c0be904c1d2df2daa8,0xd840945ef8eee9bcdf8a,0x7ccf48b2465649fa3065,0xb65789b14d079a1c7c80,0x1e311e6431d3c4122002],[0x20f67b005c336f492c,0xcd026dadac487979d1ea,0xde3f1769e16b73e97445,0xff7a6c300c04e53a72ad,0x8dfa0b166e22739cd877,0xb8fe18b55cfb5ac56feb,0xf941f7668ea315f4dd1e,0xab660f4457ef60b19792,0xf56303d0741000e5c566,0xbbd95906c826bd30208b,0xfe9b889a3f6af783e714,0x863113f8800f784a7923,0x8333ac005885326bd6d2,0x35ffaf8ba8d0e963d5dd,0xe5712b969c8079103002],[0x3027ffdb6361f6e6c,0xd43f64f858d6680c95ca,0xf5608928d54acdba6fef,0x82199f19b7c4b03d5527,0xbada3d8740d772ba9f41,0x674810d4c6ad273b6743,0xdac51c48393143c3e66,0x973a49495c3992ec0165,0xbfe8187797233adea636,0x28e1c99c6d56e7d2e134,0xa111c9d74262de5c6ece,0xa8a789af9bb226326ce,0x5c9fcf8737ef61337304,0xcaf3b5ebbe28fb16af32,0xca51cea0d1c567113002],[0x11f4d9e598d07f0d1,0xa46e4e449cdad983c2bc,0x94f6a822c98b5b3fc136,0xf9502eefd31043b43ada,0x89a3b2845a26f00ede16,0x300feec3264aaffe6f60,0x694aa39959073496ea8,0x5382d4db7a90f04cfd74,0xe064a02e91036eb23e5c,0x700f1e65198dbfa11bdf,0xeddb933b8bcf02810e54,0x6024c672cb1c62679422,0x7f62e79a350646187edb,0xc2d0e5917f241e392ab3,0x5913a3444120ac104002],[0x49af13c2f690feb71,0xf139c2bf2159c8b57c6d,0xcb2e3d81b964992ed02,0x2046f70b56f848e11ff9,0xe89aeae21cd3d461434a,0x6ea47b47138af3d530af,0xf729dec830100791e855,0x8de051c2e55f13286412,0x8f6a712798c0ce85c427,0xd200462dba8cf74200c8,0xcccf14ca391a2e9b1ff,0xc9c33786f3e252db3a31,0x618b8dd5e115ef2c7137,0x777c1bbb1cc04cb6848e,0xf7a98789a7fa1e200012],[0x223405312e079cb0,0xf914b2b757b29ebbc9a7,0x2a3cbded336f04749c8a,0x9c19137984b63ead7dd8,0xf31f3bfce7bb1231c186,0x209b21cffeebcce3cfca,0xd4dfecdb1a2b4baa7b51,0x86264c91ee8c8dcda3b6,0x6ec4de55d91956e2e41d,0xff5e91fde5a43fa6d3f4,0x7cf38a3f9d3568d459b5,0x2a74190035e1db203c4a,0x9608e6139c1d6a4a7bb6,0x70ac176687717ed9f966,0xcb06671cf62bca010012]]).map tailNat

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def suffix9 : List Nat :=
  ([[0x1b6efa140528404fa,0x344c305c3ceff1b72d82,0xebd9f0836c9bcc426bc6,0x31933a233e2dafca9ae9,0x1af110bfd175c5cde60d,0xaa0b984f1c966e70ee46,0x57b85327500d29d54fb1,0x3ccbbc738d69ef18916a,0x7bba71f934fa9a6a12b3,0x828f3e00648f4fd5ad93,0xc17a4f058b8c114396cf,0x8200e426370f024c59c8,0x98b327de9cf0dc121eb0,0x344bf58e61764b9477ea,0x71068aed602800100000],[0x204125235aab07736,0x9e8ecb2dda292c998356,0x7c168234ad54336e206b,0xc6fd4ea86033e7808049,0x2a54c54ae141da87c222,0x59a207193b32b2ae39ad,0x281f2cfa002a942c1ee4,0x18095fefbaef5e14bfdc,0xcb9dc2654a87c933d134,0x4928c053bb796b740e9a,0xb062a581dbe645f1f0d,0x3e7a65132b12173cad97,0x5cc07c8212685228eb60,0x99776ca619db8c9d5a23,0x2064b5a5bc7400110000],[0xd57c198c7bf0f1bd,0x619acb7407c7248974af,0x7e79a6b85c4d3a63789c,0xc96544699c0484408ce4,0x5afe0ab18ca29dc86050,0x5ebec571d73220e102ba,0x9eded32349741f936222,0x4fe7d5bbc95c514f5fb7,0xbde6ef73bd2f64152d8c,0xd5c20726e829085373b7,0xefcff15f97c3de00e678,0xeb5acb22bf0a7ade544a,0x4339263891768479f2e7,0x50e124c0c287d6963733,0x7d93f1c1b8af00120000],[0x5191707dced18f2,0x52b07aaa552b7b0e7113,0x47d1e76a58248ed3d73,0x5aa99502867302687398,0xbcf09823a5a2b49a94e2,0x111820f5b06e7b077cae,0x9e2c6f4dd47fb3e74e40,0xdf33af94ea8433e084fe,0x2a529e74129c60cc21dc,0xb398f2f999bc5ce5b8fa,0x799db18441a546eb14d5,0x38cae1f1d5abb7cd5afb,0x99a2af41cda3e9d0d564,0xc6b9685e7dc0db54e8a0,0x47e5ce3a44bd80030000],[0x20a1ff40537e1682,0x3e16a9436f5c66e37ee8,0xaeaed5c4c4216380e75f,0x15772c3588bdb74f5797,0x71dfee1f818bbabcaba6,0x6447fb26891b7c95d43f,0x2098b0c797e3f15107a4,0x22f53cc8ea3ba35f1442,0x3932ab2b25ba8a4f80f1,0xef80551abcbe776b5c0,0xea30be6c7b05ebcaaf55,0x24f9acd4a5c5342ee087,0xa4f15ce31feec1cbfdc7,0x9c25cd24144f38bbc29,0x4089ffafedfbc0040000],[0x98bbfd807ea4841,0xbcfa3e98f0f69a2ee724,0x8d4ce8bf1b8bd31d4860,0x7f6f56bb8c121c501c1f,0x72df18da2f270ed2e621,0x84756a7d934537650a77,0xa3e16fb2e9ac3ba5354,0x12e9c051db7a999699f3,0xa64650968ffcc5cbe718,0x4262254be00f757a58e5,0x9966c379c359f77d845c,0x8c2b6f7b00e876ffd25a,0x7a5ed6987f2b46f7c314,0x41c8961a6a11d7d1625b,0x66160a12f1f7e0050000],[0xeca684740c8c98,0xe70d6f65c32be931de20,0x84c61ac40a145ef8141b,0x72c085844bcdf28ee80,0xab2b60e9a5d1e8f7f317,0x26128304b08b247c0d20,0x7f390dc3e76992073508,0x788ec1ede72616a4d3e4,0x54cade2dd0e92460eb27,0xad71f45ea61cde6ab1e1,0x7adb0fe1b6f5bef66245,0x55b2650f6c40be9e3a56,0x78e9b7ff0655fd4f9f0d,0xe46aa5325e7e89953f28,0xd9dbb8851c3780060000],[0x47851ab4f0aab,0x2e50ef4f806e00903169,0xf412e90a85b867df463b,0xfc1203e74b22fc8d543f,0x9818888976574bd3ad94,0x8269833152f90067bce5,0xf5c764d6c09989854a9e,0x4233120e4d2a4d08f107,0x8c193d6596e139d43800,0xeba76e5d1761910a0c58,0x181f367ef648137c8e77,0x1e5bc1f5d75889feb12d,0xb34d9c45d461c8e2b51e,0xce42cff1527a482f2ba1,0x948993cffa8b60070000],[0x11ad401fb41aff660,0x33c99012c9ca4b226a8f,0xe4d0d8daa34262bb02a2,0xeafe60bd50e3c6f74cd5,0xcefe83444e146bdabdd8,0x72fbebee1590380ad1c4,0x4445cb7b107235d14295,0x31c4a00b7d7dce41814,0x35386a181d1066884232,0x103be284bae8b4b4b875,0x99e32b6f58b05d102bb0,0xa1936737bd8739f90029,0x2eedd3757575175b1f44,0x3c7748ff06fbee86fabb,0x8e19cabfb68c00001000],[0xfbb24cf6bd8871fb,0xfcafb788c66aab69c931,0x403b3784ccacbdf279b2,0x5d10e8475fe4c91b5522,0xebd6526e7d4efdbae938,0x2a1d17af2526bc7cade8,0x51d8d9819979347eeab4,0xd2bfc57a4e1204fde766,0x4c4db549187bc1332ede,0x944eb9430118963ee218,0xe1d9ddaf132d57125bf6,0x2dcf7450b8eb7e1d71a3,0x1ed7027b2044a6a092d2,0x29eb7dacbeab3480805b,0xa6c92d8f861500111000],[0x97ab4a71ab1bcb6,0x3713515e000dddf2647f,0x2be19ebcada5c23af60f,0x2ebb8096c2a60087d300,0x664e0c60b08b22cc302e,0x293203e0eaaecbae5f59,0x5cf74ae263fc505f5efb,0x439826006d4b12197dd5,0x8ea88c8525d3bb373f4a,0x7341d6370ea9527f2e9,0x9e239715ead95360a55f,0x186729f2d2bacf5469f9,0xf58064e5f42225b7a2ad,0x31770cf86924600dc131,0xdeef7c87567480121000],[0xa1ab3b24d73516fd,0xf3b75c05e1ec047f9267,0x8d4173a8343c9d4b0b73,0xc8d76a4666b75e9cb7df,0x2d0cdfcad1cff6a08353,0xdfaf76e2e1c1525a2a5,0xde3b75946f30eb097421,0xb37ac4159c983ff69306,0xf45073d89abc10e47ea,0x800f316718e0de8725e9,0xb9d35888028171da2353,0xc608e9e50a627aa46d1d,0x5ec6aadb20e26ade9e9e,0x5413faf9714a04175876,0x58c70a6d71280031000],[0x2b35f297c87ec87c,0x429658ef3076499438e7,0x8aa81ab812d1b631e556,0xe90d1656c2c22b9ae4c,0x819ce78642115813fa1f,0xa8fc493007bbffc33ed5,0x940bfcc5dbb6d57d2453,0x1c53ac8150d44ad9d47e,0x4ebc4d09d1a2355bb220,0x41fd161b647e693d2800,0x6f0a1d7036404df8799e,0xf8c7c0eea63380686f67,0xc86d76285495c7736437,0xdf7a3f9db3ae8d07b7ab,0xacde35627211e0041000],[0x2b6d2e668200574,0xd236a536faa7f63151e9,0xad8e4a0c408686abfa67,0xb96e7f3a13a7b2ae562e,0xd61557700abf80431ff2,0xe686da1bc07725c27943,0xfa8f384b7d437cce6b53,0xf4e67fd00cb1e6e13940,0xf5b7237a8d14b979bca6,0xb016586d20fd4cd0e249,0x2d455e48dece2d329e39,0x6e2205cd9b5488f224b0,0xae8fcaa2b3af23da723a,0x1ff88524933296817a32,0xa6d5519a623590051000],[0x6cfc8ac57d2a2,0xd9fadf60f217ebba8338,0x1b62bd2d638f72ac4ef0,0xa02a97d5f0ff395bdd87,0x21429cc83807beb0e8b,0x7d485de4a2a5f994c0ec,0x24a0ce1e755ae06f7344,0x4613ee8e2d7b7f4f7ae2,0x158b7577c17dc6649988,0xd7238e561319679aef9c,0xc750a784d47a11420835,0xda916f29f449f29f07c6,0x7d989b67b780c0055f84,0x7e3c5431d7603d8bebf,0x8791f315586820061000],[0x21cef348a2e2de39c6,0x310455e0a2ca805be167,0xe601ab968af7cd2361df,0x82b90ea01fc198e72be,0x7baa3e06ecd227446aec,0x338e7c9617fb761d5081,0x843132937d76594cebf1,0xc3b372a40b66eba276c1,0x900bd5810e70f4c7dfc4,0xa3702dee69d8ddc5f40a,0xe89fa81719424e1072f5,0x9284e00c55c82f32a701,0x7d3c2c552295f10e0f2f,0xe58e07679b5059c3f9cf,0xdf5e9374db1000002000],[0x11777e2f212b31379d,0x35a79a96af32d8b2ae2d,0x9af8ce88226084e9d805,0x4433d44e92252719b076,0x9bd5751b14a62c033ee,0x8746e85687b9d2541287,0xf5a023a9fbed64702a85,0x9b29a3def946b621ed32,0x23fa7f76e0ffc55be259,0x834e30f41ccd252feec2,0x6c011aa5ab474220d2e7,0xf65517f8c6232132161f,0x38315700b448b5e60414,0x437a5b4616f6a904c9a0,0x9c4c4bf2bca200012000],[0x1a31714a7fd4c29c,0x5b8a373e8d7a85456bbb,0xf8dbd92251e6e30c035d,0x87c171d4a4bf76ea351,0x557ec7c830f59738abc8,0x287da481a9ac53c63445,0xfb87ac6c4e5bbc914c29,0x24e8e10828518ce9bd1a,0x6967e549bd922fb88dc0,0x40271dd4732c1e008069,0xc64be296054ade575fac,0xac0573fca9b3b10508ca,0xe52328aeac976e93c4db,0xc824f93235f39d72a220,0xdafd108169c180022000],[0x914c21cb93066095,0xa6c55e4372cefb5f0856,0x39d4602b9114e3a7c8cd,0xf1bdeb6b27303c617ad2,0x57b7d96bfd892b3ba13,0x7eb7404bf78d3ca3df57,0xc0e28fe01ef817a982c,0xd0bf45f69aa4752a186a,0x20846b3a70f3a0c62f9b,0x27578897a7e0c0095933,0xc8d92d16bed0c9e7b02,0xe6bf1f3b7ef9ae72e849,0xe43edbe527318d31461f,0xb9a5f128e23c3bf5f4b0,0x2f2e02a881e3c0132000],[0xf04a9b17f9e2e23,0x769a77d393789354a7a5,0xa7c304cfadf02af27407,0xa13d5d5921403d1d239c,0xa45e8a7bae5af39a98f4,0x255f54be9a268edc356a,0xbe483a12dcf7dc53a805,0x913551c7f19d2e2ae30f,0xf8ac1d00e260699e69b2,0xbe6968bf171276b75718,0x523b1d344b86e23ff730,0xa8a650145f670940301e,0x3a385b3e6a6bede044a7,0x60d0e5fd7205428c96d7,0x71999fb049dd40142000],[0x57ac5573e59bc,0x43b771979c79b1f956e6,0xd1decd21f57bbcf07cb2,0x78b663b882879ddf650b,0x7369c685be971e52f9f9,0x56c6ecf0ea7674b175f0,0x75ca1613a500d6ea1b65,0xf8c3ffd9f0496130e6eb,0x388e4ec615ae69cd712,0xcae9706fb13834613b7,0xca61f7e5cb9ecd2ced8e,0xb7028f5a1a364e7fb1e3,0xc6b301b541a62e076d66,0x4cd52272d07f1b4f5b65,0x5de1e35c867e80052000],[0x707130cff4eb82b2b,0xbb48a82a4e412770d48c,0x84747dd830e874dbc6c0,0x39c9c792ab80a6a69d52,0xdbb14cf2ec7308f693fe,0x1effc2d0ac796ef5cd1d,0x67e7560c2a26d9ea0a17,0xc6c8a4c1eb1d7253ca24,0xbc54f78a7263fb6f66f4,0x915d0fff5770071dae61,0x8f93d9eceffddfedec55,0x4871a09b745ed8a82017,0xc8ed124ecbb178a6df23,0x6a79ea4dcea2d3de3bd3,0x450d2a0ae46e80103000],[0x783d6520dea0edb98,0xc9772d41d5a1ac3bf2bd,0x213c37273080d6c17a94,0xd8a773a9f4ee2592e733,0xec90320791a46230725f,0xed3ce8868ef69eb025c5,0xa905415e384b7d6cb4d5,0x3ecf0c988112abc1aef6,0x65f02dac4befef4d6020,0x119e128dfb0adb81780d,0x77ddf4948e15456044ab,0x8b1af61f446bf65df014,0x60b08d6ee46ab79386d3,0xa24281a9911d7072dbbe,0xafaf14907cdd00113000],[0x1ba1a44776c6ccb9f,0x757ab637b5c8dec663dd,0x52b2930ff1e91ba41ed0,0x53ff014efb881dc5a6e8,0x9d225d0000f2f050b43c,0x7cef689d1978a3827757,0x240a92e08f6741646cf7,0xc216a643bf446e0be692,0x4735726e4ac165f8756e,0x28455dc38bff2513ab7e,0xca8f4b844e423ea15274,0x2ccc34e396179effe761,0x1bec7c13265d98920862,0xfb2fe97ee28ea7ca3aef,0xc73d80b5bdbcc0123000],[0x1f459130534755ba,0x7c7f30dcc358d86cf6a5,0x487b21fe074488cca715,0xd1ffedaedcb062d4182b,0xbe489d285f55a2986fc4,0x1bc20ff4ca226c5d25c4,0x338c96c943fcf2527278,0xe812c6e5f75257b24d7c,0xab8c1d4473d1ea435730,0x40bd6952cd6e72abfc0f,0xd4c13fd01eafe7556430,0x281508b3c2986ec3fa11,0xda7337c9bde690e5370c,0x678429e339bede0082a9,0x8e5f3118e30150133000],[0x1685f5685b3f7,0x8b984b02789e9f3b7f22,0x1f6b76858caa28bc6c1b,0x14e6fdbed2cc33733a0a,0x2b0a7ffc1a623191686a,0x84e20584bd0bb5756ffc,0x8c0e52ff022661efb5d4,0xaf121138baf29279df7e,0x6fc1e1ead08a9386a912,0x3be254346583dd4e2df6,0xe8424c53dcf422815c20,0x37f267dd33078320830f,0x2c73e7282af88505c495,0x6b5bee691b48a51e4a58,0x8540e1f57155a0043000],[0xb3be9480ea28ff3a,0xf547664bee4380ec8931,0xd170e176269ee7d6ad3f,0xbef7eb5222e4f3e4d0ef,0x3c78ae4a8b8211f8bb44,0x605eab951bca02032a30,0xebdde11985f6bc20e360,0xebc5f3f2c684bf396eef,0xf02da5a30ae278bd10a4,0x12ec9b65502e239a01e8,0x213b85caee3b2fbd7952,0x539470dfc6c6ae850e2f,0x4903aa5543d2024c7af0,0x8234f5c294aef86c2f23,0x605c3420546740104000],[0x23e67b2b2eeee2a9,0xea26f4994ba2137a198e,0x43129178f527b87e5a4a,0xa748b50db91a3ab41748,0x2ed13466c5fcbf865daa,0x293d2158e03225116e4c,0x82a55a4dbccf2e8783e9,0xca545f1289703357ee0,0x17200b83c9b9da20f382,0x4ecb71da6fcd19ab3ff0,0x320f4e1f5a6b65960c1a,0x485eb720a44eec569153,0x439cd607a964548822ef,0x63fa782b055eaef2fbcd,0x3b0eabcea1a420114000],[0x4006cc7164e5f41,0x938d4946d4facdc85d2c,0x35ccef1e614828cab874,0xbef578a5729e0ce95c5,0x4912a7085dc98f91582b,0xf0388d9e4aa5567199a5,0x8b69fd3dc409e75c540c,0x30f8eaa8cfe16866dc8,0xbdb39d1bdf0a034e7e1a,0xf257c17fa8449a04d414,0x8b78d433abf96c1fe8aa,0x7e859db356a3f1968f25,0xbb2e824e155d04949e9b,0x2a9168f13b0cc4390e50,0xdf0fc2621ad140124000],[0x6ad7b01229fbd30,0x58c977f67d00fd751417,0xa34636c12d2a980e9ff1,0x3c0b719e5955ad166733,0x8e0334ce6fbcf176bb46,0xefe0259e6f9b6468a6cd,0x11efdcc1bcc1b0b55a66,0xad351a9fd71dc7354c79,0x7cf354785e4988000485,0x7b984f9264b0a97c052b,0xf44aabf418b69cab4323,0x746383ea61ce7d7fb24f,0x5f6530055a67325865c3,0xe6478cc5d17e6663b5ef,0x7b27d722e4bf60105000],[0xc53f7a2eb079d3,0x5519bbf3366219b496c0,0xcb28ed0c91fd2f989e26,0x954bb1d78d576ceab32d,0x7791bdf071fb53361523,0x952d995ba199a175a805,0x4c1f1770baf99b668225,0x394881abdfb5b6309025,0xb5367b408f6865e883a7,0xe5f490765f77d639d034,0xfba64cfcf42ee771b54e,0xeaab7cddf4cf0450bac4,0x7b5ecf34b19d16b2c2f9,0xcb4485c18ad177080031,0xe2ff480d0ca820115000],[0x8e41fc9c3dc8d7ad4,0xcc4c48f7699adb43079b,0x66ff06868d339a55be39,0xc536e52026bdd3291d9d,0x787d81272513394317f1,0x240b33863eaa6370ca91,0x8952b1f18f9a374b458,0x8e02ec828fa786921a28,0xa760684d7af3cbb1fef6,0x67c9da16098c11cd98a7,0x6897324154a27d709581,0x2751fa270df89009763a,0xe7800820dc747068ab65,0xaa76484e14237aa164a5,0x1b5652e9a3e900000100]] ++
  [[0xb63f6d2a0ae55e960,0x945814fd6b9ebd4561d2,0xdb0033160356b0aec0a3,0xfd1d920720420a4f0580,0x533ca196a1cab6ddd505,0x40959aebef19bd036aba,0xaddca82e02ae2be2cb18,0x7e2a4279af2e034aa2f1,0x378e6e6a5af121959362,0xcbc6d2c3efa237ac69c7,0xae0eccd5654d6882a6f7,0xc1f8624e74a8cd035a36,0xfd3276dabd64036a56c2,0x81426de65d83147bf398,0x9258a6f2b7fe80010100],[0x286d8cd0371858e4e,0xadf15dcfb22360562a50,0xdbb71c44a76987d420dd,0xb8e9d85ff4ee292fbda1,0x5ef762f8b48fa3b0c09a,0xb5d61e413875380a82bb,0x826465939eabdf24db58,0xb1125be2b7cd73e348ec,0x95ea02985cc13d3ba0f2,0xcc49c0cdca634e5d01da,0xea7ad8cdfa6f5188a212,0x170330aeaf105dea1350,0xd0f53745e39bd3a9a5d0,0x1aa335ab85ab9dbfd7be,0x4f18c024561080020100],[0xa1a3f8e556104707,0x645cf318cfed3fed98b6,0xb3da225c83c4dbde9386,0xee4b331d5a65a20593a8,0x6636fafb41209a31ad2f,0x258cd954ed8c12cbab31,0x170470810fe7ba98dc91,0xec53e661f38ec64474ab,0xe3f31743263286fd218f,0x347a1aeccc31dc168cf5,0x7083d51d6fe514923f7a,0xc1d134c51d754d0e6806,0x916efd8d72a2df7f3ecd,0x681caa93fe95a1f3dbd3,0xd8344124536680130100],[0x1ba0ad2c79df6004,0x89fc22136f8a8d4a018a,0x95f91c1e3b686bba9e2b,0x44d497d716b2398656bb,0x8cae0042b2fcedf061b9,0x84d190927407e99c5f38,0xd008e8defdff5dcde39f,0x227e69c26e6ec6d32382,0xc074bf8f3c0f215399d4,0x78de7235409eedc72967,0x7ecd5a03a7ddbceb8ae6,0x565a0cf497df3b32eec6,0xf2a1666f0fe39bb7814f,0x205c75c3a1fc4e146ec2,0xfd6d826e290d60140100],[0x141a753ad3dd5,0xa0ee9090329dd446d980,0x739c69914f7d42bb3861,0x3a016a7c0a230385b6ec,0xf24a46916f70899ec0b9,0xc820dc62b353545125fa,0xd19f1d169e8db11af9e7,0xeb8dcc2fbf71a9c3486f,0xb4433f2befbb2c08dbdb,0x59079a69ca87eb5b89d3,0x119b12ea34c265a8d92e,0xf2b57c2811fc51e28b6,0x41574c3cc0bc9ef61fa6,0xac157377ea52bf47c5b,0xce1f3d7c327da0050100],[0x78b871f26eea4481a,0xd620fc1737124c90af56,0x530cbe54b8f9bbc590d1,0xb3d917da0fda30d77f17,0xc548dece30d16de5a777,0x3a7fd4930db45166dad2,0x648315095b8af76b7fe1,0xc816a1d278f8d3a028f8,0x3379870d67e0f3860f47,0x1ebb633e2e4d595603f4,0xffb3b597918a7c2c99d7,0x15e80ebb44cae6a7cde9,0x5ddbccc8eb23e691e1a9,0x1f1ad348b861bf1c4113,0x6c9fc1fd2b5e80001100],[0x1103ac94dc6131aea,0x62e395099b3e13300458,0x5b7e689d72a9fab2cad1,0xee33f12d401641db0de3,0x110460333a585f1d6661,0x6ce53138271ce9c1a8f5,0x759b9ad1467274a54750,0xf5b87ce3481cb2d58462,0x62b324316b4951bebc6d,0x7542676318884e62a359,0xc24c075f3287a7a2ea9d,0x5dbeb9a0c7c4abf162c1,0x9197f64267e85a05375b,0xa210c25e7ea3daaa75cd,0xee396fe7f18300111100],[0x1fce7519a074cade3,0x359794e2e361b6b8349,0x1fcff78c82092cd17c4,0x1d22009f5182c3df9dcf,0x10025f71206f424db5f8,0x7a7c4e6bd545f4824323,0xde5a0e38cf8a1ba2f0f8,0x4399227d3abd112c4fd1,0xc3df3acb6d4d2d02d181,0x6a7cbfa3e8f70f270792,0x656d3b167b10ef30fab0,0x65112ac68111c2229792,0xdc526abee9ff64b3d56f,0xb4da99c8474ffc317f95,0x20dd93e48fc060121100],[0x462a73f2c4e487ff,0xca1c0ea49575dfd63bc4,0x1c8f810065d7d15a87d1,0xaf165065a96afee6e79,0x66b22dc17f13755056a0,0x1e8a8c7c7b31b3c2d1fe,0xcb65833f16b849a180e0,0x138f3a4704fe448e3b21,0xcc541334a76e3452b345,0xdede12d00dd945233a2,0x7d33171921e5edbc838f,0xa66902d241f5816e37e,0x4b346d141955afce7625,0x262c113bcd2f5e0c6efd,0xd74c1b039efe80131100],[0x2aa06aa32f1cd,0x2c86db92ab3c738258a2,0x9307e016dc276b77a47c,0x4ee8683adcef36f8f0f7,0x1d54c68d89d2bb302924,0x4d02e1e7705f09c695f7,0x5dad7015a0b4130aafbc,0x9a9fdd687a643c3d27ee,0x24052116c045bf8f84ed,0x94e9ee9e300bc8a9b7c9,0xf9dd5f3e11b6882a354e,0x471dbf9fb427483eabc5,0x6dcb3364ebb523fbe43b,0x761d45a099edd112c6b4,0x53601f71a3d340041100],[0x1ebc1b1912c86ad9e,0xfc0b514754d76645d378,0xb0262ea7a399bea193ad,0xa65950a6da74575c186d,0x508e75a52954b9180fd5,0x37a340412b741d4b92bf,0x7aafe2a3ee3d32f1217f,0xf57882ea32e085a57023,0xc6fbe9309cf6214e0ecf,0x42ec55dc02584a427284,0x91d6748d4d533df8501d,0xc180614bdc6a8596cf9,0x17864b92473ce830724f,0x64118fde8ea36f9e3f98,0xd526beeecb3c40102100],[0x18c8e166eeb4fb38a,0x53b23c352dd32ba31ddc,0x7e007da4f3849b7fab04,0x218dc9adbb404574fdf5,0xfb2a359e72bc1184a112,0x4594fb0e729e78bf6705,0xd7046e27df51a7d1edb7,0x897cca9eb2b8734d986b,0x89fd73da597da18aedf2,0x4bf8d4f2965f4d1ab79a,0xb23853966cb1a5e42a2,0xfd639a527732928d8167,0x8eabf6d8955753d9869d,0xbf7a63f4f0bd626e69b2,0x9373d807fa020112100],[0x372ead3b81e21a0b,0xa7fc681b786c1264813d,0xace55aa744451f265e57,0xa0274d09c6acd3930b18,0xb85c8eb337adc71f126c,0x6638254db3d372496472,0x1e0f32ca3e505e34b1f8,0xf996732d4db38124c309,0xab82d6cd3efec9728e55,0x7c0a798be8c78313076a,0x4639b275e7dd861919d5,0xc642fffede1d9e4841dc,0x681ede155eb0a54f0171,0x2b3ca4c4e22bd45592a8,0x566fc28137aee0122100],[0x1685f5685b3f7,0x8b984b02789e9f3b7f22,0x1f6b76858caa28bc6c1b,0x14e6fdbed2cc33733a0a,0x2b0a7ffc1a623191686a,0x84e20584bd0bb5756ffc,0x8c0e52ff022661efb5d4,0xaf121138baf29279df7e,0x6fc1e1ead08a9386a912,0x3be254346583dd4e2df6,0xe8424c53dcf422815c20,0x37f267dd33078320830f,0x2c73e7282af88505c495,0x6b5bee691b48a51e4a58,0x8540e1f57155a0032100],[0x3759dc6c8676fb0b,0x5a363991f3f155c39e85,0xfeb06549cfbd4ffa9428,0xbf0e7da60274fbfffb3d,0x7bc83f18b302c8ffad04,0x334f3382200474663571,0xbcc8ec2f74376e085206,0xa91a0bdbebd2752dadf3,0xebf138842b5199a6e4df,0x5869bb42ae989b895803,0xd2fa7c5bf717e89d8c38,0x7af63955856ff05cf437,0xa26d15641e85968f1b6d,0xd3e61c58b985dd28ddd4,0xa2285aa2c09f20103100],[0xc32736e00f499fe,0x4d97fb2c6cae301bf9d4,0x365041ea31fa562cb4b7,0x1169cd5cb9d1571ba116,0x56353f928f5cb4003f8b,0xf9a031dde9bd45febc5e,0x402410b432d6973b1491,0x2b99f8a5d34b943dde64,0x8700fcc4b6e130905306,0x8a94db96f127e2f29681,0xf4b8886ff20bd9f5d260,0x1853bdd6400a1aa0e08d,0xaa4b54fbc848c6cb4b1b,0x8e5dc76a3044b22bbc68,0x1fc1de1904c660113100],[0xc52079654e6392,0x2ea845a1aee43d539afb,0x283b7399c098922300c2,0x47cd6fde7275e71dcb27,0xf85a1cf227988ea5f1a0,0x62cc40e0baec9cc3b65f,0x2571db29cf1a7d07bc71,0xde8584dd68d946680878,0x94586b2d8b55ee17fa72,0x164f787cd0c96b437672,0xa67ff8471551cf64a18d,0x9c2be348d8d705e3e185,0x9738c2802adfcb70c500,0x256e611b95b25ae49e11,0xaea4cb65a28a0104100],[0xb414b7a91aac0ccd,0x535fac8218c86f8316b0,0x6503f7c20a783f4a890f,0x23e9dca16a1148fd6402,0x6cbee3ffab980458ce6b,0x9dc4a4eeae14621cd68d,0x6e198f8d1cf5c1904361,0xd1ffbfa27b9c2d1151d7,0x4216ce10ebd605934887,0x25d21b2778ab90f77600,0x7bbbd766a954f5b31,0x5cc248d1bdbef6b995aa,0xcacfb27b589a49a8cbf4,0x59a147cf25fac3372a1e,0x8249e987f7ea40000200],[0x3b53ab37ce0fc6,0x54d220ba9e8804e90354,0xe8524579f176bc77054,0xbdbab6d59194f5425502,0x146caf420ac1bdb9cbe8,0x11c4714049391ee03918,0xa1aacb11d6defb83f832,0x969cfc438e8b32190dfd,0x1fc8ec4db7497c4a7a25,0xaa0eeda0056185267e3e,0xc5d660826a182bf1e1db,0x650bc8547d0cfb0d2497,0x232933990fb366fa90f8,0x47a2f93aa4c54ad3399c,0xf484cc72b37520110200],[0xfdd8168acd81ac7,0xf96f139e7059cd4b3631,0x6bfc4400b9111b791b12,0x55958cf9261f7bc68a3b,0x3de6e70d33722c3a2695,0xa3f5d1255439eb3a4f5a,0xe6f9d6eb2756021be88d,0x3fb2195bfe6153cadce2,0x654682703b429b963d0c,0x5f4b77a74db5e4cae5f7,0x6e20d07d9ab3de38f3a6,0xb092d7214552cc5626f4,0xcd6f90e58fb41e8b8e9f,0x775abb6bcd5725fce87c,0x30aadc136c6cc0120200],[0x1157a80700a6aedb,0x74d5ac2f8be370c824c,0xd3456869a6538ecab780,0x25bb021e44571f10a5b5,0x18dbfd763640a556ef6c,0x548094ff5f4f667697b7,0x2ed6d6d428ff852339ea,0xec0b271af1e3ca3e7ac6,0xb9f5683c9562124e47e0,0x84b2d3d8ee66c61a201,0x5d2c158d3768f9538822,0x5338193afa95103d75ad,0xe93f9a13b447a03ab9b0,0x887b4b3431c191e19632,0xec62daea657a20101200],[0x1330e08f3641d389,0x9775bbee5fff05cfe3a7,0xb1703adda8f28a188895,0x3fcfe851d37395cd8bcf,0x585df1bcb261bd9e2af3,0x733bd42fab3c77c453f1,0xc0f753b59695ba542df6,0x92583b549e1e8f348c37,0x6b5f5c7bac19dcf1f11,0xf591d346ae1e6767c6be,0x565bf6c6717e5c4ff48a,0x706dab6613bcf7d57266,0xf6316a73e44f7d608ce8,0xa06c52682361c4aa1c3c,0xeb96828b476100111200],[0x603ca2c855e53cd,0xd5ed84868b930ab70b30,0xfd7fb7ce5e5b37a65b4e,0x7e9d2ebd56808007ee69,0xf808dee01a56e356c3a,0x21593ba057962c842762,0xee29124615dd0819d0c2,0x1dbb0c3f86aa78b06ba2,0x263598df1b160c5f1d3c,0xb0863756797e40c5c004,0x51c54a19df01642e5c3b,0xc43ff3b4bdb1435bb27c,0x6655ac4beefc98b0554f,0x4ba5dfd5bd6fc55336a3,0xe78793dcfed540102200],[0x36905ee3a8a0e4,0xcd996921cc2b72625b9d,0x67a9e7a632070b0c1f8c,0x3d849e5ede6ad3f99726,0x675342278cec37cb94b3,0xc78d69c960a00539b15e,0xebb559c995e3ebb6fe64,0x7ef14f3442463f1effe7,0x5ce5b442c72e02b7b83d,0xdd10695629ef0f66d74a,0xed999fed57f51ee323fb,0x76e462c7d01be1b0b859,0xc6829b673d085590aec2,0x4654199d59bb63277980,0x91f6257427ff00100300],[0xb7a43966f22d9cf75,0x81ab4fe77af0693602ad,0x5870d3da6a86eea8ea26,0xc12584a4bfa6531fee99,0x3510639d9fafad6d1901,0x5ae34f5a8e916890303,0xdf6ba87e09154eef126,0x167daadea93fb4e7154c,0x79bc42c9cc1823b0cc61,0xdbaf29f3cb162c529427,0x51c9325ecc12e7a3aaac,0xeb2dd9466f16f0bcb228,0x98f03b0e7054f6806fbd,0xa7d1f7d5d06de46f71b6,0x6e09e510682c00100010],[0x32add2af4ac3a3ed9,0xb3e9070d5b8c105e7fcb,0xc57ca97d37c091f4030b,0x48af951c77f6b593cb4f,0xd4bfc48778b373911368,0xf0ceb07ce7fa3226bc71,0x7d3bad18efbeb76d0980,0xe59f9e043ec7247d75bd,0xd05085f087036d2322c3,0x7fdfaf8a5c807f752169,0xeaa5bea25cb6da6ff0f1,0x86ddececb20b3609c433,0x59ae0bf9d393535b45dc,0x40405801a65760c67746,0x7d6d959ef40800110010],[0x928fca16bfaa174d,0x8fd2f130d6fea86b5d8f,0xdade5f0b3e9e93a29e6d,0x72654fa026150e471353,0x77f01b405ed3d62e6f1a,0xb4866382598250ec6157,0x29fa209b0a7736465c7f,0x42112e6252f640afcf63,0x655d2d4364d2965dce71,0x4da9d79ba65b8381c5bb,0x920257c36b9ae5b7af7,0x4286a6dee21aa7f40c61,0x39fa91eb1a40b17d2765,0xbdb3b24613993e8173e,0x99e7806ae7a160020010],[0x1f2183525afdc74e,0x759aba645d239593203f,0xae2bc11126ddf600b74a,0xf5345fbb5bd9f6164634,0xc92fcb4afd7d3d19b23c,0xe00a470754be43914867,0x3001d92ffb200070e305,0x5ee994e937da00d51664,0xc054acc58b45e183e952,0x1ba55600d9218c1bb911,0x45dba509f37a524e7899,0xf23aece2a09bffe6aa3a,0x33ef062e9be3b35abf43,0x956dd926b903d8e84c97,0x56eb53b940cc30030010],[0x1baeeffafddcd,0xc753683b231279385f6,0x8b2382798afa896707e2,0xbfb6d20b09df2d9da1b9,0xde63a546970bbcaa3097,0xd7060cb8ddbdc60f01ed,0xbae259ccee191e103ceb,0x45d1122155059c707d92,0xa54caef6633c685cc77,0xe55022d999d7cf67027c,0x32ee3a8c1078ace617af,0xc2da7a48ca3d62bed83b,0xcff41b6b338eb1defe6b,0xa7d83eb7ea3aba877dee,0xe598a221b74c20140010],[0x4c13bdade7e518ee0,0xc7fc19cb660a8a195680,0x3ddd872e00c938df2463,0xf2b480c4d55ae88a6ca,0x8bff5b61ad6886180ee4,0xf99a9bf99e42f41bc06,0x3ca05896404a1ffce3c7,0xec2fe15abe8379358ec8,0x774b8fce94ea71c40b76,0x18e38e6501d628a82efc,0x90eca1604613bc9cb3cd,0x258fb0596f3eda1735c6,0xb2988d4cb89d57b6426,0x6d73d4bc22f3b8babaeb,0xe72c1a051501c0001010],[0x1812ecac6a30c1524,0x585ca037f6449e8dc630,0x7d5cec19a982b8a2e10a,0x9a18bfd620d2c33e2b2b,0x502dc14450d93e070d4f,0x16af755950d68d488563,0x6f6113d383746b0e088e,0x1bf32400adc29c0073d1,0x89145c3a592d58e7d644,0x2450353a9e74276f422d,0x85ff8b87aacf9c54e32a,0x42ec86417f1323085f23,0xd86c774cff0f06ee1faf,0x18e5dc7ff8d2f0fd83d2,0x946403252b1d40011010],[0x238186e961700339,0x25b95dd06e39f252ac6a,0x127f23388f19b0f44b4f,0x3372bbebf9e504b1e63e,0x1edab0d7a32b37084922,0xac7166661fb0bb1cf3ff,0x96938cffdc740a8bc659,0xdabf1c911c4e87e80c3f,0xbb3a90d965b78b528438,0x88ccc6ce53100cf8a295,0x43a6c29341e7c1055e8d,0x37ad8d8b10c4cca4d836,0x6d4449ff643838bb1f30,0x1dcff153bc3104012f1f,0x486c6b2f170990021010]] ++
  [[0x3a935f0547efcdb1,0x60723ffdc9f2b271446e,0x1f943ce6b70892c0f84f,0x9023f1df0cd4aca9ab91,0xd8f9363d475aa40a9fe1,0x26a859b0312048a72688,0x3e20e346c9f69670e585,0xc68df0b0e985b2d55dbd,0x88996fd6e0137dafdf3a,0x7ccec58ab27528d9f429,0x44f33d4c021dd15dbdf4,0x4ef59951d407914eecb7,0x80b3241b7c60dbfd375a,0x135540706fa6f5a20e93,0x9aed4063c956e0102010],[0x46dd708d0b6ab8f,0x6366f9844d9f647daf61,0xe4d74c61e86ec3e87057,0x8609bb3b5126f65232a,0xbdffe4dc4f065af56849,0x647af43378f551ad5735,0x71ab64409500d8805126,0x4021de11305016579b3a,0x4809534f25e57db65ec,0x66aa417340158da9edf3,0xe2f1c4881927147e380a,0xdb53829edff92278512b,0xf4caf525ebc5ff3d2758,0xd44b2fa840b206f7d065,0x84ac984b4b22b0112010],[0x3c47aab739936c0,0x44aa7ed319fcb5be5ca9,0x9d75624f019e09d72e5c,0x13cc4481c35fbec6d783,0x6912fcb56511e5625753,0xc1c21954131af3d1e461,0xdf6f90adbb14b1dddc76,0x39e89a1a9606e6feae9d,0x1e98c31bd917f5f649c3,0xe5e1b1a476d1155f6223,0xfc2d48e561a560fc9949,0x52ea6e3e6d4a347e93c5,0xe6e34781101081ca976b,0x236786b7684e85f1b350,0xe29063dea36af0103010],[0xeac48dfec83dea3,0x231adc6620e5c20c93d6,0x6b4e8713e528d18699dd,0xb0c27fb686171896d8a,0x59bbb131958c18cfdf29,0x883e681c1f2b14f1304a,0xebf8ea2793cd7a6556c3,0x4c79d551418448cb55e7,0x675ab68f8c79be32ad59,0xa8a843aa6c5aca01152b,0x7c257651882242e9c98d,0x6042249333fc0c998d3b,0xb3dfaa9f5fbc7ec9621c,0x18cf049661ba9e7b2ec9,0x734ffb44f56440100110],[0xf0fbf0b9c327641,0x59f115ae23bf07e17a75,0xb933ff94fc1835533a39,0x26a0c010363bb4c02a98,0xdaba80ca5d5beaf3b510,0xd2bb329b5b332abe87a7,0x82db888da029fb09a54d,0x29c6a28f7d9429fa4830,0x63e7926edf5d1556f211,0xde8538f43b6237519f64,0x412f6ef5c1a208165acf,0x62a266f5130fd0ca059d,0xb577d5209b6679c7957d,0x87f0e4ab0298d16f27fd,0x2ecf9e24511a80010110],[0xd44b1a071d451e5,0x4d0f4a04d724a5108482,0x76dd654576283753259f,0xa03250a99eb47ac0856b,0x7b4ea556d35c2ccf4cd3,0x809a5d545fc58383788c,0x513a30080277a9a0c4c5,0x7a4df8b45906b90a09f0,0x46cfb352c9fe994be254,0x86e4963ba5ea462ebd8d,0x509d67bbd1cc482ff1a5,0x61a66befccc5e20c9fd6,0x9915b9b0c9249c5c3697,0x164c46a952efebe3921,0x8808c9cb1d8ee0001110],[0x8b60dc36dc531d690,0x24a595a3098a8ff0b7ae,0x720b98102dd4209adf68,0x4cd889d69631eff48d16,0xbf71bb386372c512e31b,0x4652432ce61c7d1e2f36,0x5aa3a5c4582b0b6887b9,0x8221c264cab480e3e45e,0x3a8182a3d02c2d171083,0x19f706e21dfc07133707,0x75b9691bc1f7ea597d96,0x2e5e14cfa92dc64414ee,0x325f5140d2551fc8865e,0x554a060e482cd8985f41,0xb6f2258ee7af00100001],[0x1c670f6b9924b5e7d,0xec0f41fe3c946a6faf5c,0x7d67249e0af2f88ebc7c,0x5db0d1968ecbf0931299,0x54cca901f538b2f74d6b,0xe768dee8f7020fcad939,0xf1b5b6b6910c0319dc00,0x7009329dafe11570ac29,0x434686d87b7b0f4b6e36,0x70164981cf553061eebb,0x5814096cc17127232153,0xd7e60dfdd6f2eae28798,0x676b0fb2da6e56bba175,0xa4bb3576c23417b4ca91,0x13175feecb5a80110001],[0x156aed9716d3f49d1,0x400f948e8347486aa0f9,0xfa02ef50dd7af24fca13,0xf603ab1b612e4c5e6fcf,0xac1ed3c2ceb0e152d995,0xc654cb60c8d31e307288,0x5d4c2f418bfc22ee203,0xead4bce1b745f656e09e,0x787d9fc3b76a439391df,0x41960df36bd8ea639830,0x8264debe26c1c107d106,0x763869b0a9e1f0fd0c7b,0x2145e08aa517893db46c,0xc75951e35b093aa28e17,0x417b7f58d90180020001],[0x1df9399276e03b61,0xd7e94b52a2e886e949e6,0x7e024f1f2fe87f046442,0xc2019593c7cffb649660,0x56d64c260ee73b89da67,0x871de1bc329dc184bf39,0x8c20f054e8bc54fff173,0x24cf9d3df99d2ad2ab59,0xfc1ce5904ef020c6d98d,0x54e6a70a2186d9d16a9b,0xf1635a0571ede391454,0xc5aa133d7a97a43f1339,0xc96d7830ed123673b05,0x8f96ba6a77e8ca4cc128,0x6566a38961a400030001],[0x1ecb81b0594381e,0xc8b7f20e183b7a648708,0xb3e45f25a41588c240fa,0x5031e4997e960743fe76,0x3b992eda537e020e6d24,0xee3c15045da0a212a75e,0xf4ba727d1e47b34864e8,0xb13dcbb86974a4c53c63,0x5a09b154fce9111033a7,0xcec6007a705d3629f206,0xb0aad946713a30ad49c7,0xa9464e481d5ceffa0192,0xc5bfcf09331b11e00d10,0x133729ae3b643b012ae4,0x16bbba8e6f8620140001],[0x1ce4b011c18de,0x1ca13bcd5318d0dd8c7,0x610b08f3a990fc67a1bf,0xad299bac6e33c5946348,0x7ac3c1fbec8490a38470,0x3566a149e299f6a126ee,0x9819f4c11fe5767a9ae1,0xa79334a5d2c610cbc919,0x68141c4ed69b7a44b313,0x56bd7fbee755c860548e,0x1e41d740e4918b525928,0xd73e0256233141c00568,0x458268e0e8aca4e6d0e3,0x58258a50b88c771c64ed,0x4129745e56b820150001],[0xc9850944ab6bcca60,0xcbd059af10d25c164903,0xd399aeae1c291344799b,0xc11998b82eda249aaf42,0x7d90a1a5243628d8e8c8,0xd0cca16acb0b76b699de,0xab806527d3984095c758,0xc7ace41c821a1b7ba577,0x902b96ef4b453cb20938,0xb79ce641a953e3d55c6,0x259f00857c71fc73bc16,0xe0c5480cb11a814589f2,0x74763d304cc83ff65665,0x5e0765025a845ede0c80,0xc35b299e02380001001],[0x4b3f1bc882692c0b4,0x970d1e2c2143d1ea94ce,0xf5dac8149dc0bc6e9172,0xfe23afa77e8c4be9f602,0x775d0b21259be3286386,0xf0f4e9e433b1ec984ef7,0xb937e2afb07528c6b223,0x31bdf7c29fcffa0616c,0x65377244331954b135d1,0x721fb1a09a6453068b63,0x2a8369718157c1293973,0xb2568f6025fc1f60c827,0x9e2d5838f1dba9834c5c,0x704289df7d357c98d436,0x88577932e2fd00011001],[0x5150551696a935a7,0xd0fcd629587c02d24e17,0x6b55ffff1288f670939b,0x8f21e82297ab9dd9093e,0x4ddbc61cbc3afaf8f4a8,0x4df0b089cdce57e59f07,0x86c3d3539c4b7e45ec5d,0xb39d466ed87136d69f9,0x81fe411ee65eef881021,0xc3413376d05bafaf8f54,0x77ba83a5c4d614b0ade0,0x16a8a10fb8cd28e7c8fb,0x34927d3fcbcaebe274d1,0x27b7c8dc2341eb3290e6,0x58bc63f82c0580121001],[0x1e4e56ec9e2f1826,0xf1ff7cae27f076ed550d,0x9dc8b8c78743db7d9e97,0x64e449e03ffe5ee2d0f4,0xb37db3535a3500b735c2,0x1be6e1246356404b2adb,0xb7ff42098563e218e279,0x8147bf44deea5127de49,0x404844afb0f168e9cfb5,0x81cc963f3458ed7625d5,0x92b1fc3c178466576432,0xa423b8e54396259928c2,0x60cb6bdfd626c315e528,0xdd101cf9f7e0b5165754,0x69d140f22cea30131001],[0x135c016c3b10,0xf554dd392300657a52d0,0xd5e7867a1e96730099dc,0xed72c9a1645497f6c18e,0x9c601cb55578d3f953d8,0x5e60949104dc30922500,0xdd379af431cc586a5df6,0x61c222847dc0745b4b87,0x5dbf515f7067b3bee69b,0x716d5ce54d7df8f95211,0xeb539cb4d418de6c4179,0x1463880d58f3df012d2c,0x758e4d75b51df307d277,0xb04d4b98ce51bc94e6fe,0x5b90d23c9f6c00141001],[0x2d24569a1b3c75b79,0xaa0e5196e51e06f12f46,0xc24726ff9ddf54692a9b,0x2ae66c708bdc7eacd6e2,0x4731e05b6b16d1cc439b,0x1d91a7fe132061b8da64,0xaa1951cd086e7140ee6c,0xf17de6547f40ada45213,0xba367d719585b709ae90,0x6cd65bd748d2df3423e,0x6225e63462235427d3e0,0xbfaa4a603bda520e03b3,0xa07981caf8d51725f635,0xc7005a4127516778d202,0xf13b3b2da74c00102001],[0x18d086a5d8458c29c,0xf1704a06a8f698e5b6e8,0x158f40fae195cb1120fb,0x5dacc23551dc315453f8,0xada9f403f575b01e06bc,0x6daaa4fa6944d5fb7716,0x9a7606c6542d95a847d5,0x45a905397be50858a6e4,0x129b78757d15f8512072,0xd1d9c2cc9d7f74da124d,0xba2312a548bc4bd5251f,0xec027ede465a661552c8,0x6ac13f1ce1f7662396bd,0x98f63ecff7af6a9626ae,0x7de057555f1d00112001],[0x2da1372d510142f6,0xc73be83bcac7a58aaab5,0xb91c11b918a5d44f58e6,0x39b220feae9a81392ab8,0x77f17a64cc6f40848c,0xd637d49fdda2eea32b57,0xc20592c4e77a10b647bf,0x8cdcd98b231a4cf17ac1,0x562bcdb4c9a2490759c9,0x37363b7029dca97bd224,0xeec437de2613accccac6,0xa938b98337cdde49c67b,0x2750557fde0ca14f0fe0,0x39ab286dfef487d003f5,0xcd358221d6bc00122001],[0x28858b1743d5097,0x53318356c163624ed6af,0x1991d94799d6f2892890,0x50f61f3dd5caba424850,0xd4b1a0fc457958220ee0,0xd4d3b65e95298bf745a7,0x12a51b96b3b005fc81c3,0xb265c9c4446b077f3ba,0xb00d80df8087f294c6a0,0x42f5ec1974beca9a1784,0xd5a01c2d82e4628ea2be,0xbb13214e2ab698bbc3b,0xc757f0c612db2dde4c86,0xe5940b58d1e5e1600377,0x5ccd601c307e0003001],[0x442beed4c1cb19d,0x462fe1ec5513db986a93,0x837f717bf1e650fc6f06,0x848336535054662b6430,0x7acdd8c03cf0bd248e3c,0x90eecc3577573b32efe1,0x8bcb9490503242785936,0xa304a250ee19eb8d8153,0x33902304a5d547bda096,0x693736fb6994ba276c51,0x34880bfa538b7b26ff0e,0xc9e06ae3f2bd163f8c79,0xd20cbf855ded037cfc05,0xf1e541cad98ccc8095e1,0x2466a396390910113001],[0x13bce29c924fea6,0xf2205ab78129c5ed26fb,0x76f582ffe68998ece49,0xacd66ae60f3414e47e15,0x900f45b3ef0fa6c59c40,0xf1d7df9f90a90b197c76,0x90392ced2e4610896f22,0xaaf0fcf92bd46fdcc1aa,0x4a3bec72597d9d7fb727,0x822e00b72520acd1566,0x9b46832fc67185aef821,0x40c62e84fc3a351f0864,0xf8e2fb4b89c73fcf0488,0x78593fb47ad8e7fff579,0xc5efc2ef1e4280104001],[0x1b14f2cda98f9206,0x988a74337cbb57c057ff,0xd0f36d85ca1ef960a1ff,0x7f89d8697e79bed03574,0x601fe104d83e30facf64,0x59cfd74a3ac5cf51fb6a,0x960224a7eeccfc68ace0,0x40997f9e8f3137302765,0x3f55a0d1bb449e32de3f,0x808ec0c5e7b3585434b6,0xa1fad432850c5bd9ab27,0x3b6a00f1dbffe9f9af13,0xb7dd629d8070a8e5d562,0x68875bc94d768bf3725c,0x58c78b59e1ca80000011],[0x36f35fcd4b65e3d,0x7d6eb216969ae6c2f57c,0x5c5fca8d2833936d3e35,0xfec7704586b66403b9f,0xb6708099902e32e3dffc,0xf62ad71ad749994f026d,0x6fa05af8eb3c1e3eb253,0x9ed68f3cd660fcfa141e,0xbececa9969f75de75d48,0x5aea05130b45925faf09,0x5473d0de2142673d0066,0xa4c44bea57bcced95eb4,0x75094ed4a853c432c880,0xb5a014141a9349a9f578,0xfbedc17a2b4080010011],[0x1e6b08236b0f59b,0x9f1420bc71ea52a42563,0x12ba7f2978d2e0c65115,0x187e62a178781b00ccff,0xc612f4d0e7556bb70975,0x5fdc93ad5ee464649ce0,0x8f38adfbc179b0f4dea3,0x6a2d39c2734afa033e34,0xed4eb408cf95da9791e,0x8bb663c9e547b3008b06,0xd9ac77f7e1efdb24da58,0x66d415eb792e234b9e5,0xf54e70f1cf4133641990,0xcfea9c92e02fada6da8d,0xbf41fb0bac4ea0101011],[0x4ee60556599194d5,0xb6d6c45ad51302d999e,0xd2d81ecf9485931e5e21,0x7bbfaf5b103102e5c95e,0x6a2bdd17e68e27f65759,0xfc472dd7f3f2cbdefb4e,0x46bdb10b42602ebaadfd,0x82aa7845cd30eb8af8cc,0xe6620cd81ccca71d22ee,0x3e2719b202da947168af,0x867d6a625498b76a273b,0x8935535a86c70d66fa5d,0x1b71f70f0b08122bd823,0x15c16863e7b7e930604b,0x676edcdb775d40100002],[0x8eead7c9fce3022,0x8081558930485be8219,0x63bc4b38d33a765eacad,0x38823b7eda22e1dc8ada,0xb980db1a06dc00028515,0x91f155365f38e6bc502,0x4af65d420900f4e77e73,0xe5073f57798dcf75212c,0x570cbbdd78ae34be9dd4,0xaf5714e02bc4c91b5b80,0x56286083dfa81f48d350,0xbafea6910ae2781327f6,0x31ca2d089b0b6f1554e5,0x4e1106b7d8f412dc46a8,0xe772756cbb7360010002],[0x3c744bfd62efcb9,0xf3be05da9de73fad6ae6,0xea3584639837a9e4d270,0xc616b046bac2f995d3e7,0xca2dec1d34aaede3dd5c,0x798a9c8163dfcb6038a1,0x3f16f65e0bf364f8d5b3,0x24663bfbce5609a1de40,0xa8c0782442d3b13951a7,0xbd4fbc0c62f36d7fc1f1,0x6d6379c36c34666a87ae,0x9da492879d1eef06cfd3,0x254bcf992b8655f08739,0x81cf94d9920056f9303a,0x4a3d3129784c40020002],[0xf303e91614426aa,0x28f84fef7f996ff7d4e1,0x2648bbc39b1426379464,0x7363103d5cdc4a200544,0x9750c7f5a9f0e5b4ba9e,0xbba2c737bcb68f29eb4b,0x9597127477f21b3498c9,0xbf814afd301b8a57b57b,0xbdf51b7fb3965882fcff,0x3dae68628fa632cfc93a,0xaa6230a6fbdf331a163e,0xaf11cb9b441cd1f17f02,0x7c8ebafeafd8df100930,0xa954da49fcb7a917e8fe,0x6b3023978b0f60101002],[0x3d19816bdbb86d6,0x7dd206d8f53cb9ddcf7e,0x22e19c06ca1b7da9b82a,0xd3487376dd6a8ee7aebf,0xa420c535e2ec689bdb29,0xce5bc7a8d0e19970c172,0xe30d7d2fb9f121b712f4,0xe425afcb768e667a5757,0xbf7f833cdded3cfe25f4,0x49672e97966b58044fdd,0x69368884820cfc92fe66,0x191e9b9077252713500e,0x265e972edbdab5b7c8ee,0xf217662289693cce92cd,0xb0e089e8191640011002],[0x5b63d99d3c4bde4,0xc573d1dbf8222c789741,0xfc8b44096e9d053b2b32,0xca5dae4f5c644b2a12a8,0x79fa9a6046b77da3b1b0,0x577c51d0239cc8906abc,0x50ce504691274d22c128,0x7c540ace24119c1de2d2,0x12aa452621895f538580,0x64a947398e5f421bea31,0x51ef28c8371aaac14d32,0xec8966a760ce3fc93bd1,0x92d89200131013924a5e,0x92fc6026a3020cd5f3d2,0x315c7a3a6fa880002002]]).map tailNat

namespace CubeRecovery

abbrev Term5 := Nat × Nat × Nat × Nat × Nat × Int
abbrev Term3 := Nat × Nat × Nat × Int

structure V where
  a : Int
  d : Int
  c : Int
  cd : Int
  deriving Inhabited, DecidableEq

def z : V := ⟨0,0,0,0⟩
def add (x y : V) : V := ⟨x.a+y.a,x.d+y.d,x.c+y.c,x.cd+y.cd⟩
def sub (x y : V) : V := ⟨x.a-y.a,x.d-y.d,x.c-y.c,x.cd-y.cd⟩
def scale (k : Int) (x : V) : V :=
  if k == 0 then z else ⟨k*x.a,k*x.d,k*x.c,k*x.cd⟩

def bits : Nat := 1216
def pos (b e j : Nat) : Nat := (b*120 + e*12 + j)*bits

def groupTerms (xs : List Term5) : Array Int :=
  xs.foldl (fun acc (b,c,d,e,j,k) =>
    acc.modify (8*c+d) (fun a => a + k.shiftLeft (pos b e j))) (Array.replicate 40 0)

def readRelation (ts : List Term5) : V :=
  let g := groupTerms ts
  ⟨g[0]!, g[1]!, g[8]!, g[9]!⟩

structure Rules where
  d2 : V
  c2 : V
  cd2 : V
  dc2 : V

def makeRules (d2 c2 : V) : Rules :=
  let cd2 := add ⟨0,0,d2.a,d2.d⟩ (scale d2.c c2)
  let dc2 := add (add ⟨0,c2.a,0,c2.c⟩ (scale c2.d d2)) (scale c2.cd cd2)
  ⟨d2,c2,cd2,dc2⟩

def stepD (r : Rules) (x : V) : V :=
  add (add ⟨0,x.a,0,x.c⟩ (scale x.d r.d2)) (scale x.cd r.cd2)

def stepC (r : Rules) (x : V) : V :=
  add (add ⟨0,0,x.a,x.d⟩ (scale x.c r.c2)) (scale x.cd r.dc2)

def mulV (r : Rules) (x y : V) : V :=
  let dy := stepD r y
  add (add (scale x.a y) (scale x.d dy))
    (add (scale x.c (stepC r y)) (scale x.cd (stepC r dy)))

def evalV (r : Rules) (xs : List Term5) : V :=
  let g := groupTerms xs
  (List.range 5).foldr (fun c last =>
    let q := (List.range 8).foldr (fun d acc =>
      let u := stepD r acc
      {u with a := u.a + g[8*c+d]!}) z
    add q (stepC r last)) z

def det (x y s t : V) : Int :=
  (x.a*y.d-x.d*y.a)*(s.c*t.cd-s.cd*t.c) -
  (x.a*y.c-x.c*y.a)*(s.d*t.cd-s.cd*t.d) +
  (x.a*y.cd-x.cd*y.a)*(s.d*t.c-s.c*t.d) +
  (x.d*y.c-x.c*y.d)*(s.a*t.cd-s.cd*t.a) -
  (x.d*y.cd-x.cd*y.d)*(s.a*t.c-s.c*t.a) +
  (x.c*y.cd-x.cd*y.c)*(s.a*t.d-s.d*t.a)

def digits (bias : Int) : Nat → Nat → Int → List Term3 → List Term3
  | 0, _, _, acc => acc.reverse
  | fuel+1, m, x, acc =>
    if x == 0 then acc.reverse else
      let next := (x + bias).shiftRight bits
      let k := x - next.shiftLeft bits
      let ys := if k == 0 then acc else (m / 120, (m / 12) % 10, m % 12, k) :: acc
      digits bias fuel (m+1) next ys

def recoverWith (r : Rules) (target g6 g7 g8 g9 s7 s8 s9 : List Term5) (den : Nat) :
    List (List Term3) :=
  let x := evalV r g6
  let y := stepD r x
  let s := stepC r x
  let t := stepC r y
  let residual := sub (scale (den : Int) (evalV r target))
    (add (mulV r (evalV r s7) (evalV r g7))
      (add (mulV r (evalV r s8) (evalV r g8)) (mulV r (evalV r s9) (evalV r g9))))
  let div := det x y s t
  let read := fun n => digits ((1 : Int).shiftLeft (bits-1)) 720 0 (n / div) []
  [read (det residual y s t), read (det x residual s t),
   read (det x y residual t), read (det x y s residual)]

def termsOf (p : Tower 5) : List Term5 :=
  p.zipIdx.flatMap (fun (pb,b) =>
    pb.zipIdx.flatMap (fun (pc,c) =>
      pc.zipIdx.flatMap (fun (pd,d) =>
        pd.zipIdx.flatMap (fun (pe,e) =>
          pe.zipIdx.filterMap (fun (k,j) =>
            if k == 0 then none else some (b,c,d,e,j,k))))))
    
def srcH : List Term5 :=
  (termsOf w0NegH).map (fun (b,c,d,e,j,k) => (b,c,d,e,j, k / (-w0Den)))
def srcG4 : List Term5 := termsOf SparseCubes.Chart.Chart1.Reflection.pm4k
def srcG5 : List Term5 := termsOf SparseCubes.Chart.Chart1.Reflection.pm5k
def srcG6 : List Term5 := termsOf SparseCubes.Chart.Chart1.Reflection.pm6k
def srcG7 : List Term5 := termsOf SparseCubes.Chart.Chart1.Reflection.pm7k
def srcG8 : List Term5 := termsOf SparseCubes.Chart.Chart1.Reflection.pm8k
def srcG9 : List Term5 := termsOf SparseCubes.Chart.Chart1.Reflection.pm9k

def chartRules : Rules :=
  let r4 := readRelation srcG4
  let a := (1 : Int).shiftLeft (pos 1 0 0) + (2 : Int).shiftLeft (pos 0 1 1) +
    (18 : Int).shiftLeft (pos 0 1 0) + (1 : Int).shiftLeft (pos 0 0 2) +
    (6 : Int).shiftLeft (pos 0 0 1)
  let r5 := sub (readRelation srcG5) (add (scale a r4) ⟨0,2*r4.a,0,2*r4.c⟩)
  makeRules (scale (-1) r4) r5

def candidateLists (den : Nat) (s7 s8 s9 : List Term5) : List (List Term3) :=
  recoverWith chartRules srcH srcG6 srcG7 srcG8 srcG9 s7 s8 s9 den

def candidateRows (den : Nat) (s7 s8 s9 : List Term5) : List Term5 :=
  (candidateLists den s7 s8 s9).zipIdx.flatMap (fun (row,i) =>
    row.map (fun (b,e,j,k) => (b, i / 2, i % 2, e, j, k)))

end CubeRecovery

namespace Packed

def valI {α : Type} (f : α → Int) (z : Int) : List α → Int
  | [] => 0
  | a::as => f a + z*valI f z as

def atInt : (n : Nat) → Tower n → (Nat → Int) → Int
  | 0, a, _ => a
  | n+1, xs, v => valI (fun a => atInt n a (fun k => v (k+1))) (v 0) xs

def atPoint (bits es js : Nat) : Nat → Int
  | 0 => (2^((bits*js)*es) : Nat)
  | 1 => (2^(bits*js) : Nat)
  | _ => (2^bits : Nat)

def tot {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a::as => f a + tot f as

def peak {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a::as => max (f a) (peak f as)

def mass : (n : Nat) → Tower n → Nat
  | 0,a => a.natAbs
  | n+1,xs => tot (mass n) xs

def deg : (n axis : Nat) → Tower n → Nat
  | 0,_,_ => 0
  | _+1,0,xs => xs.length-1
  | n+1,axis+1,xs => peak (deg n axis) xs

theorem le_tot_mem {α : Type} (f : α → Nat) {x : α} {xs : List α} (h : x ∈ xs) :
    f x ≤ tot f xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp [tot]
    · exact le_trans (ih ht) (Nat.le_add_left _ _)

theorem le_peak_mem {α : Type} (f : α → Nat) {x : α} {xs : List α} (h : x ∈ xs) :
    f x ≤ peak f xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact le_max_left _ _
    · exact le_trans (ih ht) (le_max_right _ _)

theorem cast_valI {α} (f : α → Int) (z : Int) (xs : List α) :
    (valI f z xs : ℝ) = value (fun a => (f a : ℝ)) (z : ℝ) xs := by
  induction xs with
  | nil => simp [valI,value]
  | cons a as ih => simp [valI,value,ih]

theorem cast_atInt (n : Nat) (p : Tower n) (v : Nat → Int) :
    (atInt n p v : ℝ) = interp n p (fun k => (v k : ℝ)) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    change (valI _ _ p : ℝ) = value _ _ p
    rw [cast_valI]
    simp only [ih]

theorem atInt_add (n : Nat) (x y : Tower n) (v : Nat → Int) :
    atInt n (add n x y) v = atInt n x v + atInt n y v := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_add, cast_atInt, interp_add]

theorem atInt_mul (n : Nat) (x y : Tower n) (v : Nat → Int) :
    atInt n (mul n x y) v = atInt n x v * atInt n y v := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, cast_atInt, interp_mul]

private theorem radix_zero {α : Type} (B : Nat) (pos : 0 < B) (f : α → Int) (xs : List α)
    (bound : ∀ a ∈ xs, (f a).natAbs < B) (zero : valI f (B : Int) xs = 0) :
    ∀ a ∈ xs, f a = 0 := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    change f a + (B : Int)*valI f (B : Int) as = 0 at zero
    have dvd : (B : Int) ∣ f a := ⟨-valI f B as, by rw [Int.mul_neg]; omega⟩
    have ha : f a = 0 := by
      by_contra h
      have d : B ∣ (f a).natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr dvd
      exact (Nat.not_lt_of_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr h) d)) (bound a (by simp))
    have ne : (B : Int) ≠ 0 := by omega
    rw [ha,zero_add,mul_eq_zero] at zero
    have tail := ih (fun c hc => bound c (by simp [hc])) (zero.resolve_left ne)
    intro c hc
    rcases List.mem_cons.mp hc with rfl | ht
    · exact ha
    · exact tail c ht

private theorem radix_mag {α : Type} (B : Nat) (f : α → Int) (xs : List α)
    (bound : ∀ a ∈ xs, (f a).natAbs < B) :
    (valI f (B : Int) xs).natAbs < B^xs.length := by
  induction xs with
  | nil => simp [valI]
  | cons a as ih =>
    have h₁ := bound a (by simp)
    have h₂ : (valI f (B : Int) as).natAbs+1 ≤ B^as.length :=
      ih (fun c hc => bound c (by simp [hc]))
    have h₃ := Nat.mul_le_mul_left B h₂
    rw [Nat.mul_add, Nat.mul_one] at h₃
    have h₄ := Int.natAbs_add_le (f a) ((B : Int)*valI f B as)
    rw [Int.natAbs_mul, Int.natAbs_natCast] at h₄
    change (f a+(B : Int)*valI f B as).natAbs < B^(as.length+1)
    rw [pow_succ,Nat.mul_comm (B^as.length) B]
    omega

theorem interp_zero (bits es js : Nat) (p : Tower 3) (v : Nat → ℝ)
    (hm : mass 3 p < 2^bits) (he : deg 3 1 p < es) (hj : deg 3 2 p < js)
    (hz : atInt 3 p (atPoint bits es js) = 0) : interp 3 p v = 0 := by
  let J := 2^bits
  let E := 2^(bits*js)
  let B := 2^((bits*js)*es)
  let row := valI (fun x : Int => x) (J : Int)
  let plane := valI row (E : Int)
  change valI plane (B : Int) p = 0 at hz
  change tot (tot (tot Int.natAbs)) p < J at hm
  change peak (fun t : List (List Int) => t.length-1) p < es at he
  change peak (peak (fun t : List Int => t.length-1)) p < js at hj
  have mag (t) (ht : t ∈ p) (r) (hr : r ∈ t) (x) (hx : x ∈ r) : Int.natAbs x < J := by
    exact lt_of_le_of_lt (le_trans (le_tot_mem _ hx) (le_trans (le_tot_mem _ hr) (le_tot_mem _ ht))) hm
  have rowMag (t) (ht : t ∈ p) (r) (hr : r ∈ t) : (row r).natAbs < E := by
    have hlen : r.length ≤ js := by
      have s := le_trans (le_peak_mem (fun q : List Int => q.length-1) hr) (le_peak_mem _ ht)
      omega
    have s := radix_mag J (fun x : Int => x) r (mag t ht r hr)
    change (row r).natAbs < 2^(bits*js)
    rw [Nat.pow_mul]
    exact lt_of_lt_of_le s (Nat.pow_le_pow_right (by positivity) hlen)
  have planeMag (t) (ht : t ∈ p) : (plane t).natAbs < B := by
    have hlen : t.length ≤ es := by
      have s := le_peak_mem (fun q : List (List Int) => q.length-1) ht
      omega
    have s := radix_mag E row t (rowMag t ht)
    change (plane t).natAbs < 2^((bits*js)*es)
    rw [Nat.pow_mul]
    exact lt_of_lt_of_le s (Nat.pow_le_pow_right (by positivity) hlen)
  have hp := radix_zero B (by dsimp [B]; positivity) plane p planeMag hz
  apply interp_of_isZero
  change p.all (fun t => t.all (fun r => r.all (fun z => z == (0 : Int)))) = true
  simp only [List.all_eq_true, beq_iff_eq]
  intro t ht r hr x hx
  have ht0 := radix_zero E (by dsimp [E]; positivity) row t (rowMag t ht) (hp t ht)
  exact radix_zero J (by dsimp [J]; positivity) (fun z => z) r (mag t ht r hr) (ht0 r hr) x hx

end Packed


namespace Packed

private theorem tot_plus {α} (f : α → Nat) (plus : α → α → α)
    (h : ∀ a b, f (plus a b) ≤ f a + f b) (xs ys) :
    tot f (plusList plus xs ys) ≤ tot f xs + tot f ys := by
  induction xs generalizing ys with
  | nil => simp [plusList,tot]
  | cons a as ih =>
    cases ys with
    | nil => simp [plusList,tot]
    | cons b bs =>
      simp only [plusList, tot]
      have s := h a b
      have t := ih bs
      omega

private theorem tot_map {α} (f : α → Nat) (mul : α → α → α)
    (h : ∀ a b, f (mul a b) ≤ f a * f b) (a xs) :
    tot f (xs.map (mul a)) ≤ f a * tot f xs := by
  induction xs with
  | nil => simp [tot]
  | cons b bs ih =>
    simp only [List.map_cons,tot,Nat.mul_add]
    exact Nat.add_le_add (h a b) ih

private theorem tot_times {α} (f : α → Nat) (plus mul : α → α → α) (zero : α)
    (isZ : α → Bool) (hz : f zero = 0) (ha : ∀ a b, f (plus a b) ≤ f a + f b)
    (hm : ∀ a b, f (mul a b) ≤ f a * f b) (xs ys) :
    tot f (timesList plus mul zero isZ ys xs) ≤ tot f xs * tot f ys := by
  induction xs with
  | nil => simp [timesList,tot]
  | cons a as ih =>
    rw [timesList]
    split
    · simp only [tot,hz,zero_add,Nat.add_mul]
      omega
    · apply le_trans (tot_plus f plus ha _ _)
      simp only [tot,hz,zero_add,Nat.add_mul]
      exact Nat.add_le_add (tot_map f mul hm a ys) ih

theorem mass_add_le (n : Nat) (a b : Tower n) :
    mass n (add n a b) ≤ mass n a + mass n b := by
  induction n with
  | zero => exact Int.natAbs_add_le _ _
  | succ n ih => exact tot_plus _ _ ih _ _

theorem mass_pzero (n : Nat) : mass n (pzero n) = 0 := by
  cases n <;> rfl

theorem mass_mul_le (n : Nat) (a b : Tower n) :
    mass n (mul n a b) ≤ mass n a * mass n b := by
  induction n with
  | zero => exact le_of_eq (Int.natAbs_mul _ _)
  | succ n ih => exact tot_times _ _ _ _ _ (mass_pzero n) (mass_add_le n) ih a b

theorem isZero_of_mass_zero (n : Nat) (p : Tower n) (h : mass n p = 0) :
    isZero n p = true := by
  induction n with
  | zero =>
    change Int.natAbs p = 0 at h
    simp [isZero,Int.natAbs_eq_zero.mp h]
  | succ n ih =>
    change p.all (isZero n) = true
    apply List.all_eq_true.mpr
    intro a ha
    exact ih a (Nat.eq_zero_of_le_zero (h ▸ le_tot_mem (mass n) ha))

private theorem len_plus {α} (plus : α → α → α) (xs ys) :
    (plusList plus xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [plusList]
  | cons a as ih =>
    cases ys with
    | nil => simp [plusList]
    | cons b bs => simp [plusList,ih]

private theorem len_times {α} (plus mul : α → α → α) (zero : α)
    (isZ : α → Bool) (xs ys) :
    (timesList plus mul zero isZ ys xs).length-1 ≤ (xs.length-1)+(ys.length-1) := by
  induction xs with
  | nil => simp [timesList]
  | cons a as ih =>
    have h0 : as = [] → (timesList plus mul zero isZ ys as).length = 0 := by
      intro h; simp [h,timesList]
    have ht : (timesList plus mul zero isZ ys as).length ≤ as.length + (ys.length-1) := by
      by_cases hh : as = []
      · simp [h0 hh]
      · have : 0 < as.length := List.length_pos_iff.mpr hh
        omega
    rw [timesList]
    split
    · simpa only [List.length_cons,Nat.add_sub_cancel] using ht
    · rw [len_plus,List.length_map]
      simp only [List.length_cons,Nat.add_sub_cancel]
      omega

private theorem peak_plus {α} (f : α → Nat) (plus : α → α → α)
    (h : ∀ a b, f (plus a b) ≤ max (f a) (f b)) (xs ys) :
    peak f (plusList plus xs ys) ≤ max (peak f xs) (peak f ys) := by
  induction xs generalizing ys with
  | nil => simp [plusList,peak]
  | cons a as ih =>
    cases ys with
    | nil => simp [plusList,peak]
    | cons b bs =>
      simp only [plusList,peak]
      have := h a b
      have := ih bs
      omega

private theorem peak_map {α} (f : α → Nat) (mul : α → α → α)
    (h : ∀ a b, f (mul a b) ≤ f a + f b) (a xs) :
    peak f (xs.map (mul a)) ≤ f a + peak f xs := by
  induction xs with
  | nil => simp [peak]
  | cons b bs ih =>
    simp only [List.map_cons,peak]
    have := h a b
    omega

private theorem peak_times {α} (f : α → Nat) (plus mul : α → α → α) (zero : α)
    (isZ : α → Bool) (hz : f zero = 0) (ha : ∀ a b, f (plus a b) ≤ max (f a) (f b))
    (hm : ∀ a b, f (mul a b) ≤ f a + f b) (xs ys) :
    peak f (timesList plus mul zero isZ ys xs) ≤ peak f xs + peak f ys := by
  induction xs with
  | nil => simp [timesList,peak]
  | cons a as ih =>
    rw [timesList]
    split
    · simp only [peak,hz,Nat.zero_max]
      omega
    · apply le_trans (peak_plus f plus ha _ _)
      simp only [peak,hz,Nat.zero_max]
      have := peak_map f mul hm a ys
      omega

theorem deg_add_le (n axis : Nat) (a b : Tower n) :
    deg n axis (add n a b) ≤ max (deg n axis a) (deg n axis b) := by
  induction n generalizing axis with
  | zero => rfl
  | succ n ih =>
    cases axis with
    | zero => change (plusList _ a b).length - 1 ≤ max (a.length-1) (b.length-1)
              rw [len_plus]; omega
    | succ i => exact peak_plus _ _ (ih i) _ _

theorem deg_pzero (n axis : Nat) : deg n axis (pzero n) = 0 := by
  cases n <;> cases axis <;> rfl

theorem deg_mul_le (n axis : Nat) (a b : Tower n) :
    deg n axis (mul n a b) ≤ deg n axis a + deg n axis b := by
  induction n generalizing axis with
  | zero => rfl
  | succ n ih =>
    cases axis with
    | zero => exact len_times _ _ _ _ a b
    | succ i => exact peak_times _ _ _ _ _ (deg_pzero n i) (deg_add_le n i) (ih i) a b

end Packed

namespace Prefix
structure V (α : Type) where
  k : α
  d : α
  c : α
  cd : α
  deriving Inhabited

abbrev T := Tower 3
abbrev Q := V T
def scalar (n : Int) : T := [[[n]]]
def unit0 : Q := ⟨scalar 1, [], [], []⟩
def unitD : Q := ⟨[], scalar 1, [], []⟩
def unitC : Q := ⟨[], [], scalar 1, []⟩
def unitCD : Q := ⟨[], [], [], scalar 1⟩
def zv : Q := ⟨[], [], [], []⟩
def join (a x : Q) : Q := ⟨add 3 a.k x.k, add 3 a.d x.d, add 3 a.c x.c, add 3 a.cd x.cd⟩
def scale (s : T) (x : Q) : Q := ⟨mul 3 s x.k, mul 3 s x.d, mul 3 s x.c, mul 3 s x.cd⟩
def comb (u x y z t : Q) : Q :=
  join (scale u.k x) (join (scale u.d y) (join (scale u.c z) (scale u.cd t)))

def pt (b e j : ℝ) : Nat → ℝ | 0 => b | 1 => e | _ => j
def ev (p : Q) (b c d e j : ℝ) : ℝ :=
  interp 3 p.k (pt b e j) + d * interp 3 p.d (pt b e j) +
  c * interp 3 p.c (pt b e j) + (c*d) * interp 3 p.cd (pt b e j)


def L : V (Tower 3) := ⟨[[[], [], [-48, -12, -1]], [[12], [-12, -2]]], [[[-12, -12, -1], [-12, -2]], [[-1]]], [[[12, 2], [-1]]], []⟩
def K : V (Tower 3) := ⟨[[[], [], [0, -288, -120, -18, -1], [216, 24]], [[0, 72, 12], [-108, -24, -9, -1], [72, 12, 1]], [[12], [3, 1]]], [[[0, -72, -84, -18, -1], [36, 48, -9, -1], [24]], [[36, 12, 1], [3, 1]]], [[[72, 48, 9, 1], [-96], [9, 1]], [[-3, -1], [1]]], [[[9, 1], [1]]]⟩

def cd2 : Q := join (scale L.k unitC) (join (scale L.d unitCD) (scale L.c K))
def dc2 : Q := comb K unitD L unitCD cd2
def byD (u : Q) : Q := comb u unitD L unitCD cd2
def byC (u : Q) : Q := comb u unitC unitCD K dc2

variable (b c d e j : ℝ)

theorem ev_join (a x : Q) : (fun x => ev x b c d e j) (join a x) = (fun x => ev x b c d e j) a + (fun x => ev x b c d e j) x := by
  simp only [ev, join, interp_add]; ring

theorem ev_scale (t : T) (x : Q) : (fun x => ev x b c d e j) (scale t x) = (fun x => interp 3 x (pt b e j)) t * (fun x => ev x b c d e j) x := by
  simp only [ev, scale, interp_mul]; ring

theorem ev_comb (u x y z t : Q) : (fun x => ev x b c d e j) (comb u x y z t) =
    (fun x => interp 3 x (pt b e j)) u.k * (fun x => ev x b c d e j) x + (fun x => interp 3 x (pt b e j)) u.d * (fun x => ev x b c d e j) y + (fun x => interp 3 x (pt b e j)) u.c * (fun x => ev x b c d e j) z + (fun x => interp 3 x (pt b e j)) u.cd * (fun x => ev x b c d e j) t := by
  simp only [comb, ev_join, ev_scale]; ring

theorem ev_units : (fun x => ev x b c d e j) unit0 = 1 ∧ (fun x => ev x b c d e j) unitD = d ∧ (fun x => ev x b c d e j) unitC = c ∧ (fun x => ev x b c d e j) unitCD = c*d ∧ (fun x => ev x b c d e j) zv = 0 := by
  simp [ev, unit0, unitD, unitC, unitCD, zv, scalar, interp, value]

theorem rules (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun x => ev x b c d e j) L = d^2 ∧ (fun x => ev x b c d e j) K = c^2 := by
  dsimp [ev, L, K, interp, value, pt, w1G0, w1G1, w1T0, w1T1, point] at *
  constructor
  · linear_combination -h0
  · linear_combination h1 - (b+2*d+2*e*j+18*e+j^2+6*j)*h0

theorem ev_cd2 (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun x => ev x b c d e j) cd2 = c*d^2 := by
  obtain ⟨hl,hk⟩ := rules b c d e j h0 h1
  obtain ⟨_,_,hc,hcd,_⟩ := ev_units b c d e j
  rw [cd2, ev_join, ev_join, ev_scale, ev_scale, ev_scale, hc, hcd, hk]
  change (fun x => interp 3 x (pt b e j)) L.k + d * (fun x => interp 3 x (pt b e j)) L.d + c * (fun x => interp 3 x (pt b e j)) L.c + (c*d) * 0 = d^2 at hl
  linear_combination c*hl

theorem ev_dc2 (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun x => ev x b c d e j) dc2 = d*c^2 := by
  obtain ⟨hl,hk⟩ := rules b c d e j h0 h1
  obtain ⟨_,hd,_,hcd,_⟩ := ev_units b c d e j
  rw [dc2, ev_comb, hd, hl, hcd, ev_cd2 b c d e j h0 h1]
  unfold ev at hk
  linear_combination d*hk

theorem ev_byD (u : Q) (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun x => ev x b c d e j) (byD u) = d* (fun x => ev x b c d e j) u := by
  obtain ⟨hl,_⟩ := rules b c d e j h0 h1
  obtain ⟨_,hd,_,hcd,_⟩ := ev_units b c d e j
  rw [byD, ev_comb, hd, hl, hcd, ev_cd2 b c d e j h0 h1]; unfold ev; ring

theorem ev_byC (u : Q) (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun x => ev x b c d e j) (byC u) = c* (fun x => ev x b c d e j) u := by
  obtain ⟨_,hk⟩ := rules b c d e j h0 h1
  obtain ⟨_,_,hc,hcd,_⟩ := ev_units b c d e j
  rw [byC, ev_comb, hc, hcd, hk, ev_dc2 b c d e j h0 h1]; unfold ev; ring


def ejLift (u : Tower 2) : Q := ⟨[u], [], [], []⟩
end Prefix

namespace Prefix
structure PackLaws where
  val : T → Int
  mass : T → Nat
  eDeg : T → Nat
  jDeg : T → Nat
  limit : Nat
  eWidth : Nat
  jWidth : Nat
  val_add : ∀ a b, val (add 3 a b) = val a + val b
  val_mul : ∀ a b, val (mul 3 a b) = val a * val b
  mass_add : ∀ a b, mass (add 3 a b) ≤ mass a + mass b
  mass_mul : ∀ a b, mass (mul 3 a b) ≤ mass a * mass b
  e_add : ∀ a b, eDeg (add 3 a b) ≤ max (eDeg a) (eDeg b)
  j_add : ∀ a b, jDeg (add 3 a b) ≤ max (jDeg a) (jDeg b)
  e_mul : ∀ a b, eDeg (mul 3 a b) ≤ eDeg a + eDeg b
  j_mul : ∀ a b, jDeg (mul 3 a b) ≤ jDeg a + jDeg b
  mass_zero : ∀ a, mass a = 0 → ∀ v, interp 3 a v = 0
  faithful : ∀ a, mass a < limit → eDeg a < eWidth → jDeg a < jWidth →
    val a = 0 → ∀ v, interp 3 a v = 0

structure Tracked (F : PackLaws) where
  p : T
  v : Int
  m : Nat
  e : Nat
  j : Nat
  hv : F.val p = v
  hm : F.mass p ≤ m
  he : F.eDeg p ≤ e
  hj : F.jDeg p ≤ j

variable (F : PackLaws)

def box (p : T) : Tracked F := ⟨p,F.val p,F.mass p,F.eDeg p,F.jDeg p,rfl,le_rfl,le_rfl,le_rfl⟩
def plusT (x y : Tracked F) : Tracked F :=
  if x.m = 0 then y else if y.m = 0 then x else
  ⟨add 3 x.p y.p, x.v+y.v,x.m+y.m,max x.e y.e,max x.j y.j,
   (F.val_add _ _).trans (congrArg₂ (·+·) x.hv y.hv),
   (F.mass_add _ _).trans (Nat.add_le_add x.hm y.hm),
   (F.e_add _ _).trans (max_le_max x.he y.he), (F.j_add _ _).trans (max_le_max x.hj y.hj)⟩
def timesT (x y : Tracked F) : Tracked F :=
  if x.m = 0 ∨ y.m = 0 then box F [] else
  ⟨mul 3 x.p y.p,x.v*y.v,x.m*y.m,x.e+y.e,x.j+y.j,
   (F.val_mul _ _).trans (congrArg₂ (·*·) x.hv y.hv),
   (F.mass_mul _ _).trans (Nat.mul_le_mul x.hm y.hm),
   (F.e_mul _ _).trans (Nat.add_le_add x.he y.he), (F.j_mul _ _).trans (Nat.add_le_add x.hj y.hj)⟩

theorem scalar_mass_zero (x : Tracked F) (h : x.m = 0) (v) : interp 3 x.p v = 0 :=
  F.mass_zero x.p (Nat.eq_zero_of_le_zero (h ▸ x.hm)) v

theorem interp_plusT (x y : Tracked F) (v) :
    interp 3 (plusT F x y).p v = interp 3 x.p v + interp 3 y.p v := by
  unfold plusT
  split_ifs with a b
  · simp [scalar_mass_zero F x a]
  · simp [scalar_mass_zero F y b]
  · exact interp_add _ _ _ _

theorem interp_timesT (x y : Tracked F) (v) :
    interp 3 (timesT F x y).p v = interp 3 x.p v * interp 3 y.p v := by
  unfold timesT
  split_ifs with h
  · obtain h|h := h
    · rw [scalar_mass_zero F x h]; simp [box, interp, value]
    · rw [scalar_mass_zero F y h]; simp [box, interp, value]
  · exact interp_mul _ _ _ _

def vbox (u : Q) : V (Tracked F) := ⟨box F u.k, box F u.d, box F u.c, box F u.cd⟩
def eraseQ (u : V (Tracked F)) : Q := ⟨u.k.p,u.d.p,u.c.p,u.cd.p⟩
def aJoin (a x : V (Tracked F)) : V (Tracked F) :=
  ⟨plusT F a.k x.k, plusT F a.d x.d, plusT F a.c x.c, plusT F a.cd x.cd⟩
def aScale (s : Tracked F) (x : V (Tracked F)) : V (Tracked F) :=
  ⟨timesT F s x.k, timesT F s x.d, timesT F s x.c, timesT F s x.cd⟩
def aComb (u x y z t : V (Tracked F)) : V (Tracked F) :=
  aJoin F (aScale F u.k x) (aJoin F (aScale F u.d y) (aJoin F (aScale F u.c z) (aScale F u.cd t)))
def aCD2 := aJoin F (aScale F (box F L.k) (vbox F unitC))
  (aJoin F (aScale F (box F L.d) (vbox F unitCD)) (aScale F (box F L.c) (vbox F K)))
def aDC2 := aComb F (vbox F K) (vbox F unitD) (vbox F L) (vbox F unitCD) (aCD2 F)
def aByD (u : V (Tracked F)) := aComb F u (vbox F unitD) (vbox F L) (vbox F unitCD) (aCD2 F)
def aByC (u : V (Tracked F)) := aComb F u (vbox F unitC) (vbox F unitCD) (vbox F K) (aDC2 F)
def aProd (u x : V (Tracked F)) := aComb F u x (aByD F x) (aByC F x) (aByC F (aByD F x))
def bVar : T := [[],[[1]]]
def aBump (u : V (Tracked F)) := aScale F (box F bVar) u
def aHorner {α} (f : α → V (Tracked F)) (shift : V (Tracked F) → V (Tracked F)) :
    List α → V (Tracked F)
  | [] => vbox F zv
  | x::xs => aJoin F (f x) (shift (aHorner f shift xs))
def aNormD : Tower 3 → V (Tracked F) := aHorner F (fun e => vbox F (ejLift e)) (aByD F)
def aNormC : Tower 4 → V (Tracked F) := aHorner F (aNormD F) (aByC F)
def aNorm5 : Tower 5 → V (Tracked F) := aHorner F (aNormC F) (aBump F)
def aRes (den : Int) (h p2 p3 p4 p5 : Tower 5) (c6 c7 c8 c9 : V (Tracked F)) :=
  aJoin F (aScale F (box F (scalar (-den))) (aNorm5 F h))
    (aJoin F (aProd F c6 (aNorm5 F p2)) (aJoin F (aProd F c7 (aNorm5 F p3))
    (aJoin F (aProd F c8 (aNorm5 F p4)) (aProd F c9 (aNorm5 F p5)))))
def certS (p : Tracked F) : Bool :=
  decide (p.m < F.limit ∧ p.e < F.eWidth ∧ p.j < F.jWidth ∧ p.v = 0)
def certQ (q : V (Tracked F)) := certS F q.k && certS F q.d && certS F q.c && certS F q.cd

theorem interp_certS (p : Tracked F) (h : certS F p = true) (v) : interp 3 p.p v = 0 := by
  simp only [certS, decide_eq_true_eq] at h
  exact F.faithful p.p (p.hm.trans_lt h.1) (p.he.trans_lt h.2.1)
    (p.hj.trans_lt h.2.2.1) (p.hv.trans h.2.2.2) v

variable (b c d e j : ℝ)

theorem av_join (a x : V (Tracked F)) : (fun u => ev (eraseQ F u) b c d e j) (aJoin F a x) = (fun u => ev (eraseQ F u) b c d e j) a + (fun u => ev (eraseQ F u) b c d e j) x := by
  simp only [ev, eraseQ, aJoin, interp_plusT]; ring
theorem av_scale (t : Tracked F) (x : V (Tracked F)) : (fun u => ev (eraseQ F u) b c d e j) (aScale F t x) = (fun (u : Tracked F) => interp 3 (Tracked.p u) (pt b e j)) t * (fun u => ev (eraseQ F u) b c d e j) x := by
  simp only [ev, eraseQ, aScale, interp_timesT]; ring
theorem av_comb (u x y z t : V (Tracked F)) : (fun u => ev (eraseQ F u) b c d e j) (aComb F u x y z t) =
    (fun (u : Tracked F) => interp 3 (Tracked.p u) (pt b e j)) u.k * (fun u => ev (eraseQ F u) b c d e j) x + (fun (u : Tracked F) => interp 3 (Tracked.p u) (pt b e j)) u.d * (fun u => ev (eraseQ F u) b c d e j) y + (fun (u : Tracked F) => interp 3 (Tracked.p u) (pt b e j)) u.c * (fun u => ev (eraseQ F u) b c d e j) z + (fun (u : Tracked F) => interp 3 (Tracked.p u) (pt b e j)) u.cd * (fun u => ev (eraseQ F u) b c d e j) t := by
  simp only [aComb, av_join, av_scale]; ring
theorem ee_box (u : Q) : (fun u => ev (eraseQ F u) b c d e j) (vbox F u) = ev u b c d e j := rfl

theorem av_cd2 : (fun u => ev (eraseQ F u) b c d e j) (aCD2 F) = ev cd2 b c d e j := by
  simp only [aCD2, cd2, av_join, av_scale, ev_join, ev_scale, ee_box]; rfl
theorem av_dc2 : (fun u => ev (eraseQ F u) b c d e j) (aDC2 F) = ev dc2 b c d e j := by
  simp only [aDC2, dc2, av_comb, ev_comb, av_cd2, ee_box]; rfl

theorem av_byD (u) (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun u => ev (eraseQ F u) b c d e j) (aByD F u) = d * (fun u => ev (eraseQ F u) b c d e j) u := by
  trans ev (byD (eraseQ F u)) b c d e j
  · simp only [aByD, byD, av_comb, ev_comb, av_cd2, ee_box]; rfl
  · exact ev_byD b c d e j _ h0 h1
theorem av_byC (u) (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun u => ev (eraseQ F u) b c d e j) (aByC F u) = c * (fun u => ev (eraseQ F u) b c d e j) u := by
  trans ev (byC (eraseQ F u)) b c d e j
  · simp only [aByC, byC, av_comb, ev_comb, av_dc2, ee_box]; rfl
  · exact ev_byC b c d e j _ h0 h1
theorem av_prod (u x) (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun u => ev (eraseQ F u) b c d e j) (aProd F u x) = (fun u => ev (eraseQ F u) b c d e j) u * (fun u => ev (eraseQ F u) b c d e j) x := by
  simp only [aProd, av_comb, av_byC _ _ _ _ _ _ _ h0 h1, av_byD _ _ _ _ _ _ _ h0 h1]
  unfold ev eraseQ; ring

theorem av_bump (u) : (fun u => ev (eraseQ F u) b c d e j) (aBump F u) = b * (fun u => ev (eraseQ F u) b c d e j) u := by
  rw [aBump, av_scale]; simp [box, bVar, interp, value, pt]

theorem av_horner {α} (f : α → V (Tracked F)) (g) (v : ℝ) (xs : List α)
    (hg : ∀ x, (fun u => ev (eraseQ F u) b c d e j) (g x) = v * (fun u => ev (eraseQ F u) b c d e j) x) :
    (fun u => ev (eraseQ F u) b c d e j) (aHorner F f g xs) = value (fun x => (fun u => ev (eraseQ F u) b c d e j) (f x)) v xs := by
  induction xs with
  | nil => exact (ev_units b c d e j).2.2.2.2
  | cons h t ht => rw [aHorner, av_join, hg, ht, value]

theorem av_norm5 (u : Tower 5) (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0) :
    (fun u => ev (eraseQ F u) b c d e j) (aNorm5 F u) = interp 5 u (point b c d e j) := by
  have left (p : Tower 2) : (fun u => ev (eraseQ F u) b c d e j) (vbox F (ejLift p)) =
      interp 2 p (fun n => point b c d e j (n+3)) := by
    change ev (ejLift p) b c d e j = _; simp [ev, ejLift, interp, value, pt, point]
  have mid (p : Tower 3) : (fun u => ev (eraseQ F u) b c d e j) (aNormD F p) =
      interp 3 p (fun n => point b c d e j (n+2)) := by
    simp only [aNormD, av_horner F b c d e j _ _ d _ (fun x => av_byD F b c d e j x h0 h1),
      left, interp, point]
  have outer (p : Tower 4) : (fun u => ev (eraseQ F u) b c d e j) (aNormC F p) =
      interp 4 p (fun n => point b c d e j (n+1)) := by
    simp only [aNormC, av_horner F b c d e j _ _ c _ (fun x => av_byC F b c d e j x h0 h1),
      mid, interp, point]
  simp only [aNorm5, av_horner F b c d e j _ _ b _ (fun x => av_bump F b c d e j x),
    outer, interp, point]

theorem av_certQ (q) (h : certQ F q = true) : (fun u => ev (eraseQ F u) b c d e j) q = 0 := by
  simp only [certQ, Bool.and_eq_true] at h
  simp only [ev, eraseQ, interp_certS _ _ h.1.1.1, interp_certS _ _ h.1.1.2,
    interp_certS _ _ h.1.2, interp_certS _ _ h.2, mul_zero, add_zero]
theorem tracked_excludes (den : Int) (h p2 p3 p4 p5 : Tower 5) (c6 c7 c8 c9)
    (hd : (den : ℝ) ≠ 0) (h0 : w1G0 b c d e j = 0) (h1 : w1G1 b c d e j = 0)
    (h2 : interp 5 p2 (point b c d e j) = 0) (h3 : interp 5 p3 (point b c d e j) = 0)
    (h4 : interp 5 p4 (point b c d e j) = 0) (h5 : interp 5 p5 (point b c d e j) = 0)
    (chk : certQ F (aRes F den h p2 p3 p4 p5 c6 c7 c8 c9) = true) :
    interp 5 h (point b c d e j) = 0 := by
  have pass := av_certQ F b c d e j _ chk
  simp only [aRes, av_join, av_scale, av_prod _ _ _ _ _ _ _ _ h0 h1,
    av_norm5 _ _ _ _ _ _ _ h0 h1, h2, h3, h4, h5, mul_zero, add_zero] at pass
  have base : interp 3 (box F (scalar (-den))).p (pt b e j) = -(den:ℝ) := by
    simp [box,scalar,interp,value]
  rw [base] at pass
  exact (mul_eq_zero.mp pass).resolve_left (neg_ne_zero.mpr hd)
end Prefix

namespace Prefix
def actual : PackLaws where
  val := fun p => Packed.atInt 3 p (Packed.atPoint 1240 18 20)
  mass := Packed.mass 3
  eDeg := Packed.deg 3 1
  jDeg := Packed.deg 3 2
  limit := 2^1240
  eWidth := 18
  jWidth := 20
  val_add := fun _ _ => Packed.atInt_add 3 _ _ _
  val_mul := fun _ _ => Packed.atInt_mul 3 _ _ _
  mass_add := Packed.mass_add_le 3
  mass_mul := Packed.mass_mul_le 3
  e_add := Packed.deg_add_le 3 1
  j_add := Packed.deg_add_le 3 2
  e_mul := Packed.deg_mul_le 3 1
  j_mul := Packed.deg_mul_le 3 2
  mass_zero := fun a h v => interp_of_isZero 3 a v (Packed.isZero_of_mass_zero 3 a h)
  faithful := fun a hm he hj hz v => Packed.interp_zero 1240 18 20 a v hm he hj hz
end Prefix

private def coeffAt {α : Type} (z : α) (f : α → α) : Nat → List α → List α
  | 0, [] => [f z]
  | 0, x :: xs => f x :: xs
  | n+1, [] => z :: coeffAt z f n []
  | n+1, x :: xs => x :: coeffAt z f n xs

private def curvePoly5 (ts : List CubeRecovery.Term5) : Tower 5 :=
  ts.foldl (fun p (b,c,d,e,j,v) =>
    coeffAt [] (coeffAt [] (coeffAt [] (coeffAt [] (coeffAt 0 (· + v) j) e) d) c) b p) []

private def curvePoly3 (ts : List CubeRecovery.Term3) : Tower 3 :=
  ts.foldl (fun p (b,e,j,v) =>
    coeffAt [] (coeffAt [] (coeffAt 0 (· + v) j) e) b p) []

private def curve7 := suffix7.map unpack
private def curve8 := suffix8.map unpack
private def curve9 := suffix9.map unpack

private def curve6 : Prefix.Q :=
  let rows := CubeRecovery.candidateLists suffixDen curve7 curve8 curve9
  ⟨curvePoly3 (rows.getD 0 []), curvePoly3 (rows.getD 1 []),
   curvePoly3 (rows.getD 2 []), curvePoly3 (rows.getD 3 [])⟩

private def curveH : Tower 5 := [[[], [], [[], [], [], [[-27]]], [[[], [], [], [-27]], [[], [-81]]], [[[27]]]], [[], [], [[], [[], [], [27]], [[-27]]], [[[], [-54]]]], [[], [], [[[], [], [27]]]], [[[], [], [], [[4]]], [[[], [], [], [4]], [[], [12]]], [[[-4]]]], [[[], [[], [], [-4]], [[4]]], [[[], [8]]]], [[[[], [], [-4]]]]]

private theorem curveH_interp (b c d e j : ℝ) :
    interp 5 curveH (point b c d e j) = chartH b c d e j := by
  simp only [curveH, interp, value, point, chartH, Int.cast_ofNat, Int.cast_neg,
    zero_add, add_zero, mul_zero, mul_one] <;> ring

private def curveCheck : Bool :=
  let F := Prefix.actual
  Prefix.certQ F (Prefix.aRes F (suffixDen : Int) curveH w1T2 w1T3 w1T4 w1T5
    (Prefix.vbox F curve6)
    (Prefix.aNorm5 F (curvePoly5 curve7))
    (Prefix.aNorm5 F (curvePoly5 curve8))
    (Prefix.aNorm5 F (curvePoly5 curve9)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem curveCheck_true : curveCheck = true := by decide +kernel

theorem w1_excludes (b c d e j : ℝ)
    (h0 : w1G0 b c d e j = 0)
    (h1 : w1G1 b c d e j = 0)
    (h2 : w1G2 b c d e j = 0)
    (h3 : w1G3 b c d e j = 0)
    (h4 : w1G4 b c d e j = 0)
    (h5 : w1G5 b c d e j = 0) :
    chartH b c d e j = 0 := by
  rw [← curveH_interp]
  apply Prefix.tracked_excludes Prefix.actual b c d e j (suffixDen : Int) curveH
    w1T2 w1T3 w1T4 w1T5 (Prefix.vbox Prefix.actual curve6)
    (Prefix.aNorm5 Prefix.actual (curvePoly5 curve7))
    (Prefix.aNorm5 Prefix.actual (curvePoly5 curve8))
    (Prefix.aNorm5 Prefix.actual (curvePoly5 curve9))
  · exact Int.cast_ne_zero.mpr (by decide)
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact curveCheck_true
end SparseCubes.Certificate

namespace SparseCubes.Chart.Chart1

variable (b c d e j z : ℝ)

theorem ev0 (hz : z^3=b*z+c) : (m0 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 0 := by
  rw [base0]
  exact eval_initialRep b c d e j 1 z hz 0

theorem ev1 (hz : z^3=b*z+c) : (m1 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 1 := by
  rw [base1]
  exact eval_initialRep b c d e j 1 z hz 1

theorem ev2 (hz : z^3=b*z+c) : (m2 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 2 := by
  rw [base2]
  exact eval_initialRep b c d e j 1 z hz 2

theorem ev3 (hz : z^3=b*z+c) : (m3 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 3 := by
  rw [base3]
  exact eval_initialRep b c d e j 1 z hz 3

theorem ev4 (hz : z^3=b*z+c) : (m4 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 4 := by
  rw [step4,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 1 z hz 0 _ _ _ _ (ev3 b c d e j z hz) (ev2 b c d e j z hz) (ev1 b c d e j z hz) (ev0 b c d e j z hz)

theorem ev5 (hz : z^3=b*z+c) : (m5 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 5 := by
  rw [step5,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 1 z hz 1 _ _ _ _ (ev4 b c d e j z hz) (ev3 b c d e j z hz) (ev2 b c d e j z hz) (ev1 b c d e j z hz)

theorem ev6 (hz : z^3=b*z+c) : (m6 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 6 := by
  rw [step6,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 1 z hz 2 _ _ _ _ (ev5 b c d e j z hz) (ev4 b c d e j z hz) (ev3 b c d e j z hz) (ev2 b c d e j z hz)

theorem ev7 (hz : z^3=b*z+c) : (m7 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 7 := by
  rw [step7,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 1 z hz 3 _ _ _ _ (ev6 b c d e j z hz) (ev5 b c d e j z hz) (ev4 b c d e j z hz) (ev3 b c d e j z hz)

theorem ev8 (hz : z^3=b*z+c) : (m8 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 8 := by
  rw [step8,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 1 z hz 4 _ _ _ _ (ev7 b c d e j z hz) (ev6 b c d e j z hz) (ev5 b c d e j z hz) (ev4 b c d e j z hz)

theorem ev9 (hz : z^3=b*z+c) : (m9 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 1 z) 9 := by
  rw [step9,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 1 z hz 5 _ _ _ _ (ev8 b c d e j z hz) (ev7 b c d e j z hz) (ev6 b c d e j z hz) (ev5 b c d e j z hz)

theorem excludes : Case 1 := by
  intro m x d e j hx hc hv hraw hm
  let b := coeffB x
  let c := coeffC x
  have h0 := hraw 0 (by decide)
  change mass m (fun _ => 1) = 0 at h0
  have h1m := hraw 1 (by decide)
  have h1 : mass m x = 0 := by
    simp only [mass,Fin.sum_univ_three,rawMoment] at h1m ⊢
    linear_combination (1/3:ℝ)*h1m
  have hk := mass_quadratic_ne m x b hm hx h0 h1
  apply chartH_ne x d e j hc hx hv
  apply Certificate.w1_excludes
  · have h : mass m (fun i => (m4 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 1 (x i)) 4) :=
               congrArg (mass m) (funext (fun i => ev4 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 4 (by decide)
    rw [mass_rep m x b (m4 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w1G0 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m5 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 1 (x i)) 5) :=
               congrArg (mass m) (funext (fun i => ev5 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 5 (by decide)
    rw [mass_rep m x b (m5 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w1G1 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m6 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 1 (x i)) 6) :=
               congrArg (mass m) (funext (fun i => ev6 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 6 (by decide)
    rw [mass_rep m x b (m6 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w1G2 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m7 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 1 (x i)) 7) :=
               congrArg (mass m) (funext (fun i => ev7 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 7 (by decide)
    rw [mass_rep m x b (m7 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w1G3 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m8 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 1 (x i)) 8) :=
               congrArg (mass m) (funext (fun i => ev8 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 8 (by decide)
    rw [mass_rep m x b (m8 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w1G4 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m9 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 1 (x i)) 9) :=
               congrArg (mass m) (funext (fun i => ev9 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 9 (by decide)
    rw [mass_rep m x b (m9 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w1G5 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)

end SparseCubes.Chart.Chart1

namespace SparseCubes.Chart


theorem distinct_mean_excludes (m x v s : Fin 3 → ℝ) (hm : ∀ i, m i ≠ 0)
    (hx : Function.Injective x) (hv : ∀ i, v i ≠ 0) (hc : ∑ i, x i=0)
    (hz : ∀ n < 10, mass m (fun i => rawMoment (x i) (v i) (s i) n)=0) : False :=
  center_distinct_of_cases Chart0.excludes Chart1.excludes m x v s hm hx hv hc hz

end SparseCubes.Chart

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section


theorem multiplicity_bound :
    ∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ),
      (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) →
      ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 →
      ∀ x : ℝ, 0 < x → Polynomial.rootMultiplicity x
        ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9 := by
  intro s g hsign hsparse hP r hr
  classical
  by_cases hsmall : ∃ i, (g i).support.card ≤ 1
  · exact bound_of_one_small_input s g hsparse hsmall hP r hr
  have htwo (i) : (g i).support.card = 2 := by
    have h := hsparse i
    have h' : ¬(g i).support.card ≤ 1 := fun hi => hsmall ⟨i,hi⟩
    omega
  choose a hpoly hg using fun i => genuine_arm (g i) (htwo i)
  have htotal : total s a = ∑ i, C (s i) * g i^3 := by simp only [total,hpoly]
  have hne : total s a ≠ 0 := htotal ▸ hP
  have hs (i) : s i ≠ 0 := by rcases hsign i with hi|hi <;> rw [hi] <;> norm_num
  rw [← htotal]
  by_contra! h
  have hl := low_of_ten s a r h
  by_cases hz : ∃ i, (a i).value r = 0
  · exact hne (zero_of_any_vanishes s a r hr.ne' hs hg hz hl)
  have hn (i) : (a i).value r ≠ 0 := fun hi => hz ⟨i,hi⟩
  rcases nonvanishing_cases s a r hr.ne' hs hg hn hl with hzero|⟨m,x,v,u,hm,hx,hv,hc,hw⟩
  · exact hne hzero
  · exact Chart.distinct_mean_excludes m x v u hm hx hv hc hw

end
end SparseCubes
end PEqualNP.Outside.L_gct_234

theorem PEqualNP.Outside.L_gct_234 : ∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) → ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 → ∀ x : ℝ, 0 < x → Polynomial.rootMultiplicity x ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9 := PEqualNP.Outside.L_gct_234.SparseCubes.multiplicity_bound
