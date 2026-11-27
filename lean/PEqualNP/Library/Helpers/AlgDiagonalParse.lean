import PEqualNP.Defs
import PEqualNP.Library.L064

/-!
# Reading extension-oracle queries, and evading them

Helper module for `PEqualNP.Library.Helpers.AlgDiagonal` (proofs only). Under the hypothesis
that `algEncodeNat` is prefix-free (`henc`), a query string of `extOracle` names its prime, its
exponent and its arity (`hdr`), and, for an injective naming of field elements, its point
(`ptOf`). From a finite set of query strings, `Yq` collects the points queried at a given arity
in each field, and `evade` (from `L064`) gives one cube point `w` and, in every field, a
polynomial of degree at most 2 in each variable vanishing on the queried points and equal to the
indicator of `w` on the cube.
-/

namespace PEqualNP.Library.Helpers.AlgDiagonalParse

open Classical PEqualNP.Library

/-- The query string naming `p`, `k`, `m`, the point `y` and the bit `j`. -/
def qstr (codes : FieldCodes) (p : ℕ) [Fact p.Prime] (k m : ℕ) (y : Fin m → GaloisField p k)
    (j : ℕ) : List Bool :=
  algEncodeNat p ++ algEncodeNat k ++ algEncodeNat m ++
    (List.ofFn fun i => algEncodeNat (codes p k (y i))).flatten ++ algEncodeNat j

theorem qstr_assoc (codes : FieldCodes) (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (y : Fin m → GaloisField p k) (j : ℕ) :
    qstr codes p k m y j = algEncodeNat p ++ (algEncodeNat k ++ (algEncodeNat m ++
      ((List.ofFn fun i => algEncodeNat (codes p k (y i))).flatten ++ algEncodeNat j))) := by
  simp [qstr, List.append_assoc]

/-- Membership in `extOracle` depends only on the values of the polynomials at the points the
string names. -/
theorem extOracle_congr (codes : FieldCodes) (E E' : AlgExtension) (s : List Bool)
    (h : ∀ (p : ℕ) [Fact p.Prime] (k m : ℕ) (y : Fin m → GaloisField p k) (j : ℕ),
      s = qstr codes p k m y j → MvPolynomial.eval y (E p k m) = MvPolynomial.eval y (E' p k m)) :
    s ∈ extOracle codes E ↔ s ∈ extOracle codes E' := by
  constructor
  · rintro ⟨p, hp, k, m, y, j, hs, hb⟩
    exact ⟨p, hp, k, m, y, j, hs, by rw [← h p k m y j hs]; exact hb⟩
  · rintro ⟨p, hp, k, m, y, j, hs, hb⟩
    exact ⟨p, hp, k, m, y, j, hs, by rw [h p k m y j hs]; exact hb⟩

/-- The header of a string: the three numbers it starts with, when it starts with three. -/
noncomputable def hdr (s : List Bool) : Option (ℕ × ℕ × ℕ) :=
  if h : ∃ t : ℕ × ℕ × ℕ, ∃ r : List Bool,
      s = algEncodeNat t.1 ++ (algEncodeNat t.2.1 ++ (algEncodeNat t.2.2 ++ r))
  then some (Classical.choose h) else none

section
variable (henc : ∀ (a b : ℕ) (s t : List Bool),
  algEncodeNat a ++ s = algEncodeNat b ++ t → a = b ∧ s = t)
include henc

theorem hdr_eq {s : List Bool} {p k m : ℕ} {r : List Bool}
    (hs : s = algEncodeNat p ++ (algEncodeNat k ++ (algEncodeNat m ++ r))) :
    hdr s = some (p, k, m) := by
  have h : ∃ t : ℕ × ℕ × ℕ, ∃ r : List Bool,
      s = algEncodeNat t.1 ++ (algEncodeNat t.2.1 ++ (algEncodeNat t.2.2 ++ r)) :=
    ⟨(p, k, m), r, hs⟩
  rw [hdr, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨r', hr'⟩ := Classical.choose_spec h
  replace hr' := hs.symm.trans hr'
  obtain ⟨h1, hr1⟩ := henc _ _ _ _ hr'
  obtain ⟨h2, hr2⟩ := henc _ _ _ _ hr1
  obtain ⟨h3, -⟩ := henc _ _ _ _ hr2
  exact congrArg some (Prod.ext h1.symm (Prod.ext h2.symm h3.symm))

theorem hdr_qstr (codes : FieldCodes) (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (y : Fin m → GaloisField p k) (j : ℕ) : hdr (qstr codes p k m y j) = some (p, k, m) :=
  hdr_eq henc (qstr_assoc codes p k m y j)

theorem flat_inj (codes : FieldCodes) (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hc : Function.Injective (codes p k)) :
    ∀ (m : ℕ) (y y' : Fin m → GaloisField p k) (j j' : ℕ),
      (List.ofFn fun i => algEncodeNat (codes p k (y i))).flatten ++ algEncodeNat j =
        (List.ofFn fun i => algEncodeNat (codes p k (y' i))).flatten ++ algEncodeNat j' →
      y = y' := by
  intro m
  induction m with
  | zero => intro y y' _ _ _; funext i; exact i.elim0
  | succ m ih =>
    intro y y' j j' h
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc] at h
    obtain ⟨h0, hrest⟩ := henc _ _ _ _ h
    have e0 := hc h0
    have e1 := ih (fun i => y i.succ) (fun i => y' i.succ) j j' hrest
    funext i
    refine Fin.cases e0 (fun i => congrFun e1 i) i

theorem qstr_inj (codes : FieldCodes) (p : ℕ) [Fact p.Prime] (k m : ℕ)
    (hc : Function.Injective (codes p k)) {y y' : Fin m → GaloisField p k} {j j' : ℕ}
    (h : qstr codes p k m y j = qstr codes p k m y' j') : y = y' := by
  rw [qstr_assoc, qstr_assoc] at h
  obtain ⟨-, h1⟩ := henc _ _ _ _ h
  obtain ⟨-, h2⟩ := henc _ _ _ _ h1
  obtain ⟨-, h3⟩ := henc _ _ _ _ h2
  exact flat_inj henc codes p k hc m y y' j j' h3

end

/-- The point a string names in `GaloisField p k ^ n`, when it names one. -/
noncomputable def ptOf (codes : FieldCodes) (p : ℕ) [Fact p.Prime] (k n : ℕ) (s : List Bool) :
    Fin n → GaloisField p k :=
  if h : ∃ (y : Fin n → GaloisField p k) (j : ℕ), s = qstr codes p k n y j
  then Classical.choose h else 0

theorem ptOf_qstr (henc : ∀ (a b : ℕ) (s t : List Bool),
      algEncodeNat a ++ s = algEncodeNat b ++ t → a = b ∧ s = t)
    (codes : FieldCodes) (p : ℕ) [Fact p.Prime] (k n : ℕ)
    (hc : Function.Injective (codes p k)) (y : Fin n → GaloisField p k) (j : ℕ) :
    ptOf codes p k n (qstr codes p k n y j) = y := by
  have h : ∃ (y' : Fin n → GaloisField p k) (j' : ℕ),
      qstr codes p k n y j = qstr codes p k n y' j' := ⟨y, j, rfl⟩
  rw [ptOf, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨j', hj'⟩ := Classical.choose_spec h
  exact (qstr_inj henc codes p k n hc hj').symm

/-- The points of `GaloisField p k ^ n` named by the strings of `Qs`. -/
noncomputable def Yq (codes : FieldCodes) (n : ℕ) (Qs : Finset (List Bool)) (p : ℕ) [Fact p.Prime]
    (k : ℕ) : Finset (Fin n → GaloisField p k) :=
  (Qs.filter fun s => hdr s = some (p, k, n)).image (ptOf codes p k n)

theorem mem_Yq (henc : ∀ (a b : ℕ) (s t : List Bool),
      algEncodeNat a ++ s = algEncodeNat b ++ t → a = b ∧ s = t)
    (codes : FieldCodes) (n : ℕ) (Qs : Finset (List Bool)) (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hc : Function.Injective (codes p k)) (y : Fin n → GaloisField p k) (j : ℕ)
    (hs : qstr codes p k n y j ∈ Qs) : y ∈ Yq codes n Qs p k := by
  rw [Yq, Finset.mem_image]
  exact ⟨_, Finset.mem_filter.mpr ⟨hs, hdr_qstr henc codes p k n y j⟩,
    ptOf_qstr henc codes p k n hc y j⟩

theorem card_Yq (codes : FieldCodes) (n : ℕ) (Qs : Finset (List Bool)) (p : ℕ) [Fact p.Prime]
    (k : ℕ) : (Yq codes n Qs p k).card ≤ (Qs.filter fun s => hdr s = some (p, k, n)).card :=
  Finset.card_image_le

/-- The prime fields-with-exponent named by the strings of `Qs`. -/
noncomputable def names (Qs : Finset (List Bool)) : Finset (ℕ × ℕ) :=
  (Qs.image fun s => ((hdr s).map fun t => (t.1, t.2.1)).getD (0, 0)).filter
    fun pk => pk.1.Prime

theorem names_prime (Qs : Finset (List Bool)) : ∀ pk ∈ names Qs, pk.1.Prime :=
  fun _ h => (Finset.mem_filter.mp h).2

theorem Yq_empty (codes : FieldCodes) (n : ℕ) (Qs : Finset (List Bool)) (p : ℕ) [hp : Fact p.Prime]
    (k : ℕ) (h : (p, k) ∉ names Qs) : Yq codes n Qs p k = ∅ := by
  rw [Yq, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro s hs hh
  apply h
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨s, hs, ?_⟩, hp.out⟩
  rw [hh]
  rfl

theorem sum_filter_le (T : Finset (ℕ × ℕ)) (Qs : Finset (List Bool)) (n : ℕ) :
    ∑ pk ∈ T, (Qs.filter fun s => hdr s = some (pk.1, pk.2, n)).card ≤ Qs.card := by
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _)
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun s ha hb => hab ?_
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    rw [h1] at h2
    have h3 := Option.some.inj h2
    simp only [Prod.mk.injEq] at h3
    exact Prod.ext h3.1 h3.2.1

/-- A polynomial of degree at most 2 in each variable, vanishing on `Y`, equal on the cube to
the indicator of `w`. -/
def Good {F : Type} [Field F] {n : ℕ} (Y : Finset (Fin n → F)) (w : Fin n → Bool)
    (P : MvPolynomial (Fin n) F) : Prop :=
  (∀ i, MvPolynomial.degreeOf i P ≤ 2) ∧ (∀ y ∈ Y, MvPolynomial.eval y P = 0) ∧
    ∀ z : Fin n → Bool, MvPolynomial.eval (fun i => if z i then (1 : F) else 0) P =
      if z = w then 1 else 0

theorem good_empty {F : Type} [Field F] {n : ℕ} (w : Fin n → Bool) :
    ∃ P, Good (∅ : Finset (Fin n → F)) w P :=
  ⟨QueryEvasion.delta w, fun i => (QueryEvasion.degreeOf_delta_le w i).trans (by norm_num),
    by simp, fun z => QueryEvasion.eval_delta w z⟩

/-- `L064` over the fields named by a finite set `T` of pairs. -/
theorem evade (n : ℕ) (T : Finset (ℕ × ℕ)) (hT : ∀ pk ∈ T, pk.1.Prime) (c : ℕ × ℕ → ℕ)
    (Y : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Finset (Fin n → GaloisField p k))
    (hY : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), (Y p k).card ≤ c (p, k))
    (hYT : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), (p, k) ∉ T → Y p k = ∅)
    (hsum : ∑ pk ∈ T, c pk < 2 ^ n) :
    ∃ w : Fin n → Bool, ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), ∃ P, Good (Y p k) w P := by
  let e := T.equivFin
  let f : Fin T.card → ℕ × ℕ := fun j => (e.symm j).1
  have hp : ∀ j, (f j).1.Prime := fun j => hT _ (e.symm j).2
  let Fs : Fin T.card → Type := fun j => @GaloisField (f j).1 ⟨hp j⟩ (f j).2
  let inst : ∀ j, Field (Fs j) := fun j => by
    haveI : Fact (f j).1.Prime := ⟨hp j⟩
    exact inferInstanceAs (Field (GaloisField (f j).1 (f j).2))
  let Ys : ∀ j, Finset (Fin n → Fs j) := fun j => @Y (f j).1 ⟨hp j⟩ (f j).2
  have hs : ∑ j, (Ys j).card < 2 ^ n := by
    calc ∑ j, (Ys j).card ≤ ∑ j, c (f j) :=
          Finset.sum_le_sum fun j _ => @hY (f j).1 ⟨hp j⟩ (f j).2
      _ = ∑ pk ∈ T, c pk := by
          rw [← Finset.sum_coe_sort T c]
          exact Equiv.sum_comp e.symm (fun x : T => c x)
      _ < 2 ^ n := hsum
  obtain ⟨w, hw⟩ := @PEqualNP.Library.L064 n T.card Fs inst Ys hs
  refine ⟨w, fun p _ k => ?_⟩
  by_cases hmem : (p, k) ∈ T
  · have key : ∀ (a : ℕ × ℕ) (ha : a.1.Prime), a = (p, k) →
        (∃ P : MvPolynomial (Fin n) (@GaloisField a.1 ⟨ha⟩ a.2),
          @Good _ (by haveI : Fact a.1.Prime := ⟨ha⟩; exact inferInstance) n
            (@Y a.1 ⟨ha⟩ a.2) w P) → ∃ P, Good (Y p k) w P := by
      rintro a ha rfl h
      exact h
    exact key (f (e ⟨(p, k), hmem⟩)) (hp _) (by simp [f]) (hw (e ⟨(p, k), hmem⟩))
  · rw [hYT p k hmem]
    exact good_empty w

end PEqualNP.Library.Helpers.AlgDiagonalParse
