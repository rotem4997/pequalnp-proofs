import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9702

open PEqualNP.Search PEqualNP.ProofComplexity

abbrev V : Type := Fin 6 × Fin 5

-- Indices of the 81 clauses: pigeon clauses and hole clauses (i, i', j) with i < i'.
abbrev I : Type := Fin 6 ⊕ (Fin 6 × Fin 6 × Fin 5)

abbrev Tr : Type := Finset I × ℕ × ℕ

def pig (i : Fin 6) : Clause V := Finset.univ.image (fun j : Fin 5 => ((i, j), true))

def hole (i i' : Fin 6) (j : Fin 5) : Clause V := {((i, j), false), ((i', j), false)}

def cl : I → Clause V
  | Sum.inl i => pig i
  | Sum.inr t => hole t.1 t.2.1 t.2.2

def okIdx : I → Bool
  | Sum.inl _ => true
  | Sum.inr t => decide (t.1 < t.2.1)

def I0 : Finset I := Finset.univ.filter (fun c => okIdx c = true)

lemma card_I0 : I0.card = 81 := by decide

-- Hole of pigeon p when pigeon i is left out.
def sig (i p : ℕ) : ℕ := if p < i then p else p - 1

-- Hole of pigeon p when pigeons i and i' share hole j.
def gh (i i' j p : ℕ) : ℕ :=
  if p = i' then j else if sig i' p = i then j else if sig i' p = j then i else sig i' p

def asg : I → V → Bool
  | Sum.inl i => fun v => decide (v.1 ≠ i ∧ v.2.val = sig i.val v.1.val)
  | Sum.inr t => fun v => decide (v.2.val = gh t.1.val t.2.1.val t.2.2.val v.1.val)

lemma sig_lt {i p : ℕ} (hi : i ≤ 5) (hp : p ≤ 5) : sig i p < 5 := by
  unfold sig; split_ifs <;> omega

lemma sig_inj {i p q : ℕ} (hp : p ≠ i) (hq : q ≠ i) (h : sig i p = sig i q) : p = q := by
  unfold sig at h; split_ifs at h <;> omega

lemma gh_lt {i i' j p : ℕ} (hii : i < i') (hi' : i' ≤ 5) (hj : j < 5) (hp : p ≤ 5) :
    gh i i' j p < 5 := by
  unfold gh sig; split_ifs <;> omega

lemma gh_coll {i i' j p q x : ℕ} (hii : i < i') (hi' : i' ≤ 5) (hj : j < 5) (hp : p ≤ 5)
    (hq : q ≤ 5) (hpq : p ≠ q) (hv : x = gh i i' j p) (hw : x = gh i i' j q) :
    (p = i ∧ q = i' ∨ p = i' ∧ q = i) ∧ x = j := by
  unfold gh sig at hv hw; split_ifs at hv hw <;> omega

lemma mem_I0_inr {i i' : Fin 6} {j : Fin 5} (h : Sum.inr (i, i', j) ∈ I0) : i < i' := by
  simpa [okIdx] using (Finset.mem_filter.mp h).2

lemma sat_of_ne (c : I) (hc : c ∈ I0) (D : Clause V) (hD : D ∈ PHP 6 5) (hne : cl c ≠ D) :
    ClauseSat (asg c) D := by
  simp only [PHP, Set.mem_union, Set.mem_ofPred_eq] at hD
  rcases hD with ⟨p, rfl⟩ | ⟨p, p', h, hpp, rfl⟩
  · rcases c with i | ⟨i, i', j⟩
    · have hip : i ≠ p := by
        rintro rfl
        exact hne rfl
      refine ⟨((p, ⟨sig i.val p.val, sig_lt (by omega) (by omega)⟩), true),
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      simp [asg, Ne.symm hip]
    · have hii := mem_I0_inr hc
      refine ⟨((p, ⟨gh i.val i'.val j.val p.val,
        gh_lt (Fin.lt_def.mp hii) (by omega) j.isLt (by omega)⟩), true),
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      simp [asg]
  · by_contra hns
    have h1 : asg c (p, h) = true := by
      by_contra h1
      exact hns ⟨((p, h), false), by simp, by simpa using h1⟩
    have h2 : asg c (p', h) = true := by
      by_contra h2
      exact hns ⟨((p', h), false), by simp, by simpa using h2⟩
    rcases c with i | ⟨i, i', j⟩
    · simp only [asg, decide_eq_true_eq] at h1 h2
      apply hpp
      apply Fin.ext
      apply sig_inj (i := i.val)
      · exact fun e => h1.1 (Fin.ext e)
      · exact fun e => h2.1 (Fin.ext e)
      · rw [← h1.2, ← h2.2]
    · have hii := mem_I0_inr hc
      simp only [asg, decide_eq_true_eq] at h1 h2
      have hpq : p.val ≠ p'.val := fun e => hpp (Fin.ext e)
      obtain ⟨hor, hj⟩ := gh_coll (Fin.lt_def.mp hii) (by omega) j.isLt (by omega) (by omega)
        hpq h1 h2
      have hjj : h = j := Fin.ext hj
      subst hjj
      apply hne
      rcases hor with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have : p = i := Fin.ext e1
        have : p' = i' := Fin.ext e2
        subst p p'
        rfl
      · have : p = i' := Fin.ext e1
        have : p' = i := Fin.ext e2
        subst p p'
        exact Finset.pair_comm _ _

lemma cl_inj (a b : I) (ha : a ∈ I0) (hb : b ∈ I0) (h : cl a = cl b) : a = b := by
  rcases a with i | ⟨i, i', j⟩ <;> rcases b with k | ⟨k, k', l⟩
  · have hm : ((i, (0 : Fin 5)), true) ∈ cl (Sum.inl k) := by
      rw [← h]
      simp [cl, pig]
    simp [cl, pig] at hm
    rw [hm]
  · have hm : ((i, (0 : Fin 5)), true) ∈ cl (Sum.inr (k, k', l)) := by
      rw [← h]
      simp [cl, pig]
    simp [cl, hole] at hm
  · have hm : ((i, j), false) ∈ cl (Sum.inl k) := by
      rw [← h]
      simp [cl, hole]
    simp [cl, pig] at hm
  · have hii := Fin.lt_def.mp (mem_I0_inr ha)
    have hkk := Fin.lt_def.mp (mem_I0_inr hb)
    have m1 : ((i, j), false) ∈ cl (Sum.inr (k, k', l)) := by
      rw [← h]; simp [cl, hole]
    have m2 : ((i', j), false) ∈ cl (Sum.inr (k, k', l)) := by
      rw [← h]; simp [cl, hole]
    have m3 : ((k, l), false) ∈ cl (Sum.inr (i, i', j)) := by
      rw [h]; simp [cl, hole]
    simp only [cl, hole, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
      at m1 m2 m3
    simp only [Fin.ext_iff] at m1 m2 m3
    simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega

def slack (e : CPLine V) : ℤ := ∑ v, e.1 v - 5 * e.2

lemma coef_sum (C : Clause V) (w : V → ℤ) :
    ∑ v, (clauseCP C).1 v * w v = ∑ l ∈ C, (if l.2 then 1 else -1) * w l.1 := by
  simp only [clauseCP, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp [ite_mul]

lemma clause_holds (a : V → Bool) (C : Clause V) (h : ClauseSat a C) :
    CPLine.Holds a (clauseCP C) := by
  unfold CPLine.Holds
  rw [coef_sum]
  obtain ⟨l0, hl0, hsat⟩ := h
  have key : (1 : ℤ) ≤ ∑ l ∈ C, ((if l.2 then 1 else -1) * (if a l.1 then 1 else 0)
      + (if l.2 then 0 else 1)) := by
    calc (1 : ℤ) = (if l0.2 then 1 else -1) * (if a l0.1 then 1 else 0)
          + (if l0.2 then 0 else 1) := by
            rw [hsat]; cases l0.2 <;> simp
      _ ≤ _ := Finset.single_le_sum (f := fun l : V × Bool => (if l.2 then 1 else -1)
            * (if a l.1 then 1 else 0) + (if l.2 then (0 : ℤ) else 1))
          (fun l _ => by cases l.2 <;> cases a l.1 <;> simp) hl0
  rw [Finset.sum_add_distrib] at key
  simp only [clauseCP]
  linarith

lemma clause_slack (C : Clause V) (hC : C ∈ PHP 6 5) : 0 ≤ slack (clauseCP C) := by
  have hs : slack (clauseCP C) = ∑ l ∈ C, (if l.2 then 1 else -1)
      - 5 * (1 - ∑ l ∈ C, if l.2 then 0 else 1) := by
    unfold slack
    have := coef_sum C (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    rfl
  rw [hs]
  simp only [PHP, Set.mem_union, Set.mem_ofPred_eq] at hC
  rcases hC with ⟨p, rfl⟩ | ⟨p, p', h, hpp, rfl⟩
  · rw [Finset.sum_image (by intro x _ y _ e; simpa using e),
      Finset.sum_image (by intro x _ y _ e; simpa using e)]
    simp
  · have hne : ((p, h), false) ≠ ((p', h), false) := by
      intro e; apply hpp; simpa using e
    rw [Finset.sum_pair hne, Finset.sum_pair hne]
    simp

lemma add_holds (a : V → Bool) (e e' : CPLine V) (h : CPLine.Holds a e)
    (h' : CPLine.Holds a e') : CPLine.Holds a (e.1 + e'.1, e.2 + e'.2) := by
  unfold CPLine.Holds at *
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  linarith

lemma add_slack (e e' : CPLine V) : slack (e.1 + e'.1, e.2 + e'.2) = slack e + slack e' := by
  unfold slack
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

lemma mul_holds (a : V → Bool) (e : CPLine V) (k : ℕ) (h : CPLine.Holds a e) :
    CPLine.Holds a ((k : ℤ) • e.1, (k : ℤ) * e.2) := by
  unfold CPLine.Holds at *
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (by positivity)

lemma mul_slack (e : CPLine V) (k : ℕ) :
    slack ((k : ℤ) • e.1, (k : ℤ) * e.2) = (k : ℤ) * slack e := by
  unfold slack
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma div_holds (a : V → Bool) (e : CPLine V) (d : ℕ) (hd : 0 < d)
    (hdiv : ∀ v, (d : ℤ) ∣ e.1 v) (h : CPLine.Holds a e) :
    CPLine.Holds a (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) := by
  unfold CPLine.Holds at *
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hsum : ∑ v, e.1 v * (if a v then 1 else 0)
      = (d : ℤ) * ∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← mul_assoc, Int.mul_ediv_cancel' (hdiv v)]
  simp only
  have h2 : (-(∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0))) * d ≤ -e.2 := by
    rw [hsum] at h
    linarith
  have h3 := (Int.le_ediv_iff_mul_le hd').mpr h2
  linarith

lemma div_slack (e : CPLine V) (d : ℕ) (hd : 0 < d) (hdiv : ∀ v, (d : ℤ) ∣ e.1 v)
    (hs : 0 ≤ slack e) : -5 < slack (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) := by
  unfold slack at *
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hsum : ∑ v, e.1 v = (d : ℤ) * ∑ v, e.1 v / (d : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Int.mul_ediv_cancel' (hdiv v)]
  have hq := Int.lt_ediv_add_one_mul_self (-e.2) hd'
  simp only
  rw [hsum] at hs
  set A := ∑ v, e.1 v / (d : ℤ)
  set r := (-e.2) / (d : ℤ)
  nlinarith

def Good (e : CPLine V) (t : Tr) : Prop :=
  (∀ c ∈ I0, c ∉ t.1 → CPLine.Holds (asg c) e) ∧ (t.2.2 = 0 → 0 ≤ slack e) ∧
    (t.2.2 ≤ 1 → -5 < slack e)

def cost (t : Tr) : ℕ := 2 * t.2.1 + 1 + t.2.2

lemma good_mono {e : CPLine V} {t t' : Tr} (h : Good e t) (hS : t.1 ⊆ t'.1)
    (hx : t.2.2 ≤ t'.2.2) : Good e t' :=
  ⟨fun c hc hn => h.1 c hc (fun m => hn (hS m)), fun h0 => h.2.1 (by omega),
    fun h1 => h.2.2 (by omega)⟩

lemma sum_erase (L : List Tr) (t : Tr) (h : t ∈ L) :
    cost t + ((L.erase t).map cost).sum = (L.map cost).sum := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    by_cases hat : a = t
    · subst hat
      simp
    · have ht : t ∈ L := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hat
        · exact h
      rw [List.erase_cons_tail (by simpa using hat)]
      simp only [List.map_cons, List.sum_cons]
      rw [← ih ht]
      ring

def Inv (π : List (CPLine V)) : Prop :=
  ∃ L : List Tr, (L.map cost).sum ≤ π.length ∧ (∀ t ∈ L, t.1.card ≤ t.2.1 + 1) ∧
    ∀ e ∈ π, ∃ t ∈ L, Good e t

lemma inv_fresh {π : List (CPLine V)} (hI : Inv π) (e : CPLine V) (S : Finset I)
    (hS : S.card ≤ 1) (he : Good e (S, 0, 0)) : Inv (e :: π) := by
  obtain ⟨L, hsum, hcard, hgood⟩ := hI
  refine ⟨(S, 0, 0) :: L, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.sum_cons, List.length_cons, cost]
    omega
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · simpa using hS
    · exact hcard t ht
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨_, List.mem_cons_self .., he⟩
    · obtain ⟨t, ht, hg⟩ := hgood e' he'
      exact ⟨t, List.mem_cons_of_mem _ ht, hg⟩

lemma inv_bump {π : List (CPLine V)} (L : List Tr) (hsum : (L.map cost).sum ≤ π.length)
    (hcard : ∀ t ∈ L, t.1.card ≤ t.2.1 + 1) (hgood : ∀ e ∈ π, ∃ t ∈ L, Good e t)
    (t : Tr) (ht : t ∈ L) (e : CPLine V) (he : Good e (t.1, t.2.1, t.2.2 + 1)) :
    Inv (e :: π) := by
  have hs := sum_erase L t ht
  refine ⟨(t.1, t.2.1, t.2.2 + 1) :: L.erase t, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.sum_cons, List.length_cons]
    simp only [cost] at hs ⊢
    omega
  · intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hcard t ht
    · exact hcard u (List.mem_of_mem_erase hu)
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨_, List.mem_cons_self .., he⟩
    · obtain ⟨u, hu, hg⟩ := hgood e' he'
      by_cases hut : u = t
      · subst hut
        exact ⟨_, List.mem_cons_self .., good_mono hg (subset_refl _) (by simp)⟩
      · exact ⟨u, List.mem_cons_of_mem _ ((List.mem_erase_of_ne hut).mpr hu), hg⟩

lemma inv_merge {π : List (CPLine V)} (L : List Tr) (hsum : (L.map cost).sum ≤ π.length)
    (hcard : ∀ t ∈ L, t.1.card ≤ t.2.1 + 1) (hgood : ∀ e ∈ π, ∃ t ∈ L, Good e t)
    (t t' : Tr) (ht : t ∈ L) (ht' : t' ∈ L) (hne : t ≠ t') (e : CPLine V)
    (he : Good e (t.1 ∪ t'.1, t.2.1 + t'.2.1 + 1, t.2.2 + t'.2.2)) :
    Inv (e :: π) := by
  have ht'' : t' ∈ L.erase t := (List.mem_erase_of_ne (Ne.symm hne)).mpr ht'
  have hs := sum_erase L t ht
  have hs' := sum_erase (L.erase t) t' ht''
  refine ⟨(t.1 ∪ t'.1, t.2.1 + t'.2.1 + 1, t.2.2 + t'.2.2) :: (L.erase t).erase t', ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.sum_cons, List.length_cons]
    simp only [cost] at hs hs' ⊢
    omega
  · intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · have h1 := hcard t ht
      have h2 := hcard t' ht'
      have := Finset.card_union_le t.1 t'.1
      simp only
      omega
    · exact hcard u (List.mem_of_mem_erase (List.mem_of_mem_erase hu))
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨_, List.mem_cons_self .., he⟩
    · obtain ⟨u, hu, hg⟩ := hgood e' he'
      by_cases hut : u = t
      · subst hut
        exact ⟨_, List.mem_cons_self .., good_mono hg Finset.subset_union_left (by simp)⟩
      · by_cases hut' : u = t'
        · subst hut'
          exact ⟨_, List.mem_cons_self .., good_mono hg Finset.subset_union_right (by simp)⟩
        · exact ⟨u, List.mem_cons_of_mem _ ((List.mem_erase_of_ne hut').mpr
            ((List.mem_erase_of_ne hut).mpr hu)), hg⟩

lemma inv_of_der (π : List (CPLine V)) (h : IsCPDerivation (PHP 6 5) π) : Inv π := by
  induction h with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | ax C _ hC ih =>
    refine inv_fresh ih _ (I0.filter (fun c => cl c = C)) ?_ ?_
    · rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact cl_inj a b ha.1 hb.1 (ha.2.trans hb.2.symm)
    · have hs := clause_slack C hC
      refine ⟨fun c hc hn => clause_holds _ _ (sat_of_ne c hc C hC ?_), fun _ => hs,
        fun _ => by linarith⟩
      intro e
      exact hn (Finset.mem_filter.mpr ⟨hc, e⟩)
  | boolLo v _ ih =>
    refine inv_fresh ih _ ∅ (by simp) ⟨fun c _ _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · unfold CPLine.Holds
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      split_ifs <;> simp
    · unfold slack; simp
    · unfold slack; simp
  | boolHi v _ ih =>
    refine inv_fresh ih _ ∅ (by simp) ⟨fun c _ _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · unfold CPLine.Holds
      simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      split_ifs <;> simp
    · unfold slack; simp
    · unfold slack; simp
  | @add π e e' _ he he' ih =>
    obtain ⟨L, hsum, hcard, hgood⟩ := ih
    obtain ⟨t, ht, hg⟩ := hgood e he
    obtain ⟨t', ht', hg'⟩ := hgood e' he'
    by_cases htt : t = t'
    · subst htt
      refine inv_bump L hsum hcard hgood t ht _ ⟨fun c hc hn => ?_, fun h0 => ?_, fun h1 => ?_⟩
      · exact add_holds _ _ _ (hg.1 c hc hn) (hg'.1 c hc hn)
      · simp at h0
      · have a1 := hg.2.1 (by simp at h1; omega)
        have a2 := hg'.2.1 (by simp at h1; omega)
        rw [add_slack]
        linarith
    · refine inv_merge L hsum hcard hgood t t' ht ht' htt _
        ⟨fun c hc hn => ?_, fun h0 => ?_, fun h1 => ?_⟩
      · simp only [Finset.mem_union, not_or] at hn
        exact add_holds _ _ _ (hg.1 c hc hn.1) (hg'.1 c hc hn.2)
      · simp only at h0
        have a1 := hg.2.1 (by omega)
        have a2 := hg'.2.1 (by omega)
        rw [add_slack]
        linarith
      · simp only at h1
        rw [add_slack]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h | h
        · have a1 := hg.2.1 (by omega)
          have a2 := hg'.2.1 (by omega)
          linarith
        · by_cases hx : t.2.2 = 0
          · have a1 := hg.2.1 hx
            have a2 := hg'.2.2 (by omega)
            linarith
          · have a1 := hg.2.2 (by omega)
            have a2 := hg'.2.1 (by omega)
            linarith
  | @mul π e k _ he ih =>
    obtain ⟨L, hsum, hcard, hgood⟩ := ih
    obtain ⟨t, ht, hg⟩ := hgood e he
    refine inv_bump L hsum hcard hgood t ht _ ⟨fun c hc hn => ?_, fun h0 => ?_, fun h1 => ?_⟩
    · exact mul_holds _ _ _ (hg.1 c hc hn)
    · simp at h0
    · have a1 := hg.2.1 (by simp at h1; omega)
      rw [mul_slack]
      have : (0 : ℤ) ≤ (k : ℤ) * slack e := mul_nonneg (by positivity) a1
      linarith
  | @div π e d _ he hd hdiv ih =>
    obtain ⟨L, hsum, hcard, hgood⟩ := ih
    obtain ⟨t, ht, hg⟩ := hgood e he
    refine inv_bump L hsum hcard hgood t ht _ ⟨fun c hc hn => ?_, fun h0 => ?_, fun h1 => ?_⟩
    · exact div_holds _ _ _ hd hdiv (hg.1 c hc hn)
    · simp at h0
    · exact div_slack e d hd hdiv (hg.2.1 (by simp at h1; omega))

lemma final (π : List (CPLine V)) (h : IsCPDerivation (PHP 6 5) π)
    (hmem : ((0 : V → ℤ), (1 : ℤ)) ∈ π) (hlen : π.length ≤ 162) : False := by
  obtain ⟨L, hsum, hcard, hgood⟩ := inv_of_der π h
  obtain ⟨t, ht, hg⟩ := hgood _ hmem
  have hsub : I0 ⊆ t.1 := by
    intro c hc
    by_contra hn
    have := hg.1 c hc hn
    simp [CPLine.Holds] at this
  have hc1 := Finset.card_le_card hsub
  rw [card_I0] at hc1
  have hc2 := hcard t ht
  have hx : ¬ t.2.2 ≤ 1 := by
    intro h1
    have := hg.2.2 h1
    simp [slack] at this
  have hle : cost t ≤ (L.map cost).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem ht)
  simp only [cost] at hle
  omega

end PEqualNP.Outside.L_meta_9702

theorem PEqualNP.Outside.L_meta_9702 : ¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (5 + 1) × Fin 5)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (5 + 1) 5) π ∧ π.length ≤ 162) := by
  rintro ⟨π, ⟨hder, hmem⟩, hlen⟩
  exact PEqualNP.Outside.L_meta_9702.final π hder hmem hlen
