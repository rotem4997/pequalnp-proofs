import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9666

open PEqualNP.Search PEqualNP.ProofComplexity

-- Lower bound 45 for cutting planes refutations of PHP 4 3 (lines counted as in IsCPRefutation).
-- Each line e gets S e: the indices of 22 fixed 0/1 points (each falsifies exactly one clause of
-- PHP 4 3) where e fails, and Phi e = 3 * (value of e at the all 1/3 point minus its constant).
-- Lines are covered by blocks (X, l): S e is inside X and Phi e meets level l
-- (l = 0: Phi >= 0, l = 1: Phi >= -2, l >= 2: free). A block costs 2 |X| + l - 1, and the
-- costs of the blocks never exceed the number of lines. Divisions keep Phi >= -2, so the line
-- 0 >= 1 (Phi = -3, all 22 points fail) needs a block of cost 2 * 22 + 2 - 1 = 45.

abbrev V : Type := Fin (3 + 1) × Fin 3

def posL : List (List (Option (Fin 3))) :=
  [[none, some 0, some 1, some 2],
    [some 0, none, some 1, some 2],
    [some 0, some 1, none, some 2],
    [some 0, some 1, some 2, none],
    [some 0, some 0, some 1, some 2],
    [some 0, some 1, some 0, some 2],
    [some 0, some 1, some 2, some 0],
    [some 1, some 0, some 0, some 2],
    [some 1, some 0, some 2, some 0],
    [some 1, some 2, some 0, some 0],
    [some 1, some 1, some 0, some 2],
    [some 1, some 0, some 1, some 2],
    [some 1, some 0, some 2, some 1],
    [some 0, some 1, some 1, some 2],
    [some 0, some 1, some 2, some 1],
    [some 0, some 2, some 1, some 1],
    [some 2, some 2, some 0, some 1],
    [some 2, some 0, some 2, some 1],
    [some 2, some 0, some 1, some 2],
    [some 0, some 2, some 2, some 1],
    [some 0, some 2, some 1, some 2],
    [some 0, some 1, some 2, some 2]]

def W (k : Fin 22) (v : V) : Bool :=
  decide ((posL.getD k.val []).getD v.1.val none = some v.2)

def ev (a : V → Bool) (e : CPLine V) : ℤ := ∑ v, e.1 v * (if a v then 1 else 0)

def S (e : CPLine V) : Finset (Fin 22) := Finset.univ.filter (fun k => ev (W k) e < e.2)

def Phi (e : CPLine V) : ℤ := (∑ v, e.1 v) - 3 * e.2

def ok (l : ℕ) (x : ℤ) : Prop := (l = 0 ∧ 0 ≤ x) ∨ (l = 1 ∧ -2 ≤ x) ∨ 2 ≤ l

def cost (b : Finset (Fin 22) × ℕ) : ℕ := 2 * b.1.card + b.2 - 1

def Cov (B : Finset (Finset (Fin 22) × ℕ)) (e : CPLine V) : Prop :=
  ∃ b ∈ B, S e ⊆ b.1 ∧ ok b.2 (Phi e)

def Inv (π : List (CPLine V)) : Prop :=
  ∃ B : Finset (Finset (Fin 22) × ℕ), (∀ e ∈ π, Cov B e) ∧ ∑ b ∈ B, cost b ≤ π.length

theorem ok_mono {l l' : ℕ} {x : ℤ} (h : ok l x) (hl : l ≤ l') : ok l' x := by
  unfold ok at *; omega

theorem sum_insert_le (t : Finset (Finset (Fin 22) × ℕ)) (m : Finset (Fin 22) × ℕ) :
    ∑ b ∈ insert m t, cost b ≤ cost m + ∑ b ∈ t, cost b := by
  by_cases hm : m ∈ t
  · rw [Finset.insert_eq_of_mem hm]; omega
  · rw [Finset.sum_insert hm]

theorem stepNew {π : List (CPLine V)} (h : Inv π) (m : Finset (Fin 22) × ℕ) (e' : CPLine V)
    (hc : cost m ≤ 1) (hS : S e' ⊆ m.1) (hok : ok m.2 (Phi e')) : Inv (e' :: π) := by
  obtain ⟨B, hcov, hsum⟩ := h
  refine ⟨insert m B, ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨m, Finset.mem_insert_self _ _, hS, hok⟩
    · obtain ⟨b, hb, h1, h2⟩ := hcov e he
      exact ⟨b, Finset.mem_insert_of_mem hb, h1, h2⟩
  · have := sum_insert_le B m
    simp only [List.length_cons]
    omega

theorem stepOne {π : List (CPLine V)} (h : ∃ B : Finset (Finset (Fin 22) × ℕ),
      (∀ e ∈ π, Cov B e) ∧ ∑ b ∈ B, cost b ≤ π.length)
    (B : Finset (Finset (Fin 22) × ℕ)) (hcov : ∀ e ∈ π, Cov B e)
    (hsum : ∑ b ∈ B, cost b ≤ π.length) (b : Finset (Fin 22) × ℕ) (hb : b ∈ B)
    (m : Finset (Fin 22) × ℕ) (e' : CPLine V)
    (hX : b.1 ⊆ m.1) (hl : b.2 ≤ m.2) (hc : cost m ≤ cost b + 1)
    (hS : S e' ⊆ m.1) (hok : ok m.2 (Phi e')) : Inv (e' :: π) := by
  clear h
  refine ⟨insert m (B.erase b), ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨m, Finset.mem_insert_self _ _, hS, hok⟩
    · obtain ⟨c, hcB, h1, h2⟩ := hcov e he
      by_cases hcb : c = b
      · subst hcb
        exact ⟨m, Finset.mem_insert_self _ _, h1.trans hX, ok_mono h2 hl⟩
      · exact ⟨c, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hcb, hcB⟩), h1, h2⟩
  · have h1 := sum_insert_le (B.erase b) m
    have h2 := Finset.add_sum_erase B cost hb
    simp only [List.length_cons]
    omega

theorem stepTwo (π : List (CPLine V))
    (B : Finset (Finset (Fin 22) × ℕ)) (hcov : ∀ e ∈ π, Cov B e)
    (hsum : ∑ b ∈ B, cost b ≤ π.length) (b1 b2 : Finset (Fin 22) × ℕ) (hb1 : b1 ∈ B)
    (hb2 : b2 ∈ B) (hne : b1 ≠ b2)
    (m : Finset (Fin 22) × ℕ) (e' : CPLine V)
    (hX1 : b1.1 ⊆ m.1) (hX2 : b2.1 ⊆ m.1) (hl1 : b1.2 ≤ m.2) (hl2 : b2.2 ≤ m.2)
    (hc : cost m ≤ cost b1 + cost b2 + 1)
    (hS : S e' ⊆ m.1) (hok : ok m.2 (Phi e')) : Inv (e' :: π) := by
  refine ⟨insert m ((B.erase b1).erase b2), ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨m, Finset.mem_insert_self _ _, hS, hok⟩
    · obtain ⟨c, hcB, h1, h2⟩ := hcov e he
      by_cases hc1 : c = b1
      · subst hc1
        exact ⟨m, Finset.mem_insert_self _ _, h1.trans hX1, ok_mono h2 hl1⟩
      by_cases hc2 : c = b2
      · subst hc2
        exact ⟨m, Finset.mem_insert_self _ _, h1.trans hX2, ok_mono h2 hl2⟩
      exact ⟨c, Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hc2, Finset.mem_erase.mpr ⟨hc1, hcB⟩⟩), h1, h2⟩
  · have hb2' : b2 ∈ B.erase b1 := Finset.mem_erase.mpr ⟨Ne.symm hne, hb2⟩
    have h1 := sum_insert_le ((B.erase b1).erase b2) m
    have h2 := Finset.add_sum_erase B cost hb1
    have h3 := Finset.add_sum_erase (B.erase b1) cost hb2'
    simp only [List.length_cons]
    omega

-- Copied from lean/PEqualNP/Search/Helpers/CP/TriDag.lean (clauseCP_holds_iff), merged library.
theorem clauseCP_holds_iff (a : V → Bool) (C : Clause V) :
    CPLine.Holds a (clauseCP C) ↔ ClauseSat a C := by
  have hsum : (∑ v, (∑ l ∈ C, if l.1 = v then (if l.2 then (1 : ℤ) else -1) else 0)
        * (if a v then 1 else 0))
      = ∑ l ∈ C, (if l.2 then (1 : ℤ) else -1) * (if a l.1 then 1 else 0) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l.1]
    · simp
    · intro v _ hv
      simp [Ne.symm hv]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hind : (∑ l ∈ C, (if l.2 then (1 : ℤ) else -1) * (if a l.1 then 1 else 0))
      + (∑ l ∈ C, if l.2 then (0 : ℤ) else 1) = ∑ l ∈ C, if a l.1 = l.2 then (1 : ℤ) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases l with ⟨v, b⟩
    cases b <;> cases a v <;> simp
  have key : CPLine.Holds a (clauseCP C)
      ↔ (1 : ℤ) ≤ ∑ l ∈ C, if a l.1 = l.2 then (1 : ℤ) else 0 := by
    unfold CPLine.Holds clauseCP
    dsimp only
    rw [hsum, ← hind]
    constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · intro h
    by_contra hne
    have h0 : (∑ l ∈ C, if a l.1 = l.2 then (1 : ℤ) else 0) = 0 :=
      Finset.sum_eq_zero fun l hl => by
        have hal : ¬ a l.1 = l.2 := fun hal => hne ⟨l, hl, hal⟩
        simp [hal]
    omega
  · rintro ⟨l, hl, hal⟩
    calc (1 : ℤ) = if a l.1 = l.2 then (1 : ℤ) else 0 := by simp [hal]
      _ ≤ _ := Finset.single_le_sum (f := fun l : Literal V => if a l.1 = l.2 then (1 : ℤ) else 0)
        (fun i _ => by split_ifs <;> norm_num) hl

theorem S_clause (C : Clause V) :
    S (clauseCP C) = Finset.univ.filter (fun k => ¬ ∃ l ∈ C, W k l.1 = l.2) := by
  ext k
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have h := clauseCP_holds_iff (W k) C
  unfold CPLine.Holds ClauseSat at h
  unfold ev
  rw [← h]
  exact ⟨fun h1 h2 => by omega, fun h1 => by omega⟩

theorem Phi_clause (C : Clause V) :
    Phi (clauseCP C) = (∑ l ∈ C, if l.2 then (1 : ℤ) else -1) - 3 * (1 - ∑ l ∈ C, if l.2 then 0 else 1) := by
  unfold Phi clauseCP
  dsimp only
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l.1]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ax_facts (C : Clause V) (hC : C ∈ PHP (3 + 1) 3) :
    (S (clauseCP C)).card ≤ 1 ∧ 0 ≤ Phi (clauseCP C) := by
  rw [S_clause, Phi_clause]
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hii, rfl⟩
  · revert i
    decide
  · revert i i' j
    decide

theorem ev_add (a : V → Bool) (e e' : CPLine V) :
    ev a (e.1 + e'.1, e.2 + e'.2) = ev a e + ev a e' := by
  unfold ev
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.add_apply]
  ring

theorem Phi_add (e e' : CPLine V) : Phi (e.1 + e'.1, e.2 + e'.2) = Phi e + Phi e' := by
  unfold Phi
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem S_add (e e' : CPLine V) : S (e.1 + e'.1, e.2 + e'.2) ⊆ S e ∪ S e' := by
  intro k hk
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hk ⊢
  rw [ev_add] at hk
  by_contra h
  push_neg at h
  omega

theorem ev_mul (a : V → Bool) (e : CPLine V) (k : ℕ) :
    ev a ((k : ℤ) • e.1, (k : ℤ) * e.2) = (k : ℤ) * ev a e := by
  unfold ev
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem S_mul (e : CPLine V) (k : ℕ) : S ((k : ℤ) • e.1, (k : ℤ) * e.2) ⊆ S e := by
  intro i hi
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [ev_mul] at hi
  by_contra h
  push_neg at h
  have : (k : ℤ) * e.2 ≤ (k : ℤ) * ev (W i) e :=
    mul_le_mul_of_nonneg_left h (Int.natCast_nonneg k)
  omega

theorem Phi_mul (e : CPLine V) (k : ℕ) :
    Phi ((k : ℤ) • e.1, (k : ℤ) * e.2) = (k : ℤ) * Phi e := by
  unfold Phi
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem div_facts (e : CPLine V) (d : ℕ) (hd : 0 < d) (hdv : ∀ v, (d : ℤ) ∣ e.1 v) :
    S (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) ⊆ S e ∧
    (-2 ≤ Phi e → -2 ≤ Phi (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ)))) := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hq : ∀ v, e.1 v / (d : ℤ) * d = e.1 v := fun v => Int.ediv_mul_cancel (hdv v)
  have hr := Int.mul_ediv_add_emod (-e.2) (d : ℤ)
  have hr0 := Int.emod_nonneg (-e.2) (ne_of_gt hd')
  have hr1 := Int.emod_lt_of_pos (-e.2) hd'
  set c' := -((-e.2) / (d : ℤ)) with hc'
  set r := (-e.2) % (d : ℤ)
  have hdc : (d : ℤ) * c' = e.2 + r := by rw [hc']; linarith
  have hev : ∀ a, (d : ℤ) * ev a (fun v => e.1 v / (d : ℤ), c') = ev a e := by
    intro a
    unfold ev
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    dsimp only
    rw [← mul_assoc, mul_comm (d : ℤ) (e.1 v / (d : ℤ)), hq v]
  have hsumq : (d : ℤ) * (∑ v, e.1 v / (d : ℤ)) = ∑ v, e.1 v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_comm]; exact hq v
  constructor
  · intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    have h1 := hev (W k)
    by_contra h
    push_neg at h
    have h2 : (d : ℤ) * (ev (W k) (fun v => e.1 v / (d : ℤ), c') + 1) ≤ (d : ℤ) * c' :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hd')
    nlinarith
  · intro hP
    unfold Phi at hP ⊢
    dsimp only
    by_contra h
    push_neg at h
    have h2 : (d : ℤ) * ((∑ v, e.1 v / (d : ℤ)) - 3 * c') ≤ (d : ℤ) * (-3) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hd')
    nlinarith

theorem S_bool (e : CPLine V) (h : ∀ a, e.2 ≤ ev a e) : S e = ∅ := by
  ext k
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_lt]
  exact h _

theorem inv_of_der {π : List (CPLine V)} (h : IsCPDerivation (PHP (3 + 1) 3) π) : Inv π := by
  induction h with
  | nil => exact ⟨∅, by simp, by simp⟩
  | ax C ih hC hinv =>
    obtain ⟨h1, h2⟩ := ax_facts C hC
    refine stepNew hinv (S (clauseCP C), 0) _ ?_ (subset_refl _) ?_
    · unfold cost; dsimp only; omega
    · unfold ok; left; exact ⟨rfl, h2⟩
  | boolLo v ih hinv =>
    refine stepNew hinv (∅, 0) _ (by unfold cost; simp) ?_ ?_
    · rw [S_bool]
      intro a
      unfold ev
      dsimp only
      apply Finset.sum_nonneg
      intro u _
      split_ifs <;> norm_num
    · unfold ok Phi
      left
      refine ⟨rfl, ?_⟩
      dsimp only
      rw [Finset.sum_ite_eq']
      simp
  | boolHi v ih hinv =>
    refine stepNew hinv (∅, 0) _ (by unfold cost; simp) ?_ ?_
    · rw [S_bool]
      intro a
      unfold ev
      dsimp only
      rw [Finset.sum_eq_single v]
      · split_ifs <;> norm_num
      · intro u _ hu
        simp [hu]
      · intro h; exact absurd (Finset.mem_univ _) h
    · unfold ok Phi
      left
      refine ⟨rfl, ?_⟩
      dsimp only
      rw [Finset.sum_ite_eq']
      simp
  | @add π0 e e' ih he he' hinv =>
    obtain ⟨B, hcov, hsum⟩ := hinv
    obtain ⟨b1, hb1, hS1, hok1⟩ := hcov e he
    obtain ⟨b2, hb2, hS2, hok2⟩ := hcov e' he'
    by_cases hb : b1 = b2
    · subst hb
      refine stepOne ⟨B, hcov, hsum⟩ B hcov hsum b1 hb1
        (b1.1, if b1.2 = 0 then 0 else b1.2 + 1) _ (subset_refl _) ?_ ?_ ?_ ?_
      · dsimp only; split_ifs <;> omega
      · unfold cost; dsimp only; split_ifs <;> omega
      · exact (S_add e e').trans (Finset.union_subset hS1 hS2)
      · rw [Phi_add]
        unfold ok at hok1 hok2 ⊢
        dsimp only
        split_ifs <;> omega
    · refine stepTwo π0 B hcov hsum b1 b2 hb1 hb2 hb
        (b1.1 ∪ b2.1, b1.2 + b2.2) _ Finset.subset_union_left Finset.subset_union_right
        (by dsimp only; omega) (by dsimp only; omega) ?_ ?_ ?_
      · unfold cost
        dsimp only
        have := Finset.card_union_le b1.1 b2.1
        omega
      · exact (S_add e e').trans (Finset.union_subset_union hS1 hS2)
      · rw [Phi_add]
        unfold ok at hok1 hok2 ⊢
        dsimp only
        omega
  | @mul π0 e k ih he hinv =>
    obtain ⟨B, hcov, hsum⟩ := hinv
    obtain ⟨b, hb, hS, hok⟩ := hcov e he
    refine stepOne ⟨B, hcov, hsum⟩ B hcov hsum b hb
      (b.1, if b.2 = 0 then 0 else b.2 + 1) _ (subset_refl _) ?_ ?_ ?_ ?_
    · dsimp only; split_ifs <;> omega
    · unfold cost; dsimp only; split_ifs <;> omega
    · exact (S_mul e k).trans hS
    · rw [Phi_mul]
      unfold ok at hok ⊢
      dsimp only
      by_cases h0 : b.2 = 0
      · rw [if_pos h0]
        left
        refine ⟨rfl, ?_⟩
        have : 0 ≤ Phi e := by omega
        exact mul_nonneg (Int.natCast_nonneg k) this
      · rw [if_neg h0]
        right; right; omega
  | @div π0 e d ih he hd hdv hinv =>
    obtain ⟨B, hcov, hsum⟩ := hinv
    obtain ⟨b, hb, hS, hok⟩ := hcov e he
    obtain ⟨hdS, hdP⟩ := div_facts e d hd hdv
    refine stepOne ⟨B, hcov, hsum⟩ B hcov hsum b hb
      (b.1, if b.2 = 0 then 1 else b.2) _ (subset_refl _) ?_ ?_ (hdS.trans hS) ?_
    · dsimp only; split_ifs <;> omega
    · unfold cost; dsimp only; split_ifs <;> omega
    · unfold ok at hok ⊢
      dsimp only
      by_cases h0 : b.2 = 0
      · rw [if_pos h0]
        right; left
        exact ⟨rfl, hdP (by omega)⟩
      · rw [if_neg h0]
        rcases hok with h | h | h
        · omega
        · right; left; exact ⟨h.1, hdP h.2⟩
        · right; right; exact h

theorem length_ge {π : List (CPLine V)} (h : IsCPRefutation (PHP (3 + 1) 3) π) :
    45 ≤ π.length := by
  obtain ⟨B, hcov, hsum⟩ := inv_of_der h.1
  obtain ⟨b, hb, hS, hok⟩ := hcov _ h.2
  have hSu : S ((0 : V → ℤ), (1 : ℤ)) = Finset.univ := by
    ext k
    simp [S, ev]
  rw [hSu] at hS
  have hcard : b.1.card = 22 := by
    have := Finset.card_le_card hS
    have h2 := Finset.card_le_univ b.1
    simp only [Finset.card_univ, Fintype.card_fin] at this h2
    omega
  have hP : Phi ((0 : V → ℤ), (1 : ℤ)) = -3 := by simp [Phi]
  rw [hP] at hok
  have hl : 2 ≤ b.2 := by unfold ok at hok; omega
  have hcb : cost b ≤ ∑ c ∈ B, cost c :=
    Finset.single_le_sum (f := cost) (fun _ _ => Nat.zero_le _) hb
  have hcost : cost b = 2 * b.1.card + b.2 - 1 := rfl
  omega

end PEqualNP.Outside.L_meta_9666

theorem PEqualNP.Outside.L_meta_9666 : ¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (3 + 1) × Fin 3)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (3 + 1) 3) π ∧ π.length ≤ 44) := by
  rintro ⟨π, hπ, hlen⟩
  have := PEqualNP.Outside.L_meta_9666.length_ge hπ
  omega
