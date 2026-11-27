import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkC1

/-!
# The owner link, clause (c), part 2: the tails number at most `2k + 1` per call

Conjecture until a seat's checker accepts a row. For every formula `ψ`, the tail lengths of
`OWN' E k ψ` sum to at most `(2k + 1)` times the number of calls `callsF E ψ`
(`ownC_tl_le`): each inner block has `k` triples with two neighbours each, and the vertex lists
own at most one end per call (the pair calls of a clause are owned by its hub lists, each
positive occurrence by the single variable list at the first occurrence of its variable).
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

/-- Sum of tail lengths of a list family. -/
def ownC_tl (L : List (List ℕ)) : ℕ := (L.map (fun l => l.tail.length)).sum

theorem ownC_tl_append (A B : List (List ℕ)) : ownC_tl (A ++ B) = ownC_tl A + ownC_tl B := by
  simp [ownC_tl]

theorem ownC_tl_flatMap {α : Type} (L : List α) (g : α → List (List ℕ)) :
    ownC_tl (L.flatMap g) = (L.map (fun x => ownC_tl (g x))).sum := by
  induction L with
  | nil => simp [ownC_tl]
  | cons a L ih => simp only [List.flatMap_cons, ownC_tl_append, ih, List.map_cons, List.sum_cons]

theorem ownC_lsum (g : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem ownC_flen (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    ((List.range n).filter (fun i => decide (p i))).length =
      ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem ownC_flen_gt (j n : ℕ) :
    ((List.range n).filter (fun l => decide (j < l))).length = n - (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : j < n <;> simp [h] <;> omega

theorem ownC_sum_const {α : Type} (L : List α) (c : ℕ) : (L.map (fun _ => c)).sum = c * L.length := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

theorem ownC_inner_len (E k u v : ℕ) (b : Bool) : (innerF E k u v b).length = k := by
  unfold innerF
  rw [List.length_map]
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1 + 1) % 2 = 0 := by omega
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.filter_append, List.filter_append, List.length_append, List.length_append, ih]
    cases b <;> simp [List.filter_cons, h1, h2]

theorem ownC_tl_inner (E k u v : ℕ) (b : Bool) : ownC_tl (innerF E k u v b) = 2 * k := by
  have : ownC_tl (innerF E k u v b) = ((innerF E k u v b).map (fun _ => 2)).sum := by
    unfold ownC_tl
    congr 1
    apply List.map_congr_left
    intro l hl
    rw [ownC_innerF_mem] at hl
    obtain ⟨s, -, -, rfl⟩ := hl
    rfl
  rw [this, ownC_sum_const, ownC_inner_len]

theorem ownC_tl_inners {α : Type} (E k : ℕ) (L : List α) (a b : α → ℕ) (c : α → Bool) :
    ownC_tl (L.flatMap (fun x => innerF E k (a x) (b x) (c x))) = 2 * k * L.length := by
  rw [ownC_tl_flatMap]
  simp only [ownC_tl_inner]
  rw [ownC_sum_const]

/-- The calls of item `(i, j)`. -/
def ownC_ci (E : ℕ) (ψ : CNF) (i j : ℕ) : List (ℕ × ℕ × Bool) :=
  (if j < wF ψ i then
      [(2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0), posF E ψ i j, (litF ψ i j).2)]
    else [(2 * E + 1, posF E ψ i j, true)]) ++
  ((List.range (wF ψ i + 1)).filter (fun l : ℕ => decide (j < l))).map
      (fun l : ℕ => (posF E ψ i j, posF E ψ i l, decide (j ≠ fF ψ i))) ++
  (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then
      [(2 * (litF ψ i j).1, 2 * (litF ψ i j).1 + 1, false)] else [])

theorem ownC_calls_eq (E : ℕ) (ψ : CNF) : callsF E ψ =
    (List.range ψ.length).flatMap (fun i => (List.range (wF ψ i + 1)).flatMap
      (fun j => ownC_ci E ψ i j)) ++ [(2 * E, 2 * E + 1, false), (2 * E, 3 * E + 2, false)] := rfl

theorem ownC_ci_len (E : ℕ) (ψ : CNF) (i j : ℕ) : (ownC_ci E ψ i j).length =
    1 + (wF ψ i - j) + (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then 1 else 0) := by
  unfold ownC_ci
  simp only [List.length_append, List.length_map, ownC_flen_gt]
  split_ifs <;> simp <;> omega

theorem ownC_hub_tl (E k : ℕ) (ψ : CNF) (i j : ℕ) : (hubL E k ψ i j).tail.length =
    (if j < wF ψ i ∧ (litF ψ i j).2 = false then 1 else 0) + (if fF ψ i < j then 1 else 0) +
      (wF ψ i - j) := by
  unfold hubL
  simp only [List.tail_cons, List.length_append, List.length_map, ownC_flen_gt]
  split_ifs <;> simp <;> omega

/-- The number of positive occurrences of variable `z`. -/
def ownC_pc (ψ : CNF) (z : ℕ) : ℕ :=
  ∑ i' ∈ Finset.range ψ.length, ∑ j' ∈ Finset.range (wF ψ i'),
    if (litF ψ i' j').1 = z ∧ (litF ψ i' j').2 = true then 1 else 0

theorem ownC_var_tl (E k : ℕ) (ψ : CNF) (i j : ℕ) :
    (varL E k ψ i j).tail.length = 1 + ownC_pc ψ (litF ψ i j).1 := by
  unfold varL ownC_pc
  simp only [List.tail_cons, List.length_cons, List.length_flatMap, List.length_map]
  rw [ownC_lsum]
  simp only [ownC_flen]
  omega

/-- The vertex-list tails of item `(i, j)`. -/
def ownC_vt (E k : ℕ) (ψ : CNF) (i j : ℕ) : ℕ :=
  (if j ≠ fF ψ i then (hubL E k ψ i j).tail.length else 0) +
    (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then (varL E k ψ i j).tail.length else 0)

theorem ownC_item_tl (E k : ℕ) (ψ : CNF) (i j : ℕ) :
    ownC_tl (itemF E k ψ i j) = 2 * k * (ownC_ci E ψ i j).length + ownC_vt E k ψ i j := by
  unfold itemF ownC_ci ownC_vt
  simp only [ownC_tl_append, List.length_append, List.length_map]
  rw [ownC_tl_inners E k _ (fun l => posF E ψ i j) (fun l => posF E ψ i l)
    (fun _ => decide (j ≠ fF ψ i))]
  have e1 : ownC_tl (if j < wF ψ i then
      innerF E k (2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0)) (posF E ψ i j)
        (litF ψ i j).2
    else innerF E k (2 * E + 1) (posF E ψ i j) true) = 2 * k := by
    split_ifs <;> exact ownC_tl_inner _ _ _ _ _
  have e2 : (if j < wF ψ i then
      [(2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0), posF E ψ i j, (litF ψ i j).2)]
    else [(2 * E + 1, posF E ψ i j, true)]).length = 1 := by
    split_ifs <;> rfl
  rw [e1, e2]
  by_cases hc : j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j
  · rw [if_pos hc, if_pos hc, if_pos hc, if_pos hc, ownC_tl_inner]
    by_cases hf : j ≠ fF ψ i
    · rw [if_pos hf, if_pos hf]; simp [ownC_tl]; ring
    · rw [if_neg hf, if_neg hf]; simp [ownC_tl]; ring
  · rw [if_neg hc, if_neg hc, if_neg hc, if_neg hc]
    by_cases hf : j ≠ fF ψ i
    · rw [if_pos hf, if_pos hf]; simp [ownC_tl]; ring
    · rw [if_neg hf, if_neg hf]; simp [ownC_tl]; ring

theorem ownC_own_tl (E k : ℕ) (ψ : CNF) : ownC_tl (OWN' E k ψ) =
    (∑ i ∈ Finset.range ψ.length, ∑ j ∈ Finset.range (wF ψ i + 1), ownC_tl (itemF E k ψ i j)) +
      2 * k + 2 * k + (1 + ψ.length) + 1 := by
  unfold OWN'
  simp only [ownC_tl_append, ownC_tl_flatMap, ownC_lsum, ownC_tl_inner]
  simp [ownC_tl]
  omega

theorem ownC_calls_len (E : ℕ) (ψ : CNF) : (callsF E ψ).length =
    (∑ i ∈ Finset.range ψ.length, ∑ j ∈ Finset.range (wF ψ i + 1), (ownC_ci E ψ i j).length) + 2 := by
  rw [ownC_calls_eq]
  simp only [List.length_append, List.length_flatMap, ownC_lsum]
  simp

theorem ownC_sum_gt (f n : ℕ) :
    (∑ j ∈ Finset.range n, if f < j then 1 else 0) = n - (f + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; split_ifs <;> omega

/-- One clause: hub tails plus the closing entry plus the positive literals give the clause's
item and pair calls. -/
theorem ownC_clause (E k : ℕ) (ψ : CNF) (i : ℕ) :
    (∑ j ∈ Finset.range (wF ψ i + 1),
        if j ≠ fF ψ i then (hubL E k ψ i j).tail.length else 0) + 1 +
      (∑ j ∈ Finset.range (wF ψ i), if (litF ψ i j).2 = true then 1 else 0) =
      ∑ j ∈ Finset.range (wF ψ i + 1), (1 + (wF ψ i - j)) := by
  set W := wF ψ i with hW
  set F := fF ψ i with hF
  have hFW : F ≤ W := ownC_f_le ψ i
  have hpt : ∀ j, (if j ≠ F then (hubL E k ψ i j).tail.length else 0) =
      (if j < W ∧ (litF ψ i j).2 = false then 1 else 0) + (if F < j then 1 else 0) +
        (if j ≠ F then W - j else 0) := by
    intro j
    rw [ownC_hub_tl]
    by_cases hj : j = F
    · subst hj
      have : ¬ (F < W ∧ (litF ψ i F).2 = false) := by
        rintro ⟨h1, h2⟩
        rw [ownC_f_pos ψ i h1] at h2
        exact Bool.noConfusion h2
      simp [this]
    · rw [if_pos hj, if_pos hj]
  simp only [hpt, Finset.sum_add_distrib]
  have hs1 : (∑ j ∈ Finset.range (W + 1), if j ≠ F then W - j else 0) + (W - F) =
      ∑ j ∈ Finset.range (W + 1), (W - j) := by
    have : (∑ j ∈ Finset.range (W + 1), if j = F then W - j else 0) = W - F := by
      rw [Finset.sum_ite_eq']
      simp; omega
    rw [← this, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = F <;> simp [hj]
  have hs2 := ownC_sum_gt F (W + 1)
  have hs3 : (∑ j ∈ Finset.range (W + 1), if j < W ∧ (litF ψ i j).2 = false then 1 else 0) +
      (∑ j ∈ Finset.range W, if (litF ψ i j).2 = true then 1 else 0) = W := by
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, false_and, if_false, Nat.add_zero]
    rw [← Finset.sum_add_distrib]
    have : ∀ j ∈ Finset.range W, ((if j < W ∧ (litF ψ i j).2 = false then 1 else 0) +
        (if (litF ψ i j).2 = true then 1 else 0)) = 1 := by
      intro j hj
      rw [Finset.mem_range] at hj
      cases (litF ψ i j).2 <;> simp [hj]
    rw [Finset.sum_congr rfl this]
    simp
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

/-- Strict growth of the offsets across clauses. -/
theorem ownC_off_succ (ψ : CNF) (i : ℕ) (hi : i < ψ.length) :
    offF ψ (i + 1) = offF ψ i + wF ψ i + 1 := by
  unfold offF wF
  rw [List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem _ _ hi]
  simp
  omega

theorem ownC_off_mono (ψ : CNF) (i : ℕ) : offF ψ i ≤ offF ψ (i + 1) := by
  unfold offF
  rw [List.take_succ, List.map_append, List.sum_append]
  omega

theorem ownC_off_lt (ψ : CNF) {i i' : ℕ} (hi : i < ψ.length) (h : i < i') :
    offF ψ i + wF ψ i + 1 ≤ offF ψ i' := by
  induction i' with
  | zero => omega
  | succ m ih =>
    by_cases hm : i = m
    · subst hm; rw [ownC_off_succ ψ i hi]
    · have := ih (by omega); have := ownC_off_mono ψ m; omega

theorem ownC_off_inj (ψ : CNF) {i j i' j' : ℕ} (hi : i < ψ.length) (hi' : i' < ψ.length)
    (hj : j < wF ψ i) (hj' : j' < wF ψ i') (h : offF ψ i + j = offF ψ i' + j') :
    i = i' ∧ j = j' := by
  rcases lt_trichotomy i i' with hlt | rfl | hlt
  · have := ownC_off_lt ψ hi hlt; omega
  · omega
  · have := ownC_off_lt ψ hi' hlt; omega

/-- Each positive occurrence is counted by at most one variable list. -/
theorem ownC_cross (ψ : CNF) :
    (∑ i ∈ Finset.range ψ.length, ∑ j ∈ Finset.range (wF ψ i + 1),
        if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then ownC_pc ψ (litF ψ i j).1 else 0) ≤
      ∑ i ∈ Finset.range ψ.length, ∑ j ∈ Finset.range (wF ψ i),
        if (litF ψ i j).2 = true then 1 else 0 := by
  unfold ownC_pc
  rw [Finset.sum_sigma', Finset.sum_sigma']
  have h1 : ∀ a ∈ (Finset.range ψ.length).sigma (fun i => Finset.range (wF ψ i + 1)),
      (if a.2 < wF ψ a.1 ∧ (litF ψ a.1 a.2).1 = offF ψ a.1 + a.2 then
        ∑ i' ∈ Finset.range ψ.length, ∑ j' ∈ Finset.range (wF ψ i'),
          (if (litF ψ i' j').1 = (litF ψ a.1 a.2).1 ∧ (litF ψ i' j').2 = true then 1 else 0)
        else 0) =
      ∑ b ∈ (Finset.range ψ.length).sigma (fun i => Finset.range (wF ψ i)),
        if (a.2 < wF ψ a.1 ∧ (litF ψ a.1 a.2).1 = offF ψ a.1 + a.2) ∧
          ((litF ψ b.1 b.2).1 = (litF ψ a.1 a.2).1 ∧ (litF ψ b.1 b.2).2 = true) then 1 else 0 := by
    intro a _
    rw [Finset.sum_sigma']
    split_ifs with hc
    · apply Finset.sum_congr rfl; intro b _; simp [hc]
    · simp [hc]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  simp only [Finset.mem_sigma, Finset.mem_range] at hb
  by_cases hp : (litF ψ b.1 b.2).2 = true
  · rw [if_pos hp, Finset.sum_boole]
    simp only [hp, and_true, Nat.cast_id]
    apply Finset.card_le_one.mpr
    intro a ha a' ha'
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range] at ha ha'
    obtain ⟨⟨hai, -⟩, ⟨haj, haz⟩, hab⟩ := ha
    obtain ⟨⟨hai', -⟩, ⟨haj', haz'⟩, hab'⟩ := ha'
    obtain ⟨e1, e2⟩ := ownC_off_inj ψ hai hai' haj haj' (by omega)
    cases a; cases a'
    simp only at e1 e2
    subst e1; subst e2; rfl
  · rw [if_neg hp]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro a _
    simp [hp]

/-- The count: tails of `OWN'` are at most `2k + 1` per call. -/
theorem ownC_tl_le (E k : ℕ) (ψ : CNF) :
    ownC_tl (OWN' E k ψ) ≤ (2 * k + 1) * (callsF E ψ).length := by
  rw [ownC_own_tl, ownC_calls_len]
  simp only [ownC_item_tl, Finset.sum_add_distrib, ← Finset.mul_sum]
  set C := ∑ i ∈ Finset.range ψ.length, ∑ j ∈ Finset.range (wF ψ i + 1), (ownC_ci E ψ i j).length
  suffices hv : (∑ i ∈ Finset.range ψ.length, ∑ j ∈ Finset.range (wF ψ i + 1), ownC_vt E k ψ i j)
      + ψ.length ≤ C by
    have : (2 * k + 1) * (C + 2) = 2 * k * C + C + 4 * k + 2 := by ring
    omega
  have hvt : ∀ i j, ownC_vt E k ψ i j =
      (if j ≠ fF ψ i then (hubL E k ψ i j).tail.length else 0) +
      (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then 1 else 0) +
      (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then ownC_pc ψ (litF ψ i j).1 else 0) := by
    intro i j
    unfold ownC_vt
    rw [ownC_var_tl]
    split_ifs <;> omega
  have hci : ∀ i j, (ownC_ci E ψ i j).length = (1 + (wF ψ i - j)) +
      (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then 1 else 0) := by
    intro i j; rw [ownC_ci_len]
  simp only [C, hvt, hci, Finset.sum_add_distrib]
  have hcl : ∀ i, (∑ j ∈ Finset.range (wF ψ i + 1),
        if j ≠ fF ψ i then (hubL E k ψ i j).tail.length else 0) + 1 +
      (∑ j ∈ Finset.range (wF ψ i), if (litF ψ i j).2 = true then 1 else 0) =
      ∑ j ∈ Finset.range (wF ψ i + 1), (1 + (wF ψ i - j)) := ownC_clause E k ψ
  have hcl' := Finset.sum_congr (s₁ := Finset.range ψ.length) rfl (fun i _ => hcl i)
  simp only [Finset.sum_add_distrib] at hcl'
  have hx := ownC_cross ψ
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hcl' ⊢
  omega

end PEqualNP.MetaComplexity.Helpers.OwnerLink
