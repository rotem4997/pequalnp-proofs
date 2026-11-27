import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkA

/-!
# The owner link, clause (c), part 1: owned pairs are the thread edges of the calls

Conjecture until a seat's checker accepts a row. For any formula `ψ` whose variables have first
occurrences at their own position (`ownC_First`, proved for `REN φ` by `ownC_first_ren`), a pair
is owned by a list of `OWN' E k ψ` (in either order) exactly when it is a thread edge of some
call of `callsF E ψ` (`ownC_c1_vals`). Assembled with `PlacedEdges` in `OwnerLinkC.lean`.
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

/-! ## Threads -/

/-- The thread relation of `S` on values: `x` is thread vertex `i` of the slot `(u, v)` and
`y` its successor on the thread (or `u` when `i = 0`). -/
def ownC_TR (E k u v x y : ℕ) : Prop :=
  ∃ i, i < 2 * k ∧ x = 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + i ∧
    ((i = 0 ∧ y = u) ∨ (i + 1 < 2 * k ∧ y = 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + i + 1) ∨
      (i + 1 = 2 * k ∧ y = v))

theorem ownC_Xf_eq (E k u v t : ℕ) (ht : 1 ≤ t) :
    Xf E k u v t = 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + (t - 1) := by
  unfold Xf; omega

/-- Owned pairs of a list family. -/
def ownC_Own (L : List (List ℕ)) (x y : ℕ) : Prop :=
  ∃ l ∈ L, l.headD 0 = x ∧ y ∈ l.tail

theorem ownC_innerF_mem {E k u v : ℕ} {b : Bool} {l : List ℕ} :
    l ∈ innerF E k u v b ↔ ∃ s, s < 2 * k ∧ ((s + 1) % 2 = 0 ↔ b = true) ∧
      l = [Xf E k u v (s + 1), if s = 0 then u else Xf E k u v s,
        if s + 1 = 2 * k then v else Xf E k u v (s + 2)] := by
  unfold innerF
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨s, ⟨hs, hp⟩, rfl⟩; exact ⟨s, hs, hp, rfl⟩
  · rintro ⟨s, hs, hp, rfl⟩; exact ⟨s, ⟨hs, hp⟩, rfl⟩

/-- An owned pair of an inner triple is a thread edge of its slot. -/
theorem ownC_inner_tr {E k u v : ℕ} {b : Bool} {l : List ℕ} (hl : l ∈ innerF E k u v b)
    {x y : ℕ} (hx : l.headD 0 = x) (hy : y ∈ l.tail) :
    ownC_TR E k u v x y ∨ ownC_TR E k u v y x := by
  rw [ownC_innerF_mem] at hl
  obtain ⟨s, hs, -, rfl⟩ := hl
  simp only [List.headD_cons, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  subst hx
  rcases hy with rfl | rfl
  · split_ifs with h0
    · left; exact ⟨s, hs, by unfold Xf; omega, Or.inl ⟨h0, rfl⟩⟩
    · right; exact ⟨s - 1, by omega, by unfold Xf; omega, Or.inr (Or.inl ⟨by omega, by unfold Xf; omega⟩)⟩
  · split_ifs with h0
    · left; exact ⟨s, hs, by unfold Xf; omega, Or.inr (Or.inr ⟨h0, rfl⟩)⟩
    · left; exact ⟨s, hs, by unfold Xf; omega, Or.inr (Or.inl ⟨by omega, by unfold Xf; omega⟩)⟩

/-- Every thread edge of a slot whose inner block is present is owned, except the end edge
not covered by the flag: the `u` end when the flag is true, the `v` end when it is false. -/
theorem ownC_tr_own {E k u v : ℕ} {b : Bool} (hk : 1 ≤ k) {L : List (List ℕ)}
    (hin : ∀ l ∈ innerF E k u v b, l ∈ L)
    (hend : if b then ownC_Own L u (Xf E k u v 1) else ownC_Own L v (Xf E k u v (2 * k)))
    {x y : ℕ} (h : ownC_TR E k u v x y) : ownC_Own L x y ∨ ownC_Own L y x := by
  obtain ⟨i, hi, rfl, hy⟩ := h
  have mk : ∀ s, s < 2 * k → ((s + 1) % 2 = 0 ↔ b = true) →
      [Xf E k u v (s + 1), if s = 0 then u else Xf E k u v s,
        if s + 1 = 2 * k then v else Xf E k u v (s + 2)] ∈ L :=
    fun s hs hp => hin _ (ownC_innerF_mem.mpr ⟨s, hs, hp, rfl⟩)
  rcases hy with ⟨rfl, rfl⟩ | ⟨hi1, rfl⟩ | ⟨hi1, rfl⟩
  · cases b
    · left
      refine ⟨_, mk 0 hi (by simp), ?_, ?_⟩
      · simp [ownC_Xf_eq]
      · simp
    · right
      simp only [if_true] at hend
      obtain ⟨l, hl, h1, h2⟩ := hend
      refine ⟨l, hl, h1, ?_⟩
      rw [ownC_Xf_eq _ _ _ _ _ le_rfl] at h2; simpa using h2
  · by_cases hp : ((i + 1) % 2 = 0 ↔ b = true)
    · left
      refine ⟨_, mk i hi hp, ?_, ?_⟩
      · simp [ownC_Xf_eq]
      · simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false]
        right
        rw [if_neg (by omega), ownC_Xf_eq _ _ _ _ _ (by omega)]
        omega
    · right
      have hp' : ((i + 1 + 1) % 2 = 0 ↔ b = true) := by
        cases b <;> simp at hp ⊢ <;> omega
      refine ⟨_, mk (i + 1) hi1 hp', ?_, ?_⟩
      · simp only [List.headD_cons]; rw [ownC_Xf_eq _ _ _ _ _ (by omega)]; omega
      · simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false]
        left
        rw [if_neg (by omega), ownC_Xf_eq _ _ _ _ _ (by omega)]
        omega
  · cases b
    · right
      simp only [Bool.false_eq_true, if_false] at hend
      obtain ⟨l, hl, h1, h2⟩ := hend
      refine ⟨l, hl, h1, ?_⟩
      rw [ownC_Xf_eq _ _ _ _ _ (by omega)] at h2
      have : 2 * k - 1 = i := by omega
      rw [this] at h2; exact h2
    · left
      refine ⟨_, mk i hi (by simp; omega), ?_, ?_⟩
      · simp [ownC_Xf_eq]
      · simp [hi1]

/-! ## Where the lists and calls sit -/

theorem ownC_f_pos (ψ : CNF) (i : ℕ) (h : fF ψ i < wF ψ i) : (litF ψ i (fF ψ i)).2 = true := by
  unfold fF wF litF at *
  rw [List.getD_eq_getElem _ _ h]
  exact List.findIdx_getElem (w := h)

theorem ownC_f_le (ψ : CNF) (i : ℕ) : fF ψ i ≤ wF ψ i := List.findIdx_le_length

theorem ownC_neg_ne_f {ψ : CNF} {i j : ℕ} (hj : j < wF ψ i) (hn : (litF ψ i j).2 = false) :
    j ≠ fF ψ i := by
  rintro rfl
  rw [ownC_f_pos ψ i hj] at hn
  exact Bool.noConfusion hn

theorem ownC_mem_item {E k : ℕ} {ψ : CNF} {i j : ℕ} (hi : i < ψ.length) (hj : j ≤ wF ψ i)
    {l : List ℕ} (hl : l ∈ itemF E k ψ i j) : l ∈ OWN' E k ψ := by
  simp only [OWN', List.mem_append, List.mem_flatMap, List.mem_range]
  left; left; left; left
  exact ⟨i, hi, j, by omega, hl⟩

theorem ownC_hub_mem {E k : ℕ} {ψ : CNF} {i j : ℕ} (hi : i < ψ.length) (hj : j ≤ wF ψ i)
    (hf : j ≠ fF ψ i) : hubL E k ψ i j ∈ OWN' E k ψ := by
  apply ownC_mem_item (j := j) hi hj
  simp only [itemF, List.mem_append]
  left; right
  simp [hf]

theorem ownC_var_mem {E k : ℕ} {ψ : CNF} {i j : ℕ} (hi : i < ψ.length) (hj : j < wF ψ i)
    (hz : (litF ψ i j).1 = offF ψ i + j) : varL E k ψ i j ∈ OWN' E k ψ := by
  apply ownC_mem_item (j := j) hi (by omega)
  simp only [itemF, List.mem_append]
  right
  simp [hj, hz]

theorem ownC_close1_mem {E k : ℕ} {ψ : CNF} :
    ((2 * E + 1) :: Xf E k (2 * E) (2 * E + 1) (2 * k) ::
      (List.range ψ.length).map (fun i : ℕ => Xf E k (2 * E + 1) (posF E ψ i (wF ψ i)) 1)) ∈
      OWN' E k ψ := by
  simp [OWN']

theorem ownC_close2_mem {E k : ℕ} {ψ : CNF} :
    [3 * E + 2, Xf E k (2 * E) (3 * E + 2) (2 * k)] ∈ OWN' E k ψ := by
  simp [OWN']

theorem ownC_calls_mem {E : ℕ} {ψ : CNF} {i j : ℕ} (hi : i < ψ.length) (hj : j ≤ wF ψ i)
    {c : ℕ × ℕ × Bool}
    (hc : c ∈ (if j < wF ψ i then
        [(2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0), posF E ψ i j, (litF ψ i j).2)]
      else [(2 * E + 1, posF E ψ i j, true)]) ++
    ((List.range (wF ψ i + 1)).filter (fun l : ℕ => decide (j < l))).map
        (fun l : ℕ => (posF E ψ i j, posF E ψ i l, decide (j ≠ fF ψ i))) ++
    (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then
        [(2 * (litF ψ i j).1, 2 * (litF ψ i j).1 + 1, false)] else [])) : c ∈ callsF E ψ := by
  unfold callsF
  rw [List.mem_append]
  left
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by omega), hc⟩⟩

theorem ownC_call_item {E : ℕ} {ψ : CNF} {i j : ℕ} (hi : i < ψ.length) (hj : j < wF ψ i) :
    (2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0), posF E ψ i j, (litF ψ i j).2) ∈
      callsF E ψ :=
  ownC_calls_mem hi hj.le (by simp [hj])

theorem ownC_call_last {E : ℕ} {ψ : CNF} {i : ℕ} (hi : i < ψ.length) :
    (2 * E + 1, posF E ψ i (wF ψ i), true) ∈ callsF E ψ :=
  ownC_calls_mem hi le_rfl (by simp)

theorem ownC_call_pair {E : ℕ} {ψ : CNF} {i j l : ℕ} (hi : i < ψ.length) (hjl : j < l)
    (hl : l ≤ wF ψ i) :
    (posF E ψ i j, posF E ψ i l, decide (j ≠ fF ψ i)) ∈ callsF E ψ := by
  apply ownC_calls_mem (j := j) hi (by omega)
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
  exact List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
    by simpa using hjl⟩, rfl⟩

theorem ownC_call_var {E : ℕ} {ψ : CNF} {i j : ℕ} (hi : i < ψ.length) (hj : j < wF ψ i)
    (hz : (litF ψ i j).1 = offF ψ i + j) :
    (2 * (litF ψ i j).1, 2 * (litF ψ i j).1 + 1, false) ∈ callsF E ψ := by
  apply ownC_calls_mem hi hj.le
  simp [hj, hz]

theorem ownC_call_fresh1 {E : ℕ} {ψ : CNF} : (2 * E, 2 * E + 1, false) ∈ callsF E ψ := by
  simp [callsF]

theorem ownC_call_fresh2 {E : ℕ} {ψ : CNF} : (2 * E, 3 * E + 2, false) ∈ callsF E ψ := by
  simp [callsF]

/-- The inner block of every call is in `OWN'`. -/
theorem ownC_inner_sub {E k : ℕ} {ψ : CNF} {c : ℕ × ℕ × Bool} (hc : c ∈ callsF E ψ)
    {l : List ℕ} (hl : l ∈ innerF E k c.1 c.2.1 c.2.2) : l ∈ OWN' E k ψ := by
  simp only [callsF, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨i, hi, j, hj, hc⟩ | rfl | rfl
  · apply ownC_mem_item (j := j) hi (by omega)
    simp only [itemF, List.mem_append]
    rcases hc with (hc | hc) | hc
    · left; left; left; left
      by_cases hjw : j < wF ψ i
      · rw [if_pos hjw] at hc ⊢
        simp only [List.mem_singleton] at hc; subst hc; exact hl
      · rw [if_neg hjw] at hc ⊢
        simp only [List.mem_singleton] at hc; subst hc; exact hl
    · left; left; left; right
      simp only [List.mem_map] at hc
      obtain ⟨l', hl', rfl⟩ := hc
      exact List.mem_flatMap.mpr ⟨l', hl', hl⟩
    · left; left; right
      by_cases hcond : j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j
      · rw [if_pos hcond] at hc ⊢
        simp only [List.mem_singleton] at hc; subst hc; exact hl
      · rw [if_neg hcond] at hc; simp at hc
  · simp only [OWN', List.mem_append]
    left; left; left; right; exact hl
  · simp only [OWN', List.mem_append]
    left; left; right; exact hl

/-- What a vertex entry owns: the `u` end of a call at slot 1 or its `v` end at slot `2k`. -/
def ownC_VOK (E k : ℕ) (ψ : CNF) (l : List ℕ) : Prop :=
  ∀ y ∈ l.tail, ∃ c ∈ callsF E ψ, (l.headD 0 = c.1 ∧ y = Xf E k c.1 c.2.1 1) ∨
    (l.headD 0 = c.2.1 ∧ y = Xf E k c.1 c.2.1 (2 * k))

/-- Every list of `OWN'` is an inner triple of a call or a vertex list. -/
theorem ownC_classify {E k : ℕ} {ψ : CNF} {l : List ℕ} (hl : l ∈ OWN' E k ψ) :
    (∃ c ∈ callsF E ψ, l ∈ innerF E k c.1 c.2.1 c.2.2) ∨ ownC_VOK E k ψ l := by
  simp only [OWN', List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton] at hl
  rcases hl with (((⟨i, hi, j, hj, hl⟩ | hl) | hl) | rfl) | rfl
  · have hj' : j ≤ wF ψ i := by omega
    simp only [itemF, List.mem_append] at hl
    rcases hl with (((hl | hl) | hl) | hl) | hl
    · left
      by_cases hjw : j < wF ψ i
      · rw [if_pos hjw] at hl
        exact ⟨_, ownC_call_item hi hjw, hl⟩
      · rw [if_neg hjw] at hl
        have : j = wF ψ i := by omega
        subst this
        exact ⟨_, ownC_call_last hi, hl⟩
    · left
      simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq] at hl
      obtain ⟨l', ⟨hl', hjl⟩, hl⟩ := hl
      exact ⟨_, ownC_call_pair hi hjl (by omega), hl⟩
    · left
      split_ifs at hl with hc
      · exact ⟨_, ownC_call_var hi hc.1 hc.2, hl⟩
      · simp at hl
    · right
      split_ifs at hl with hf
      · simp only [List.mem_singleton] at hl
        subst hl
        intro y hy
        simp only [hubL, List.headD_cons, List.tail_cons, List.mem_append, List.mem_map,
          List.mem_filter, List.mem_range, decide_eq_true_eq] at hy ⊢
        rcases hy with (hy | hy) | ⟨l', ⟨hl', hjl⟩, rfl⟩
        · split_ifs at hy with hc
          · simp only [List.mem_singleton] at hy; subst hy
            refine ⟨_, ownC_call_item hi hc.1, Or.inr ⟨rfl, ?_⟩⟩
            simp [hc.2]
          · simp at hy
        · split_ifs at hy with hc
          · simp only [List.mem_singleton] at hy; subst hy
            exact ⟨_, ownC_call_pair hi hc hj', Or.inr ⟨rfl, rfl⟩⟩
          · simp at hy
        · exact ⟨_, ownC_call_pair hi hjl (by omega), Or.inl ⟨rfl, rfl⟩⟩
      · simp at hl
    · right
      split_ifs at hl with hc
      · simp only [List.mem_singleton] at hl
        subst hl
        intro y hy
        simp only [varL, List.headD_cons, List.tail_cons, List.mem_cons, List.mem_flatMap,
          List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hy ⊢
        rcases hy with rfl | ⟨i', hi', j', ⟨hj', hz, hp⟩, rfl⟩
        · exact ⟨_, ownC_call_var hi hc.1 hc.2, Or.inr ⟨rfl, rfl⟩⟩
        · refine ⟨_, ownC_call_item hi' hj', Or.inl ⟨?_, ?_⟩⟩
          · simp [hz, hp]
          · simp [hz, hp]
      · simp at hl
  · left; exact ⟨_, ownC_call_fresh1, hl⟩
  · left; exact ⟨_, ownC_call_fresh2, hl⟩
  · right
    intro y hy
    simp only [List.headD_cons, List.tail_cons, List.mem_cons, List.mem_map,
      List.mem_range] at hy ⊢
    rcases hy with rfl | ⟨i, hi, rfl⟩
    · exact ⟨_, ownC_call_fresh1, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨_, ownC_call_last hi, Or.inl ⟨rfl, rfl⟩⟩
  · right
    intro y hy
    simp only [List.headD_cons, List.tail_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hy ⊢
    subst hy
    exact ⟨_, ownC_call_fresh2, Or.inr ⟨rfl, rfl⟩⟩

/-- Every variable occurrence has a first occurrence whose position is the variable. -/
def ownC_First (ψ : CNF) : Prop :=
  ∀ i, i < ψ.length → ∀ j, j < wF ψ i → ∃ i0, i0 < ψ.length ∧ ∃ j0, j0 < wF ψ i0 ∧
    (litF ψ i0 j0).1 = (litF ψ i j).1 ∧ (litF ψ i j).1 = offF ψ i0 + j0

/-- The end edge of every call not covered by its inner block is owned by a vertex list. -/
theorem ownC_end_own {E k : ℕ} {ψ : CNF} (hF : ownC_First ψ) {c : ℕ × ℕ × Bool}
    (hc : c ∈ callsF E ψ) :
    if c.2.2 then ownC_Own (OWN' E k ψ) c.1 (Xf E k c.1 c.2.1 1)
    else ownC_Own (OWN' E k ψ) c.2.1 (Xf E k c.1 c.2.1 (2 * k)) := by
  simp only [callsF, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨i, hi, j, hj, hc⟩ | rfl | rfl
  · have hj' : j ≤ wF ψ i := by omega
    rcases hc with (hc | hc) | hc
    · by_cases hjw : j < wF ψ i
      · rw [if_pos hjw] at hc
        simp only [List.mem_singleton] at hc; subst hc
        cases hb : (litF ψ i j).2
        · simp only [Bool.false_eq_true, if_false]
          refine ⟨_, ownC_hub_mem hi hj' (ownC_neg_ne_f hjw hb), rfl, ?_⟩
          simp [hubL, hjw, hb]
        · simp only [if_true]
          obtain ⟨i0, hi0, j0, hj0, h1, h2⟩ := hF i hi j hjw
          refine ⟨_, ownC_var_mem hi0 hj0 (h1.trans h2), ?_, ?_⟩
          · simp [varL, h1]
          · simp only [varL, List.tail_cons, List.mem_cons, List.mem_flatMap, List.mem_map,
              List.mem_filter, List.mem_range, decide_eq_true_eq]
            right
            exact ⟨i, hi, j, ⟨hjw, h1.symm, hb⟩, by simp [h1]⟩
      · rw [if_neg hjw] at hc
        simp only [List.mem_singleton] at hc; subst hc
        have : j = wF ψ i := by omega
        subst this
        simp only [if_true]
        refine ⟨_, ownC_close1_mem, rfl, ?_⟩
        simp only [List.tail_cons, List.mem_cons, List.mem_map, List.mem_range]
        exact Or.inr ⟨i, hi, rfl⟩
    · simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
      obtain ⟨l', ⟨hl', hjl⟩, rfl⟩ := hc
      by_cases hf : j = fF ψ i
      · simp only [hf, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
        refine ⟨_, ownC_hub_mem hi (by omega) (by omega), rfl, ?_⟩
        simp only [hubL, List.tail_cons, List.mem_append]
        left; right
        rw [if_pos (by omega)]
        simp
      · simp only [ne_eq, hf, not_false_eq_true, decide_true, if_true]
        refine ⟨_, ownC_hub_mem hi hj' hf, rfl, ?_⟩
        simp only [hubL, List.tail_cons, List.mem_append, List.mem_map, List.mem_filter,
          List.mem_range, decide_eq_true_eq]
        right
        exact ⟨l', ⟨hl', hjl⟩, rfl⟩
    · split_ifs at hc with hcond
      · simp only [List.mem_singleton] at hc; subst hc
        simp only [Bool.false_eq_true, if_false]
        refine ⟨_, ownC_var_mem hi hcond.1 hcond.2, rfl, ?_⟩
        simp [varL]
      · simp at hc
  · simp only [Bool.false_eq_true, if_false]
    exact ⟨_, ownC_close1_mem, rfl, by simp⟩
  · simp only [Bool.false_eq_true, if_false]
    exact ⟨_, ownC_close2_mem, rfl, by simp⟩

/-- Clause (c1) on values: owned pairs are exactly the thread edges of the calls. -/
theorem ownC_c1_vals {E k : ℕ} {ψ : CNF} (hk : 1 ≤ k) (hF : ownC_First ψ) (x y : ℕ) :
    (∃ c ∈ callsF E ψ, ownC_TR E k c.1 c.2.1 x y ∨ ownC_TR E k c.1 c.2.1 y x) ↔
      ownC_Own (OWN' E k ψ) x y ∨ ownC_Own (OWN' E k ψ) y x := by
  constructor
  · rintro ⟨c, hc, h⟩
    have key := fun {x y : ℕ} (h : ownC_TR E k c.1 c.2.1 x y) =>
      ownC_tr_own (b := c.2.2) hk (fun l hl => ownC_inner_sub hc hl) (ownC_end_own hF hc) h
    rcases h with h | h
    · exact key h
    · exact (key h).symm
  · have one : ∀ x y, ownC_Own (OWN' E k ψ) x y →
        ∃ c ∈ callsF E ψ, ownC_TR E k c.1 c.2.1 x y ∨ ownC_TR E k c.1 c.2.1 y x := by
      rintro x y ⟨l, hl, hx, hy⟩
      rcases ownC_classify hl with ⟨c, hc, hlc⟩ | hv
      · exact ⟨c, hc, ownC_inner_tr hlc hx hy⟩
      · obtain ⟨c, hc, h⟩ := hv y hy
        refine ⟨c, hc, Or.inr ?_⟩
        rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
        · exact ⟨0, by omega, by unfold Xf; omega, Or.inl ⟨rfl, by omega⟩⟩
        · exact ⟨2 * k - 1, by omega, by unfold Xf; omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
    rintro (h | h)
    · exact one x y h
    · obtain ⟨c, hc, h⟩ := one y x h
      exact ⟨c, hc, h.symm⟩

/-! ## The renaming has first occurrences -/

/-- The flattened occurrence list of the renaming. -/
def ownC_flat (φ : CNF) : List (Option Literal) := φ.flatMap (fun c => c.map some ++ [none])

theorem ownC_flat_get (φ : CNF) : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
    (ownC_flat φ)[offF φ i + j]? =
      some (if j < (φ.getD i []).length then some ((φ.getD i []).getD j (0, false)) else none) := by
  induction φ with
  | nil => intro i j hi; simp at hi
  | cons c φ ih =>
    intro i j hi hj
    have hflat : ownC_flat (c :: φ) = (c.map some ++ [none]) ++ ownC_flat φ := by
      simp [ownC_flat]
    rw [hflat]
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hj ⊢
      have h0 : offF (c :: φ) 0 = 0 := by simp [offF]
      rw [h0, Nat.zero_add, List.getElem?_append_left (by simp; omega)]
      by_cases hjc : j < c.length
      · rw [List.getElem?_append_left (by simpa using hjc)]
        simp [hjc, List.getD_eq_getElem _ _ hjc]
      · have : j = c.length := by omega
        subst this
        simp
    | succ i =>
      simp only [List.getD_cons_succ] at hj ⊢
      have h0 : offF (c :: φ) (i + 1) = (c.length + 1) + offF φ i := by
        simp [offF, List.take_succ_cons]
      rw [h0, Nat.add_assoc, List.getElem?_append_right (by simp)]
      simp only [List.length_append, List.length_map, List.length_singleton,
        Nat.add_sub_cancel_left]
      exact ih i j (by simpa using hi) hj

theorem ownC_flat_decomp (φ : CNF) : ∀ p, p < (ownC_flat φ).length →
    ∃ i0, i0 < φ.length ∧ ∃ j0, j0 ≤ (φ.getD i0 []).length ∧ p = offF φ i0 + j0 := by
  induction φ with
  | nil => intro p hp; simp [ownC_flat] at hp
  | cons c φ ih =>
    intro p hp
    have hflat : ownC_flat (c :: φ) = (c.map some ++ [none]) ++ ownC_flat φ := by
      simp [ownC_flat]
    rw [hflat] at hp
    simp only [List.length_append, List.length_map, List.length_singleton] at hp
    by_cases hpc : p < c.length + 1
    · exact ⟨0, by simp, p, by simp; omega, by simp [offF]⟩
    · obtain ⟨i0, hi0, j0, hj0, he⟩ := ih (p - (c.length + 1)) (by omega)
      refine ⟨i0 + 1, by simp; omega, j0, by simpa using hj0, ?_⟩
      simp only [offF, List.take_succ_cons, List.map_cons, List.sum_cons] at he ⊢
      omega

theorem ownC_ren_lit (φ : CNF) {i j : ℕ} (hi : i < φ.length) (hj : j < wF φ i) :
    litF (REN φ) i j = ((ownC_flat φ).findIdx
      (fun o => o.any (fun l => l.1 == (litF φ i j).1)), (litF φ i j).2) := by
  unfold wF at hj
  have h1 : (REN φ).getD i [] = (φ.getD i []).map (fun l : Literal =>
      ((ownC_flat φ).findIdx (fun o => o.any (fun l' => l'.1 == l.1)), l.2)) := by
    simp only [REN, ownC_flat, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases φ[i]? <;> rfl
  unfold litF
  rw [h1, List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
  simp

theorem ownC_first_ren (φ : CNF) : ownC_First (REN φ) := by
  intro i hi j hj
  rw [ren_length] at hi
  have hw : ∀ i, wF (REN φ) i = wF φ i := ren_getD_length φ
  rw [hw] at hj
  set x := (litF φ i j).1 with hx
  have hmem : (ownC_flat φ)[offF φ i + j]? = some (some (litF φ i j)) := by
    rw [ownC_flat_get φ i j hi hj.le, if_pos (show j < (φ.getD i []).length from hj)]
    rfl
  have hex : ∃ o ∈ ownC_flat φ, o.any (fun l => l.1 == x) = true := by
    refine ⟨some (litF φ i j), List.mem_of_getElem? hmem, by simp [hx]⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  have hP := List.findIdx_getElem (w := hlt)
  obtain ⟨i0, hi0, j0, hj0, he⟩ := ownC_flat_decomp φ _ hlt
  have hget := ownC_flat_get φ i0 j0 hi0 hj0
  rw [← he, List.getElem?_eq_getElem hlt] at hget
  simp only [Option.some.injEq] at hget
  rw [hget] at hP
  by_cases hj0w : j0 < (φ.getD i0 []).length
  · rw [if_pos hj0w] at hP
    simp only [Option.any_some, beq_iff_eq] at hP
    have hj0' : j0 < wF φ i0 := hj0w
    refine ⟨i0, by rw [ren_length]; exact hi0, j0, by rw [hw]; exact hj0', ?_, ?_⟩
    · have hP' : (litF φ i0 j0).1 = x := hP
      rw [ownC_ren_lit φ hi0 hj0', ownC_ren_lit φ hi hj, hP']
    · rw [ownC_ren_lit φ hi hj, ren_off]
      exact he
  · rw [if_neg hj0w] at hP
    simp at hP

end PEqualNP.MetaComplexity.Helpers.OwnerLink
