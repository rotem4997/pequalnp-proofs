import Mathlib

/-!
# The 2k-fold subdivision of a graph on `Fin m` (chain link L5, gap G3)

Numbering of SUBDIVISION-FOR-BUILDER.md section 1.2 (slot placement, no edge enumeration). For
`H : SimpleGraph (Fin m)` and `k`, the subdivision lives on `Fin (nS m k)`, `nS m k = m + 2k m^2`:

* the HUBS are the indices `0, .., m - 1` (the vertices of `H`, same index);
* a SLOT is a pair `(u, v)` of vertices of `H`; it is LIVE iff `u < v` and `H.Adj u v`; the slot
  `(u, v)` owns the `2k` indices `m + 2k (u m + v) + i`, `i < 2k` (paper position `t = i + 1`);
* the thread of a live slot is `u, m + 2k (u m + v), .., m + 2k (u m + v) + 2k - 1, v`: a walk of
  `2k + 1` steps. Indices of non-live slots are isolated.

The adjacency is `SimpleGraph.fromRel` of an explicit relation (arithmetic and bounded
existentials), hence symmetric and irreflexive by construction, decidable when `H.Adj` is.

Sanity lemmas proved here: unique decoding of thread indices (`thr_inj`, the sheet's S1), every
non-hub index is a slot index (`inner_decomp`), consecutive thread vertices are adjacent
(`adj_thread`), the neighbours of an inner vertex are exactly its two thread neighbours on a live
slot and none on a dead slot (`inner_adj_iff`, `inner_two`), and the neighbours of a hub are the
first or last inner vertices of the threads at it (`hub_adj_iff`).
-/

namespace PEqualNP.MetaComplexity.Subdiv

/-- The number of vertices of the subdivision: `m` hubs and `2k` indices for each of the `m * m`
slots. -/
def nS (m k : ℕ) : ℕ := m + 2 * k * m * m

/-- One step of a thread, oriented from the lower end `u` to the upper end `v` of a live slot:
`x` is the vertex at position `p` and `y` the vertex at position `p + 1`, where position `0` is
the hub `u`, position `2k + 1` is the hub `v`, and position `t` with `1 ≤ t ≤ 2k` is the index
`m + 2k (u m + v) + (t - 1)`. -/
def SubRel {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (nS m k)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : Fin (2 * k + 1),
    x.val = (if p.val = 0 then u.val else m + 2 * k * (u.val * m + v.val) + p.val - 1) ∧
    y.val = (if p.val = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + p.val)

/-- The 2k-fold subdivision of `H`: two indices are adjacent iff they are distinct and one thread
step joins them, in one of the two orders. -/
def subdiv {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) : SimpleGraph (Fin (nS m k)) :=
  SimpleGraph.fromRel (SubRel k H)

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidableRel (SubRel k H) :=
  fun x y => inferInstanceAs (Decidable (∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : Fin (2 * k + 1),
    x.val = (if p.val = 0 then u.val else m + 2 * k * (u.val * m + v.val) + p.val - 1) ∧
    y.val = (if p.val = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + p.val)))

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidableRel (subdiv k H).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (SubRel k H x y ∨ SubRel k H y x)))

/-- The index lies on the thread of a live slot. -/
def OnThr {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (j : Fin (nS m k)) : Prop :=
  ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧
    j.val = m + 2 * k * (u.val * m + v.val) + i.val

instance {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    DecidablePred (OnThr k H) :=
  fun j => inferInstanceAs (Decidable (∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧
    j.val = m + 2 * k * (u.val * m + v.val) + i.val))

/-- The thread label (GRAPH-FOR-BUILDER section 3, SUBDIVISION-FOR-BUILDER 1.2): the position
`i + 1` on the inner vertex at offset `i` of a live slot, `0` elsewhere (hubs, dead slots). -/
def pos {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (j : Fin (nS m k)) : ℕ :=
  if OnThr k H j then (j.val - m) % (2 * k) + 1 else 0

/-- The forward cover (SUBDIVISION-FOR-BUILDER 2.1): the hubs in `T`, and on each live slot
`(u, v)` the positions `t = i + 1` with `t` even iff `u ∈ T`. -/
def fwd {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m)) :
    Finset (Fin (nS m k)) :=
  Finset.univ.filter (fun j => (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k),
    u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T))

/-- The backward map (SUBDIVISION-FOR-BUILDER 2.4): the hubs in `U`, and the lower end of every
live slot whose two ends are both outside `U`. -/
def back {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (U : Finset (Fin (nS m k))) : Finset (Fin m) :=
  Finset.univ.filter (fun u => (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧
    (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val))

/-! ## Sanity lemmas -/

theorem adj_iff {m k : ℕ} {H : SimpleGraph (Fin m)} {x y : Fin (nS m k)} :
    (subdiv k H).Adj x y ↔ x ≠ y ∧ (SubRel k H x y ∨ SubRel k H y x) :=
  Iff.rfl

/-- Division with remainder is unique (used twice: by `2k`, then by `m`). -/
theorem div_inj {d i i' s s' : ℕ} (hs : s < d) (hs' : s' < d)
    (h : d * i + s = d * i' + s') : i = i' ∧ s = s' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have : d * (i + 1) ≤ d * i' := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_succ] at this
    omega
  · subst heq; omega
  · have : d * (i' + 1) ≤ d * i := Nat.mul_le_mul_left _ hgt
    rw [Nat.mul_succ] at this
    omega

/-- S1 of the sheet (1.3): thread indices decode uniquely. -/
theorem thr_inj {m k : ℕ} {u v u' v' : Fin m} {i i' : ℕ} (hi : i < 2 * k) (hi' : i' < 2 * k)
    (h : m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i') :
    u = u' ∧ v = v' ∧ i = i' := by
  obtain ⟨h1, h2⟩ := div_inj (d := 2 * k) (i := u.val * m + v.val) (i' := u'.val * m + v'.val)
    hi hi' (by omega)
  have h1' : m * u.val + v.val = m * u'.val + v'.val := by
    rw [Nat.mul_comm m, Nat.mul_comm m]; exact h1
  obtain ⟨h3, h4⟩ := div_inj (d := m) v.2 v'.2 h1'
  exact ⟨Fin.ext h3, Fin.ext h4, h2⟩

theorem slot_lt {m : ℕ} (u v : Fin m) : u.val * m + v.val + 1 ≤ m * m := by
  have : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right _ u.2
  rw [Nat.succ_mul] at this
  have := v.2
  omega

theorem thr_lt {m k : ℕ} (u v : Fin m) {i : ℕ} (hi : i < 2 * k) :
    m + 2 * k * (u.val * m + v.val) + i < nS m k := by
  have : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ (slot_lt u v)
  rw [Nat.mul_succ] at this
  unfold nS
  rw [Nat.mul_assoc (2 * k) m m]
  omega

/-- Every index that is not a hub is a slot index `m + 2k (u m + v) + i` with `i < 2k`. -/
theorem inner_decomp {m k : ℕ} (x : Fin (nS m k)) (hx : m ≤ x.val) :
    ∃ u v : Fin m, ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val := by
  have e : nS m k = m + 2 * k * (m * m) := by unfold nS; rw [Nat.mul_assoc (2 * k) m m]
  have hxN : x.val < m + 2 * k * (m * m) := x.2.trans_eq e
  have hk : 0 < 2 * k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hxN; omega
    · omega
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hxN
    · exact h
  have hq : x.val - m < 2 * k * (m * m) := by omega
  have hs : (x.val - m) / (2 * k) < m * m :=
    (Nat.div_lt_iff_lt_mul hk).2 (by rw [Nat.mul_comm (m * m)]; exact hq)
  refine ⟨⟨(x.val - m) / (2 * k) / m, ?_⟩, ⟨(x.val - m) / (2 * k) % m, Nat.mod_lt _ hm⟩,
    ⟨(x.val - m) % (2 * k), Nat.mod_lt _ hk⟩, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hm).2 hs
  · simp only
    have h1 := Nat.div_add_mod (x.val - m) (2 * k)
    have h2 := Nat.div_add_mod ((x.val - m) / (2 * k)) m
    rw [Nat.mul_comm m] at h2
    rw [h2]
    omega

/-- The vertex at position `t ≤ 2k + 1` of the thread of slot `(u, v)` (meaningful on a live
slot). -/
def pt {m k : ℕ} (u v : Fin m) (t : Fin (2 * k + 2)) : Fin (nS m k) :=
  ⟨if t.val = 0 then u.val else if t.val = 2 * k + 1 then v.val
    else m + 2 * k * (u.val * m + v.val) + t.val - 1, by
    have hu := u.2
    have hv := v.2
    have h0 : m ≤ nS m k := by unfold nS; omega
    split_ifs with h1 h2
    · omega
    · omega
    · have := thr_lt (k := k) u v (i := t.val - 1) (by omega)
      omega⟩

/-- Each live thread is a walk of `2k + 1` steps: consecutive positions are adjacent (`k ≥ 1`). -/
theorem adj_thread {m k : ℕ} (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) {u v : Fin m} (huv : u < v)
    (hadj : H.Adj u v) (t : ℕ) (ht : t < 2 * k + 1) :
    (subdiv k H).Adj (pt u v ⟨t, by omega⟩) (pt u v ⟨t + 1, by omega⟩) := by
  have hu := u.2
  have hv := v.2
  have huv' : u.val < v.val := huv
  refine ⟨?_, Or.inl ⟨u, v, huv, hadj, ⟨t, ht⟩, ?_, ?_⟩⟩
  · intro h
    have h' := congrArg Fin.val h
    dsimp only [pt] at h'
    split_ifs at h' <;> omega
  · dsimp only [pt]
    split_ifs <;> omega
  · dsimp only [pt]
    rw [if_neg (by omega)]
    by_cases h2 : t = 2 * k
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]; omega

/-- The neighbours of the inner index `x = m + 2k (u m + v) + i` (`i < 2k`): none if the slot is
dead; on a live slot, below it the previous inner vertex, or the hub `u` if `i = 0`, and above it
the next inner vertex, or the hub `v` if `i = 2k - 1`. -/
theorem inner_adj_iff {m k : ℕ} (H : SimpleGraph (Fin m)) (u v : Fin m) (i : Fin (2 * k))
    (x y : Fin (nS m k)) (hx : x.val = m + 2 * k * (u.val * m + v.val) + i.val) :
    (subdiv k H).Adj x y ↔ (u < v ∧ H.Adj u v) ∧
      ((y.val = if i.val = 0 then u.val else x.val - 1) ∨
       (y.val = if i.val + 1 = 2 * k then v.val else x.val + 1)) := by
  have hu := u.2
  have hv := v.2
  have hi := i.2
  constructor
  · rintro ⟨hne, ⟨u', v', huv', hadj', p, h1, h2⟩ | ⟨u', v', huv', hadj', p, h1, h2⟩⟩
    · have hu' := u'.2
      have hp := p.2
      by_cases hp0 : p.val = 0
      · rw [if_pos hp0] at h1; omega
      rw [if_neg hp0] at h1
      obtain ⟨rfl, rfl, hip⟩ := thr_inj (u := u) (v := v) (u' := u') (v' := v')
        (i := i.val) (i' := p.val - 1) hi (by omega) (by omega)
      refine ⟨⟨huv', hadj'⟩, Or.inr ?_⟩
      by_cases hp2 : p.val = 2 * k
      · rw [if_pos hp2] at h2; rw [if_pos (by omega)]; exact h2
      · rw [if_neg hp2] at h2; rw [if_neg (by omega)]; omega
    · have hv' := v'.2
      have hp := p.2
      by_cases hp2 : p.val = 2 * k
      · rw [if_pos hp2] at h2; omega
      rw [if_neg hp2] at h2
      obtain ⟨rfl, rfl, hip⟩ := thr_inj (u := u) (v := v) (u' := u') (v' := v')
        (i := i.val) (i' := p.val) hi (by omega) (by omega)
      refine ⟨⟨huv', hadj'⟩, Or.inl ?_⟩
      by_cases hp0 : p.val = 0
      · rw [if_pos hp0] at h1; rw [if_pos (by omega)]; exact h1
      · rw [if_neg hp0] at h1; rw [if_neg (by omega)]; omega
  · rintro ⟨⟨huv, hadj⟩, h | h⟩
    · refine ⟨?_, Or.inr ⟨u, v, huv, hadj, ⟨i.val, by omega⟩, ?_, ?_⟩⟩
      · intro hxy; subst hxy; split_ifs at h <;> omega
      · simp only
        split_ifs at h ⊢ <;> omega
      · simp only
        rw [if_neg (by omega)]; exact hx
    · refine ⟨?_, Or.inl ⟨u, v, huv, hadj, ⟨i.val + 1, by omega⟩, ?_, ?_⟩⟩
      · intro hxy; subst hxy; split_ifs at h <;> omega
      · simp only
        rw [if_neg (by omega)]; omega
      · simp only
        split_ifs at h ⊢ <;> omega

/-- An inner index of a live slot has exactly two neighbours (`k ≥ 1`); of a dead slot, none. -/
theorem inner_two {m k : ℕ} (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) (u v : Fin m) (i : Fin (2 * k))
    (x : Fin (nS m k)) (hx : x.val = m + 2 * k * (u.val * m + v.val) + i.val)
    (huv : u < v) (hadj : H.Adj u v) :
    ∃ a b : Fin (nS m k), a ≠ b ∧ ∀ y, (subdiv k H).Adj x y ↔ y = a ∨ y = b := by
  have hu := u.2
  have hv := v.2
  have hi := i.2
  have hN := x.2
  have h0 : m ≤ nS m k := by unfold nS; omega
  refine ⟨⟨if i.val = 0 then u.val else x.val - 1, by split_ifs <;> omega⟩,
    ⟨if i.val + 1 = 2 * k then v.val else x.val + 1, by
      split_ifs with h
      · omega
      · have := thr_lt (k := k) u v (i := i.val + 1) (by omega); omega⟩, ?_, ?_⟩
  · intro h
    have h' := congrArg Fin.val h
    simp only at h'
    split_ifs at h' <;> omega
  · intro y
    rw [inner_adj_iff H u v i x y hx, Fin.ext_iff, Fin.ext_iff]
    simp only [huv, hadj, and_self, true_and]

/-- A hub `x` (index below `m`) is adjacent exactly to the first inner vertex of each live thread
with lower end `x` and to the last inner vertex of each live thread with upper end `x`
(`k ≥ 1`). -/
theorem hub_adj_iff {m k : ℕ} (H : SimpleGraph (Fin m)) (hk : 1 ≤ k)
    (x y : Fin (nS m k)) (hx : x.val < m) :
    (subdiv k H).Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
      ((u.val = x.val ∧ y.val = m + 2 * k * (u.val * m + v.val)) ∨
       (v.val = x.val ∧ y.val = m + 2 * k * (u.val * m + v.val) + (2 * k - 1))) := by
  constructor
  · rintro ⟨hne, ⟨u, v, huv, hadj, p, h1, h2⟩ | ⟨u, v, huv, hadj, p, h1, h2⟩⟩
    · have hp := p.2
      refine ⟨u, v, huv, hadj, Or.inl ⟨?_, ?_⟩⟩
      · by_cases hp0 : p.val = 0
        · rw [if_pos hp0] at h1; omega
        · rw [if_neg hp0] at h1; omega
      · by_cases hp0 : p.val = 0
        · rw [if_neg (by omega)] at h2; omega
        · rw [if_neg hp0] at h1; omega
    · have hp := p.2
      refine ⟨u, v, huv, hadj, Or.inr ⟨?_, ?_⟩⟩
      · by_cases hp2 : p.val = 2 * k
        · rw [if_pos hp2] at h2; omega
        · rw [if_neg hp2] at h2; omega
      · by_cases hp2 : p.val = 2 * k
        · rw [if_neg (by omega)] at h1; omega
        · rw [if_neg hp2] at h2; omega
  · rintro ⟨u, v, huv, hadj, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨fun h => by subst h; omega, Or.inl ⟨u, v, huv, hadj, ⟨0, by omega⟩, ?_, ?_⟩⟩
      · simp only [if_pos]; omega
      · simp only; rw [if_neg (by omega)]; omega
    · refine ⟨fun h => by subst h; omega, Or.inr ⟨u, v, huv, hadj, ⟨2 * k, by omega⟩, ?_, ?_⟩⟩
      · simp only; rw [if_neg (by omega)]; omega
      · simp only [if_pos]; omega

end PEqualNP.MetaComplexity.Subdiv
