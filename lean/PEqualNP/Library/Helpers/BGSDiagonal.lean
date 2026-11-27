import PEqualNP.Defs
import PEqualNP.Library.Helpers.OutputLength

/-!
# The Baker-Gill-Solovay diagonal, as combinatorics

Helper module for `L-lib-059` (proofs only, no statement may use it). Given deciders `g i`,
uniform in the oracle, whose answer on `x` depends on the oracle only through at most
`q i (length of x)` strings, an oracle `B` is built in stages so that no `g i B` is the language
`{x | B has a string of length |x|}`.

Stage `i` holds a finite set `S` of strings put in `B` so far and a length bound `N` above every
length fixed so far. It picks `n` at least `N` with `q i n < 2 ^ n`, asks `g i` about the string
of `n` falses relative to `S`, and puts in `B` one string of length `n` that `g i` did not depend
on exactly when `g i` says no. The next bound is above `n` and above every string `g i` depended
on, so later stages never disturb the answer.
-/

namespace PEqualNP.Library.Helpers.BGS

open Classical

/-- Fewer than `2 ^ n` strings miss some string of length `n`. -/
theorem exists_len_not_mem (Q : Finset (List Bool)) (n : ℕ) (h : Q.card < 2 ^ n) :
    ∃ w : List Bool, w.length = n ∧ w ∉ Q := by
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ : Finset (Fin n → Bool)).image List.ofFn ⊆ Q := by
    intro y hy
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hy
    exact hne _ (by simp)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  omega

/-- A polynomial is below `2 ^ n` at some `n` above any threshold. -/
theorem exists_stage_len (p : Polynomial ℕ) (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ p.eval n < 2 ^ n := by
  obtain ⟨a, d, h⟩ := poly_le_monomial p
  obtain ⟨n, hn, hlt⟩ := exists_pow_lt a d (max N 1)
  exact ⟨n, le_of_max_le_left hn, lt_of_le_of_lt (h n (le_of_max_le_right hn)) hlt⟩

/-- The state after a stage: the strings put in the oracle so far and a length bound. -/
structure St where
  /-- The strings put in the oracle so far. -/
  S : Finset (List Bool)
  /-- Every length fixed so far is below this bound. -/
  N : ℕ

variable (g : ℕ → Language Bool → Language Bool) (q : ℕ → Polynomial ℕ)
  (Qf : ℕ → Language Bool → List Bool → Finset (List Bool))

/-- The length stage `i` works at, given the bound `N`. -/
noncomputable def len (i N : ℕ) : ℕ := Classical.choose (exists_stage_len (q i) N)

theorem len_ge (i N : ℕ) : N ≤ len q i N := (Classical.choose_spec (exists_stage_len (q i) N)).1

theorem len_lt (i N : ℕ) : (q i).eval (len q i N) < 2 ^ len q i N :=
  (Classical.choose_spec (exists_stage_len (q i) N)).2

/-- A string of length `n` outside `Q`, when there is one. -/
noncomputable def pick (Q : Finset (List Bool)) (n : ℕ) : List Bool :=
  if h : ∃ w : List Bool, w.length = n ∧ w ∉ Q then Classical.choose h else []

theorem pick_spec (Q : Finset (List Bool)) (n : ℕ) (h : Q.card < 2 ^ n) :
    (pick Q n).length = n ∧ pick Q n ∉ Q := by
  have hex := exists_len_not_mem Q n h
  unfold pick
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact Classical.choose_spec hex

/-- The oracle so far, as a language. -/
def asLang (s : St) : Language Bool := {y | y ∈ s.S}

/-- The input stage `i` diagonalizes on. -/
noncomputable def xin (i : ℕ) (s : St) : List Bool := List.replicate (len q i s.N) false

/-- The strings stage `i` depends on. -/
noncomputable def qset (i : ℕ) (s : St) : Finset (List Bool) := Qf i (asLang s) (xin q i s)

/-- One stage. -/
noncomputable def stepSt (i : ℕ) (s : St) : St where
  S := if xin q i s ∈ g i (asLang s) then s.S
    else insert (pick (qset q Qf i s) (len q i s.N)) s.S
  N := max ((qset q Qf i s).sup List.length) (len q i s.N) + 1

/-- The states after each stage. -/
noncomputable def stages : ℕ → St
  | 0 => ⟨∅, 0⟩
  | i + 1 => stepSt g q Qf i (stages i)

theorem stages_zero_S : (stages g q Qf 0).S = ∅ := rfl

theorem stages_succ (i : ℕ) : stages g q Qf (i + 1) = stepSt g q Qf i (stages g q Qf i) := rfl

theorem stepSt_S (i : ℕ) (s : St) : (stepSt g q Qf i s).S =
    if xin q i s ∈ g i (asLang s) then s.S else insert (pick (qset q Qf i s) (len q i s.N)) s.S :=
  rfl

theorem stepSt_N (i : ℕ) (s : St) :
    (stepSt g q Qf i s).N = max ((qset q Qf i s).sup List.length) (len q i s.N) + 1 := rfl

theorem mem_stepSt_S {i : ℕ} {s : St} {y : List Bool} (hy : y ∈ (stepSt g q Qf i s).S) :
    y ∈ s.S ∨ (xin q i s ∉ g i (asLang s) ∧ y = pick (qset q Qf i s) (len q i s.N)) := by
  rw [stepSt_S] at hy
  by_cases hx : xin q i s ∈ g i (asLang s)
  · simp only [hx, ↓reduceIte] at hy
    exact Or.inl hy
  · simp only [hx, ↓reduceIte] at hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl h

theorem subset_stepSt_S (i : ℕ) (s : St) : s.S ⊆ (stepSt g q Qf i s).S := by
  rw [stepSt_S]
  by_cases hx : xin q i s ∈ g i (asLang s)
  · simp only [hx, ↓reduceIte]; exact Finset.Subset.refl _
  · simp only [hx, ↓reduceIte]
    exact Finset.subset_insert _ _

/-- The oracle: every string put in at some stage. -/
def oracle : Language Bool := {y | ∃ i, y ∈ (stages g q Qf i).S}

section
variable (hQcard : ∀ i A x, (Qf i A x).card ≤ (q i).eval x.length)
include hQcard

theorem card_lt (i : ℕ) (s : St) : (qset q Qf i s).card < 2 ^ len q i s.N := by
  have h := hQcard i (asLang s) (xin q i s)
  have hl : (xin q i s).length = len q i s.N := List.length_replicate
  rw [hl] at h
  exact lt_of_le_of_lt h (len_lt q i s.N)

omit hQcard in
theorem len_lt_N_succ (i : ℕ) : len q i (stages g q Qf i).N < (stages g q Qf (i + 1)).N := by
  rw [stages_succ, stepSt_N]
  exact Nat.lt_succ_of_le (le_max_right _ _)

omit hQcard in
theorem N_le_succ (i : ℕ) : (stages g q Qf i).N ≤ (stages g q Qf (i + 1)).N :=
  (len_ge q i _).trans (len_lt_N_succ g q Qf i).le

omit hQcard in
theorem N_mono {i j : ℕ} (h : i ≤ j) : (stages g q Qf i).N ≤ (stages g q Qf j).N :=
  monotone_nat_of_le_succ (fun k => N_le_succ g q Qf k) h

omit hQcard in
theorem S_mono {i j : ℕ} (h : i ≤ j) : (stages g q Qf i).S ⊆ (stages g q Qf j).S :=
  monotone_nat_of_le_succ (f := fun n => (stages g q Qf n).S) (fun k => by rw [stages_succ]; exact subset_stepSt_S g q Qf k _) h

/-- A string put in at a later stage is at least as long as any earlier bound, so a short string
of a later stage was already there. -/
theorem back {j k : ℕ} (hjk : j ≤ k) (y : List Bool) (hy : y ∈ (stages g q Qf k).S)
    (hlen : y.length < (stages g q Qf j).N) : y ∈ (stages g q Qf j).S := by
  induction k, hjk using Nat.le_induction with
  | base => exact hy
  | succ k hjk ih =>
    rw [stages_succ] at hy
    rcases mem_stepSt_S g q Qf hy with hy' | ⟨-, rfl⟩
    · exact ih hy'
    · exfalso
      have hl := (pick_spec _ _ (card_lt q Qf hQcard k (stages g q Qf k))).1
      have h1 := len_ge q k (stages g q Qf k).N
      have h2 := N_mono g q Qf hjk
      omega

theorem mem_oracle_short {j : ℕ} (y : List Bool) (hy : y ∈ oracle g q Qf)
    (hlen : y.length < (stages g q Qf j).N) : y ∈ (stages g q Qf j).S := by
  obtain ⟨k, hk⟩ := hy
  rcases le_total j k with hjk | hkj
  · exact back g q Qf hQcard hjk y hk hlen
  · exact S_mono g q Qf hkj hk

/-- Every string of a stage is below its bound. -/
theorem S_lt_N (i : ℕ) : ∀ y ∈ (stages g q Qf i).S, y.length < (stages g q Qf i).N := by
  induction i with
  | zero => intro y hy; simp [stages_zero_S] at hy
  | succ k ih =>
    intro y hy
    have hlt := len_lt_N_succ g q Qf k
    have hge := len_ge q k (stages g q Qf k).N
    rw [stages_succ] at hy
    rcases mem_stepSt_S g q Qf hy with hy' | ⟨-, rfl⟩
    · have := ih y hy'
      omega
    · have := (pick_spec _ _ (card_lt q Qf hQcard k (stages g q Qf k))).1
      omega

end

/-- The diagonal: from deciders with few queries, an oracle defeating each of them on the
length test. -/
theorem diagonal
    (hloc : ∀ (i : ℕ) (A : Language Bool) (x : List Bool), ∃ Q : Finset (List Bool),
      Q.card ≤ (q i).eval x.length ∧ ∀ A' : Language Bool, (∀ y ∈ Q, y ∈ A ↔ y ∈ A') →
        (x ∈ g i A ↔ x ∈ g i A')) :
    ∃ B : Language Bool, ∀ i, g i B ≠ {x : List Bool | ∃ w ∈ B, w.length = x.length} := by
  choose Qf hQcard hQagree using hloc
  refine ⟨oracle g q Qf, fun i heq => ?_⟩
  have hcard := card_lt q Qf hQcard i (stages g q Qf i)
  have hxlen : (xin q i (stages g q Qf i)).length = len q i (stages g q Qf i).N :=
    List.length_replicate
  have hNs := stepSt_N g q Qf i (stages g q Qf i)
  rw [← stages_succ] at hNs
  -- The oracle agrees with stage `i` on every string `g i` depended on.
  have agree : ∀ y ∈ Qf i (asLang (stages g q Qf i)) (xin q i (stages g q Qf i)),
      y ∈ asLang (stages g q Qf i) ↔ y ∈ oracle g q Qf := by
    intro y hyQ
    constructor
    · intro hy; exact ⟨i, hy⟩
    · intro hy
      have hylen : y.length < (stages g q Qf (i + 1)).N := by
        rw [hNs]
        have h0 : y.length ≤ (qset q Qf i (stages g q Qf i)).sup List.length :=
          Finset.le_sup (f := List.length) hyQ
        exact Nat.lt_succ_of_le (le_trans h0 (le_max_left _ _))
      have h1 := mem_oracle_short g q Qf hQcard y hy hylen
      rw [stages_succ] at h1
      rcases mem_stepSt_S g q Qf h1 with h2 | ⟨-, rfl⟩
      · exact h2
      · exact absurd hyQ (pick_spec _ _ hcard).2
  have hg := hQagree i (asLang (stages g q Qf i)) (xin q i (stages g q Qf i)) (oracle g q Qf) agree
  by_cases hx : xin q i (stages g q Qf i) ∈ g i (asLang (stages g q Qf i))
  · -- `g i` says yes, and no string of length `n` is in the oracle.
    have hin : xin q i (stages g q Qf i) ∈ g i (oracle g q Qf) := hg.mp hx
    rw [heq] at hin
    obtain ⟨w, hwB, hwlen⟩ := hin
    rw [hxlen] at hwlen
    have hwN : w.length < (stages g q Qf (i + 1)).N := by
      rw [hwlen]; exact len_lt_N_succ g q Qf i
    have h1 := mem_oracle_short g q Qf hQcard w hwB hwN
    rw [stages_succ] at h1
    rcases mem_stepSt_S g q Qf h1 with h2 | ⟨hnx, -⟩
    · have h3 := S_lt_N g q Qf hQcard i w h2
      have h4 := len_ge q i (stages g q Qf i).N
      omega
    · exact hnx hx
  · -- `g i` says no, and a string of length `n` is in the oracle.
    have hnot : xin q i (stages g q Qf i) ∉ g i (oracle g q Qf) := fun h => hx (hg.mpr h)
    apply hnot
    rw [heq]
    refine ⟨pick (qset q Qf i (stages g q Qf i)) (len q i (stages g q Qf i).N), ⟨i + 1, ?_⟩, ?_⟩
    · rw [stages_succ, stepSt_S]; simp only [hx, ↓reduceIte]
      exact Finset.mem_insert_self _ _
    · rw [hxlen]; exact (pick_spec _ _ hcard).1

end PEqualNP.Library.Helpers.BGS
