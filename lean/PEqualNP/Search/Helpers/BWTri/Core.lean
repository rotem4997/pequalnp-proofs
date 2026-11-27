import PEqualNP.Search.Helpers.BW.Core

/-!
# Helpers: the core of the Beame-Whitmeyer triangle-dag bound (L-lib-105)

The rectangle core of `BW/Core.lean` with triangles in place of rectangles. A node is a set
`T` of pairs of halves of the form `{(x, y) | a x < b y}`. The fold (Algorithm 1) works with
slices `{y ∈ Y | (x, y) ∈ T}`; the counting bound (Lemma 5.6, Algorithm 2) picks a `y` with
the largest label `b y`, so that every `x` with a nonempty slice is paired with it.
-/

namespace PEqualNP.Search.Helpers.BWTri

open Classical
open PEqualNP.Search.Helpers.BW

variable {n t : ℕ}

/-- A relation between halves is a triangle: `R x y ↔ a x < b y`. -/
def TriRel (R : Half n t → Half n t → Prop) : Prop :=
  ∃ a b : Half n t → ℤ, ∀ x y, R x y ↔ a x < b y

theorem triRel_swap {R : Half n t → Half n t → Prop} (h : TriRel R) :
    TriRel (fun y x => R x y) := by
  obtain ⟨a, b, h⟩ := h
  refine ⟨fun y => -b y, fun x => -a x, fun y x => ?_⟩
  show R x y ↔ -b y < -a x
  rw [h]
  constructor <;> intro h' <;> linarith

/-- An abstract triangle dag for bit pigeonhole, newest first. A node is a set of pairs of
halves that is a triangle. A sink is a node on which two different pigeons collide in both
halves; a split node is covered by two earlier nodes. -/
inductive TDag (n t : ℕ) : List (Set (Half n t × Half n t)) → Prop
  | nil : TDag n t []
  | sink {ρ} {T : Set (Half n t × Half n t)} (i j : Fin (n + 1)) :
      TDag n t ρ → TriRel (fun x y => (x, y) ∈ T) → i ≠ j →
      (∀ p ∈ T, p.1 i = p.1 j ∧ p.2 i = p.2 j) → TDag n t (T :: ρ)
  | split {ρ} {T T₁ T₂ : Set (Half n t × Half n t)} :
      TDag n t ρ → TriRel (fun x y => (x, y) ∈ T) → T₁ ∈ ρ → T₂ ∈ ρ → T ⊆ T₁ ∪ T₂ →
      TDag n t (T :: ρ)

/-- An abstract triangle dag that has the whole space as a node. -/
def TDagFor (n t : ℕ) (σ : List (Set (Half n t × Half n t))) : Prop :=
  TDag n t σ ∧ (Set.univ : Set (Half n t × Half n t)) ∈ σ

/-! ## L5 for triangles: the counting bound (Lemma 5.6) -/

/-- The points of `A` satisfying `E` that cannot cover their slice of `B` with fewer than
`k - |E|` of their colliding pairs. -/
noncomputable def TBad (k : ℕ) (A B : Set (Half n t)) (R : Half n t → Half n t → Prop)
    (E : List (Edge n)) : Finset (Half n t) :=
  Finset.univ.filter fun x => x ∈ A ∧ Sat E x ∧
    ∀ S ⊆ Coll x, S.card + E.length < k → ¬ ∀ y ∈ B, R x y → ∃ p ∈ S, y p.1 = y p.2

theorem mem_tbad {k : ℕ} {A B : Set (Half n t)} {R : Half n t → Half n t → Prop}
    {E : List (Edge n)} {x : Half n t} :
    x ∈ TBad k A B R E ↔ x ∈ A ∧ Sat E x ∧
      ∀ S ⊆ Coll x, S.card + E.length < k → ¬ ∀ y ∈ B, R x y → ∃ p ∈ S, y p.1 = y p.2 := by
  simp [TBad]

theorem tbad_child {k : ℕ} {A B : Set (Half n t)} {R : Half n t → Half n t → Prop}
    {E : List (Edge n)} {x : Half n t}
    (hx : x ∈ TBad k A B R E) {p : Edge n} (hp : p.1 ≠ p.2) (hxp : x p.1 = x p.2) :
    x ∈ TBad k A {z | z ∈ B ∧ z p.1 ≠ z p.2} R (p :: E) := by
  rw [mem_tbad] at hx ⊢
  obtain ⟨hA, hS, hc⟩ := hx
  refine ⟨hA, ?_, ?_⟩
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hxp
    · exact hS q hq
  · intro S hSc hcard hcov
    apply hc (insert p S) (Finset.insert_subset (mem_coll.2 ⟨hp, hxp⟩) hSc)
    · have := Finset.card_insert_le p S
      simp only [List.length_cons] at hcard
      omega
    · intro z hz hR
      by_cases hzp : z p.1 = z p.2
      · exact ⟨p, Finset.mem_insert_self _ _, hzp⟩
      · obtain ⟨q, hq, e⟩ := hcov z ⟨hz, hzp⟩ hR
        exact ⟨q, Finset.mem_insert_of_mem hq, e⟩

/-- Proposition 5.1: in a nonempty `B'`, some `y` is paired with every `x` that is paired with
some point of `B'`. -/
theorem exists_top {R : Half n t → Half n t → Prop} (hR : TriRel R) {B' : Set (Half n t)}
    (hne : ∃ y, y ∈ B') : ∃ y ∈ B', ∀ x, ∀ y' ∈ B', R x y' → R x y := by
  obtain ⟨a, b, hab⟩ := hR
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun z => z ∈ B') b
    ⟨y0, by simpa using hy0⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hmax
  refine ⟨y, hy, fun x y' hy' hxy' => ?_⟩
  rw [hab] at hxy' ⊢
  exact lt_of_lt_of_le hxy' (hmax y' hy')

theorem tbad_bound (k r0 : ℕ) (hk : 4 * k ≤ 2 ^ t) (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r)
    (A B : Set (Half n t)) (R : Half n t → Half n t → Prop) (hR : TriRel R)
    (hB : ∀ y ∈ B, CovLE {x | x ∈ A ∧ R x y} y (2 * k)) :
    ∀ m (E : List (Edge n)) (B' : Set (Half n t)), B' ⊆ B → k - E.length = m →
      E.length ≤ k → E.Nodup → (∀ p ∈ E, p.1 ≠ p.2) → (∀ y ∈ B', ∀ p ∈ E, y p.1 ≠ y p.2) →
      (TBad k A B' R E).card * (2 * k) ^ rank E * 2 ^ r0 ≤ Fintype.card (Half n t) := by
  intro m
  induction m with
  | zero =>
    intro E B' _ hm hle hnd hne _
    have hlen : E.length = k := by omega
    have hrk : r0 ≤ rank E := hr _ (hlen ▸ rank_bound E hnd hne)
    have hsub : TBad k A B' R E ⊆ Finset.univ.filter fun x : Half n t => Sat E x := by
      intro x hx
      rw [mem_tbad] at hx
      simpa using hx.2.1
    have h1 := Finset.card_le_card hsub
    have h2 := eqd_rank (t := t) E
    have h3 : (2 * k) ^ rank E * 2 ^ r0 ≤ (2 ^ t) ^ rank E := by
      calc (2 * k) ^ rank E * 2 ^ r0 ≤ (2 * k) ^ rank E * 2 ^ rank E :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hrk)
        _ = (2 * k * 2) ^ rank E := (mul_pow _ _ _).symm
        _ ≤ (2 ^ t) ^ rank E := Nat.pow_le_pow_left (by omega) _
    calc (TBad k A B' R E).card * (2 * k) ^ rank E * 2 ^ r0
        = (TBad k A B' R E).card * ((2 * k) ^ rank E * 2 ^ r0) := by ring
      _ ≤ _ * (2 ^ t) ^ rank E := Nat.mul_le_mul h1 h3
      _ ≤ _ := h2
  | succ m ih =>
    intro E B' hB' hm hle hnd hne hdiff
    have hlt : E.length < k := by omega
    by_cases hy : ∃ y, y ∈ B'
    · obtain ⟨y, hyB, htop⟩ := exists_top hR hy
      obtain ⟨P, hPc, hPcard, hPcov⟩ := hB y (hB' hyB)
      have hPne : ∀ p ∈ P, p.1 ≠ p.2 := fun p hp => (mem_coll.1 (hPc hp)).1
      have hPE : ∀ p ∈ P, p ∉ E := fun p hp hpE =>
        hdiff y hyB p hpE (mem_coll.1 (hPc hp)).2
      have hchild : ∀ p ∈ P, (TBad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} R (p :: E)).card *
          (2 * k) ^ rank (p :: E) * 2 ^ r0 ≤ Fintype.card (Half n t) := by
        intro p hp
        apply ih (p :: E) {z | z ∈ B' ∧ z p.1 ≠ z p.2} (fun z hz => hB' hz.1)
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega
        · exact List.nodup_cons.2 ⟨hPE p hp, hnd⟩
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hPne _ hp
          · exact hne q hq
        · intro z hz q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hz.2
          · exact hdiff z hz.1 q hq
      have hin : ∀ x ∈ TBad k A B' R E, ∃ p ∈ P, x p.1 = x p.2 := by
        intro x hx
        rw [mem_tbad] at hx
        have hxy : R x y := by
          by_contra hxy
          exact hx.2.2 ∅ (Finset.empty_subset _) (by simpa using hlt)
            (fun z hz hRz => absurd (htop x z hz hRz) hxy)
        exact hPcov x ⟨hx.1, hxy⟩
      by_cases himp : ∃ p ∈ P, Implied E p
      · obtain ⟨p, hp, hpi⟩ := himp
        have hsub : TBad k A B' R E ⊆ TBad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} R (p :: E) := by
          intro x hx
          have hsat : Sat E x := (mem_tbad.1 hx).2.1
          exact tbad_child hx (hPne p hp) (sat_implied hsat hpi)
        have hrk : rank (p :: E) = rank E := by simp [rank, hpi]
        have h0 := hchild p hp
        rw [hrk] at h0
        refine le_trans ?_ h0
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Finset.card_le_card hsub))
      · push Not at himp
        have hsub : TBad k A B' R E ⊆
            P.biUnion fun p => TBad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} R (p :: E) := by
          intro x hx
          obtain ⟨p, hp, hxp⟩ := hin x hx
          exact Finset.mem_biUnion.2 ⟨p, hp, tbad_child hx (hPne p hp) hxp⟩
        have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        have hrk : ∀ p ∈ P, rank (p :: E) = rank E + 1 := fun p hp => by
          simp [rank, himp p hp]
        have h2 : (TBad k A B' R E).card * (2 * k) ^ (rank E + 1) * 2 ^ r0 ≤
            P.card * Fintype.card (Half n t) := by
          calc (TBad k A B' R E).card * (2 * k) ^ (rank E + 1) * 2 ^ r0
              = (TBad k A B' R E).card * ((2 * k) ^ (rank E + 1) * 2 ^ r0) := by ring
            _ ≤ (∑ p ∈ P, (TBad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} R (p :: E)).card) *
                ((2 * k) ^ (rank E + 1) * 2 ^ r0) := Nat.mul_le_mul_right _ h1
            _ = ∑ p ∈ P, (TBad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} R (p :: E)).card *
                (2 * k) ^ rank (p :: E) * 2 ^ r0 := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun p hp => ?_
                rw [hrk p hp]; ring
            _ ≤ ∑ p ∈ P, Fintype.card (Half n t) := Finset.sum_le_sum hchild
            _ = P.card * Fintype.card (Half n t) := by rw [Finset.sum_const, smul_eq_mul]
        have hkpos : 0 < 2 * k := by omega
        refine Nat.le_of_mul_le_mul_right ?_ hkpos
        calc (TBad k A B' R E).card * (2 * k) ^ rank E * 2 ^ r0 * (2 * k)
            = (TBad k A B' R E).card * (2 * k) ^ (rank E + 1) * 2 ^ r0 := by ring
          _ ≤ P.card * Fintype.card (Half n t) := h2
          _ ≤ (2 * k) * Fintype.card (Half n t) := Nat.mul_le_mul_right _ hPcard
          _ = Fintype.card (Half n t) * (2 * k) := by ring
    · push Not at hy
      have hemp : TBad k A B' R E = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        rw [mem_tbad] at hx
        exact hx.2.2 ∅ (Finset.empty_subset _) (by simpa using hlt)
          (fun z hz => absurd hz (hy z))
      simp [hemp]

/-- L5 for triangles: if every `y ∈ B` covers its slice of `A` with at most `2 k` pairs, few
`x ∈ A` fail to cover their slice of `B` with fewer than `k` pairs. -/
theorem tcore (k r0 : ℕ) (hk : 4 * k ≤ 2 ^ t) (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r)
    (A B : Set (Half n t)) (R : Half n t → Half n t → Prop) (hR : TriRel R)
    (hB : ∀ y ∈ B, CovLE {x | x ∈ A ∧ R x y} y (2 * k)) :
    (Finset.univ.filter fun x : Half n t =>
      x ∈ A ∧ ¬ CovLE {y | y ∈ B ∧ R x y} x (k - 1)).card * 2 ^ r0 ≤
      Fintype.card (Half n t) := by
  have h := tbad_bound k r0 hk hr A B R hR hB k [] B subset_rfl (by simp) (by simp)
    List.nodup_nil (by simp) (by simp)
  have hsub : (Finset.univ.filter fun x : Half n t =>
      x ∈ A ∧ ¬ CovLE {y | y ∈ B ∧ R x y} x (k - 1)) ⊆ TBad k A B R [] := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [mem_tbad]
    refine ⟨hx.1, fun p hp => by simp at hp, ?_⟩
    intro S hS hc hcov
    exact hx.2 ⟨S, hS, by simp at hc; omega, fun y hy => hcov y hy.1 hy.2⟩
  simp only [rank, pow_zero, mul_one] at h
  exact (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)).trans h

/-! ## L6 for triangles: the fold (Algorithm 1) with slices -/

/-- The surviving x-points after processing the node `T` at state `st`. -/
def tstepX (k : ℕ) (T : Set (Half n t × Half n t)) (st : St n t) : Set (Half n t) :=
  {x | x ∈ st.1 ∧ CovLE {y | y ∈ st.2 ∧ (x, y) ∈ T} x (k - 1)}

/-- Processing the node `T` at state `st`. -/
def tstep (k : ℕ) (T : Set (Half n t × Half n t)) (st : St n t) : St n t :=
  (tstepX k T st, {y | y ∈ st.2 ∧ CovLE {x | x ∈ tstepX k T st ∧ (x, y) ∈ T} y (k - 1)})

/-- Processing a newest-first list of nodes from oldest to newest. -/
def trun (k : ℕ) (σ : List (Set (Half n t × Half n t))) : St n t :=
  σ.foldr (tstep k) (Set.univ, Set.univ)

/-- The invariant of the fold. -/
def TInv (k : ℕ) (ρ : List (Set (Half n t × Half n t))) (st : St n t) : Prop :=
  ∀ T ∈ ρ, (∀ x ∈ st.1, CovLE {y | y ∈ st.2 ∧ (x, y) ∈ T} x (k - 1)) ∧
    (∀ y ∈ st.2, CovLE {x | x ∈ st.1 ∧ (x, y) ∈ T} y (k - 1))

theorem tinv_run (k : ℕ) : ∀ ρ : List (Set (Half n t × Half n t)), TInv k ρ (trun k ρ)
  | [] => fun _ h => absurd h (List.not_mem_nil)
  | T :: ρ => by
    have ih := tinv_run k ρ
    have hrun : trun k (T :: ρ) = tstep k T (trun k ρ) := rfl
    rw [hrun]
    have h1 : (tstep k T (trun k ρ)).1 ⊆ (trun k ρ).1 := fun x hx => hx.1
    have h2 : (tstep k T (trun k ρ)).2 ⊆ (trun k ρ).2 := fun y hy => hy.1
    intro T' hT'
    rcases List.mem_cons.1 hT' with rfl | hT'
    · refine ⟨fun x hx => ?_, fun y hy => hy.2⟩
      refine covLE_mono ?_ le_rfl hx.2
      intro y hy
      exact ⟨h2 hy.1, hy.2⟩
    · refine ⟨fun x hx => ?_, fun y hy => ?_⟩
      · refine covLE_mono ?_ le_rfl ((ih T' hT').1 x (h1 hx))
        intro y hy
        exact ⟨h2 hy.1, hy.2⟩
      · refine covLE_mono ?_ le_rfl ((ih T' hT').2 y (h2 hy))
        intro x hx
        exact ⟨h1 hx.1, hx.2⟩

/-! ## L8 per node for triangles -/

theorem tnode_bound (k r0 : ℕ) (hk : 4 * k ≤ 2 ^ t) (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r)
    (T : Set (Half n t × Half n t)) (hT : TriRel (fun x y => (x, y) ∈ T)) (st : St n t)
    (hy : ∀ y ∈ st.2, CovLE {x | x ∈ st.1 ∧ (x, y) ∈ T} y (2 * k)) :
    cnt st.1 * 2 ^ r0 ≤ cnt (tstep k T st).1 * 2 ^ r0 + Fintype.card (Half n t) ∧
    cnt st.2 * 2 ^ r0 ≤ cnt (tstep k T st).2 * 2 ^ r0 + Fintype.card (Half n t) := by
  constructor
  · have hc := tcore k r0 hk hr st.1 st.2 (fun x y => (x, y) ∈ T) hT hy
    have hsub : (Finset.univ.filter fun x => x ∈ st.1) ⊆
        (Finset.univ.filter fun x => x ∈ (tstep k T st).1) ∪
        (Finset.univ.filter fun x : Half n t =>
          x ∈ st.1 ∧ ¬ CovLE {y | y ∈ st.2 ∧ (x, y) ∈ T} x (k - 1)) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
      by_cases h : CovLE {y | y ∈ st.2 ∧ (x, y) ∈ T} x (k - 1)
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    have h0 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    unfold cnt
    calc _ ≤ ((Finset.univ.filter fun x => x ∈ (tstep k T st).1).card +
          (Finset.univ.filter fun x : Half n t =>
            x ∈ st.1 ∧ ¬ CovLE {y | y ∈ st.2 ∧ (x, y) ∈ T} x (k - 1)).card) * 2 ^ r0 :=
          Nat.mul_le_mul_right _ h0
      _ = _ := add_mul _ _ _
      _ ≤ _ := by convert Nat.add_le_add_left hc _
  · have hx : ∀ x ∈ (tstep k T st).1, CovLE {y | y ∈ st.2 ∧ (x, y) ∈ T} x (2 * k) :=
      fun x hx => covLE_mono subset_rfl (by omega) hx.2
    have hc := tcore k r0 hk hr st.2 (tstep k T st).1 (fun y x => (x, y) ∈ T)
      (triRel_swap hT) hx
    have hsub : (Finset.univ.filter fun y => y ∈ st.2) ⊆
        (Finset.univ.filter fun y => y ∈ (tstep k T st).2) ∪
        (Finset.univ.filter fun y : Half n t =>
          y ∈ st.2 ∧ ¬ CovLE {x | x ∈ (tstep k T st).1 ∧ (x, y) ∈ T} y (k - 1)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
      by_cases h : CovLE {x | x ∈ (tstep k T st).1 ∧ (x, y) ∈ T} y (k - 1)
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    have h0 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    unfold cnt
    calc _ ≤ ((Finset.univ.filter fun y => y ∈ (tstep k T st).2).card +
          (Finset.univ.filter fun y : Half n t =>
            y ∈ st.2 ∧ ¬ CovLE {x | x ∈ (tstep k T st).1 ∧ (x, y) ∈ T} y (k - 1)).card) *
            2 ^ r0 :=
          Nat.mul_le_mul_right _ h0
      _ = _ := add_mul _ _ _
      _ ≤ _ := by convert Nat.add_le_add_left hc _

/-! ## L8 total for triangles -/

theorem ttotal (k r0 : ℕ) (hk1 : 0 < k) (hk : 4 * k ≤ 2 ^ t)
    (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r) {ρ : List (Set (Half n t × Half n t))}
    (h : TDag n t ρ) :
    Fintype.card (Half n t) * 2 ^ r0 ≤
        cnt (trun k ρ).1 * 2 ^ r0 + ρ.length * Fintype.card (Half n t) ∧
      Fintype.card (Half n t) * 2 ^ r0 ≤
        cnt (trun k ρ).2 * 2 ^ r0 + ρ.length * Fintype.card (Half n t) := by
  induction h with
  | nil =>
    have hu : cnt (Set.univ : Set (Half n t)) = Fintype.card (Half n t) := by
      simp [cnt]
    have hr0 : trun k ([] : List (Set (Half n t × Half n t))) = (Set.univ, Set.univ) := rfl
    rw [hr0]
    simp [hu]
  | @sink ρ T i j hρ hT hij hsk ih =>
    have hy : ∀ y ∈ (trun k ρ).2, CovLE {x | x ∈ (trun k ρ).1 ∧ (x, y) ∈ T} y (2 * k) := by
      intro y _
      by_cases hyij : y i = y j
      · refine ⟨{(i, j)}, ?_, ?_, ?_⟩
        · rw [Finset.singleton_subset_iff, mem_coll]; exact ⟨hij, hyij⟩
        · rw [Finset.card_singleton]; omega
        · intro x hx; exact ⟨(i, j), Finset.mem_singleton_self _, (hsk _ hx.2).1⟩
      · exact ⟨∅, Finset.empty_subset _, Nat.zero_le _,
          fun x hx => absurd (hsk _ hx.2).2 hyij⟩
    obtain ⟨h1, h2⟩ := tnode_bound k r0 hk hr T hT (trun k ρ) hy
    obtain ⟨ih1, ih2⟩ := ih
    have hrun : trun k (T :: ρ) = tstep k T (trun k ρ) := rfl
    rw [hrun, List.length_cons]
    constructor <;> nlinarith
  | @split ρ T T₁ T₂ hρ hT hm₁ hm₂ hsub ih =>
    have hinv := tinv_run k ρ
    have hy : ∀ y ∈ (trun k ρ).2, CovLE {x | x ∈ (trun k ρ).1 ∧ (x, y) ∈ T} y (2 * k) := by
      intro y hy
      refine covLE_mono subset_rfl (by omega)
        (covLE_union ?_ ((hinv _ hm₁).2 y hy) ((hinv _ hm₂).2 y hy))
      intro x hx
      rcases hsub hx.2 with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨hx.1, h⟩
    obtain ⟨h1, h2⟩ := tnode_bound k r0 hk hr T hT (trun k ρ) hy
    obtain ⟨ih1, ih2⟩ := ih
    have hrun : trun k (T :: ρ) = tstep k T (trun k ρ) := rfl
    rw [hrun, List.length_cons]
    constructor <;> nlinarith

/-! ## L7 for triangles: the root -/

theorem troot (k : ℕ) (σ : List (Set (Half n t × Half n t)))
    (hroot : (Set.univ : Set (Half n t × Half n t)) ∈ σ) :
    cnt (trun k σ).1 = 0 ∨ cnt (trun k σ).2 * 2 ^ t ≤ (k - 1) * Fintype.card (Half n t) := by
  by_cases hx : ∃ x, x ∈ (trun k σ).1
  · right
    obtain ⟨x, hx⟩ := hx
    obtain ⟨S, hS, hcard, hcov⟩ := (tinv_run k σ _ hroot).1 x hx
    have hsub : (Finset.univ.filter fun y => y ∈ (trun k σ).2) ⊆
        S.biUnion fun p => Finset.univ.filter fun y : Half n t => y p.1 = y p.2 := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨p, hp, e⟩ := hcov y ⟨hy, trivial⟩
      exact Finset.mem_biUnion.2 ⟨p, hp, by simp [e]⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    unfold cnt
    calc _ ≤ (∑ p ∈ S, (Finset.univ.filter fun y : Half n t => y p.1 = y p.2).card) * 2 ^ t :=
          Nat.mul_le_mul_right _ h1
      _ = ∑ p ∈ S, Fintype.card (Half n t) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p hp => eqd_pair p.1 p.2 (mem_coll.1 (hS hp)).1
      _ = S.card * Fintype.card (Half n t) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hcard
  · left
    push Not at hx
    simp [cnt, hx]

/-! ## The generic lower bound for triangles -/

theorem tlower (k r0 : ℕ) (hk1 : 0 < k) (hk : 4 * k = 2 ^ t) (hr0 : 1 ≤ r0)
    (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r) (σ : List (Set (Half n t × Half n t)))
    (h : TDagFor n t σ) : 2 ^ (r0 - 1) ≤ σ.length := by
  obtain ⟨h1, h2⟩ := ttotal k r0 hk1 hk.le hr h.1
  have hN : 0 < Fintype.card (Half n t) := Fintype.card_pos
  have hP : 2 ^ r0 = 2 * 2 ^ (r0 - 1) := by
    rw [← pow_succ']; congr 1; omega
  set N := Fintype.card (Half n t)
  set L := σ.length
  set P := 2 ^ r0
  set Q := 2 ^ (r0 - 1)
  rcases troot k σ h.2 with hX | hY
  · rw [hX, zero_mul, zero_add, mul_comm L] at h1
    have := Nat.le_of_mul_le_mul_left h1 hN
    omega
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hY
    rw [← hk] at hY
    set c := cnt (trun (k' + 1) σ).2
    have e1 : N * (4 * (k' + 1) * P) ≤ N * (k' * P + 4 * (k' + 1) * L) := by
      calc N * (4 * (k' + 1) * P) = 4 * (k' + 1) * (N * P) := by ring
        _ ≤ 4 * (k' + 1) * (c * P + L * N) := Nat.mul_le_mul_left _ h2
        _ = c * (4 * (k' + 1)) * P + N * (4 * (k' + 1) * L) := by ring
        _ ≤ k' * N * P + N * (4 * (k' + 1) * L) :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ hY) _
        _ = N * (k' * P + 4 * (k' + 1) * L) := by ring
    have e2 := Nat.le_of_mul_le_mul_left e1 hN
    have e3 : (k' + 1) * (3 * P) ≤ (k' + 1) * (4 * L) := by nlinarith
    have e4 := Nat.le_of_mul_le_mul_left e3 (Nat.succ_pos k')
    omega

/-- CORE: every abstract triangle dag for bit pigeonhole with `n = 16 ^ (s + 1)` and
`t = 2 s + 2` has at least `2 ^ (2 ^ (s - 1) - 1)` nodes. -/
theorem tdag_lower' (s : ℕ) (σ : List (Set (Half (16 ^ (s + 1)) (2 * s + 2) ×
    Half (16 ^ (s + 1)) (2 * s + 2)))) (h : TDagFor (16 ^ (s + 1)) (2 * s + 2) σ) :
    2 ^ (2 ^ (s - 1) - 1) ≤ σ.length := by
  rcases s with _ | s
  · simp only [Nat.zero_sub, pow_zero, Nat.sub_self]; exact List.length_pos_of_mem h.2
  · have hk : 4 * 4 ^ (s + 1) = 2 ^ (2 * (s + 1) + 2) := by
      rw [show 2 * (s + 1) + 2 = 2 * (s + 2) by ring, pow_mul]
      norm_num [pow_succ]
      ring
    have hr : ∀ r, 4 ^ (s + 1) ≤ 4 * r ^ 2 → 2 ^ s ≤ r := by
      intro r hr'
      have h4 : (2 ^ s) ^ 2 ≤ r ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
        rw [pow_succ] at hr'
        omega
      by_contra hlt
      push Not at hlt
      have := Nat.pow_lt_pow_left hlt (two_ne_zero)
      omega
    have := tlower (4 ^ (s + 1)) (2 ^ s) (by positivity) hk Nat.one_le_two_pow hr σ h
    rw [Nat.add_sub_cancel]
    exact this

end PEqualNP.Search.Helpers.BWTri
