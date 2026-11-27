import PEqualNP.Search.Helpers.BW.Count

/-!
# Helpers: the core of the Beame-Whitmeyer rectangle-dag bound (L2, L5 to L8)

Uses only the four stubs `eqd_rank`, `eqd_pair`, `rank_bound` (and the definitions).
-/

namespace PEqualNP.Search.Helpers.BW

open Classical

variable {n t : ℕ}

/-! ## L2: covering basics -/

theorem covLE_mono {B B' : Set (Half n t)} {x : Half n t} {d d' : ℕ} (hB : B' ⊆ B)
    (hd : d ≤ d') (h : CovLE B x d) : CovLE B' x d' := by
  obtain ⟨S, hS, hc, hy⟩ := h
  exact ⟨S, hS, hc.trans hd, fun y hy' => hy y (hB hy')⟩

theorem covLE_union {B B₁ B₂ : Set (Half n t)} {x : Half n t} {d₁ d₂ : ℕ}
    (hB : B ⊆ B₁ ∪ B₂) (h₁ : CovLE B₁ x d₁) (h₂ : CovLE B₂ x d₂) : CovLE B x (d₁ + d₂) := by
  obtain ⟨S₁, hS₁, hc₁, hy₁⟩ := h₁
  obtain ⟨S₂, hS₂, hc₂, hy₂⟩ := h₂
  refine ⟨S₁ ∪ S₂, Finset.union_subset hS₁ hS₂,
    (Finset.card_union_le _ _).trans (Nat.add_le_add hc₁ hc₂), ?_⟩
  intro y hy
  rcases hB hy with h | h
  · obtain ⟨p, hp, e⟩ := hy₁ y h
    exact ⟨p, Finset.mem_union_left _ hp, e⟩
  · obtain ⟨p, hp, e⟩ := hy₂ y h
    exact ⟨p, Finset.mem_union_right _ hp, e⟩

theorem covLE_cond {C : Set (Half n t)} {y : Half n t} {d : ℕ} {P : Prop}
    (h : P → CovLE C y d) : CovLE {x | x ∈ C ∧ P} y d := by
  by_cases hP : P
  · exact covLE_mono (fun x hx => hx.1) le_rfl (h hP)
  · exact ⟨∅, Finset.empty_subset _, Nat.zero_le _, fun z hz => absurd hz.2 hP⟩

theorem mem_coll {x : Half n t} {p : Edge n} : p ∈ Coll x ↔ p.1 ≠ p.2 ∧ x p.1 = x p.2 := by
  simp [Coll]

theorem core_sat_eqvGen {E : List (Edge n)} {x : Half n t} (hx : Sat E x) :
    ∀ a b, Relation.EqvGen (fun a b => (a, b) ∈ E) a b → x a = x b := by
  intro a b h
  induction h with
  | rel a b h => exact hx (a, b) h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem sat_implied {E : List (Edge n)} {x : Half n t} (hx : Sat E x) {p : Edge n}
    (hp : Implied E p) : x p.1 = x p.2 :=
  core_sat_eqvGen hx p.1 p.2 hp

/-! ## L5: the core counting bound -/

/-- The points of `A` satisfying `E` that cannot cover `B` with fewer than `k - |E|` of their
colliding pairs. -/
noncomputable def Bad (k : ℕ) (A B : Set (Half n t)) (E : List (Edge n)) : Finset (Half n t) :=
  Finset.univ.filter fun x => x ∈ A ∧ Sat E x ∧
    ∀ S ⊆ Coll x, S.card + E.length < k → ¬ ∀ y ∈ B, ∃ p ∈ S, y p.1 = y p.2

theorem mem_bad {k : ℕ} {A B : Set (Half n t)} {E : List (Edge n)} {x : Half n t} :
    x ∈ Bad k A B E ↔ x ∈ A ∧ Sat E x ∧
      ∀ S ⊆ Coll x, S.card + E.length < k → ¬ ∀ y ∈ B, ∃ p ∈ S, y p.1 = y p.2 := by
  simp [Bad]

theorem bad_child {k : ℕ} {A B : Set (Half n t)} {E : List (Edge n)} {x : Half n t}
    (hx : x ∈ Bad k A B E) {p : Edge n} (hp : p.1 ≠ p.2) (hxp : x p.1 = x p.2) :
    x ∈ Bad k A {z | z ∈ B ∧ z p.1 ≠ z p.2} (p :: E) := by
  rw [mem_bad] at hx ⊢
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
    · intro z hz
      by_cases hzp : z p.1 = z p.2
      · exact ⟨p, Finset.mem_insert_self _ _, hzp⟩
      · obtain ⟨q, hq, e⟩ := hcov z ⟨hz, hzp⟩
        exact ⟨q, Finset.mem_insert_of_mem hq, e⟩

theorem bad_bound (k r0 : ℕ) (hk : 4 * k ≤ 2 ^ t) (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r)
    (A B : Set (Half n t)) (hB : ∀ y ∈ B, CovLE A y (2 * k)) :
    ∀ m (E : List (Edge n)) (B' : Set (Half n t)), B' ⊆ B → k - E.length = m →
      E.length ≤ k → E.Nodup → (∀ p ∈ E, p.1 ≠ p.2) → (∀ y ∈ B', ∀ p ∈ E, y p.1 ≠ y p.2) →
      (Bad k A B' E).card * (2 * k) ^ rank E * 2 ^ r0 ≤ Fintype.card (Half n t) := by
  intro m
  induction m with
  | zero =>
    intro E B' _ hm hle hnd hne _
    have hlen : E.length = k := by omega
    have hrk : r0 ≤ rank E := hr _ (hlen ▸ rank_bound E hnd hne)
    have hsub : Bad k A B' E ⊆ Finset.univ.filter fun x : Half n t => Sat E x := by
      intro x hx
      rw [mem_bad] at hx
      simpa using hx.2.1
    have h1 := Finset.card_le_card hsub
    have h2 := eqd_rank (t := t) E
    have h3 : (2 * k) ^ rank E * 2 ^ r0 ≤ (2 ^ t) ^ rank E := by
      calc (2 * k) ^ rank E * 2 ^ r0 ≤ (2 * k) ^ rank E * 2 ^ rank E :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hrk)
        _ = (2 * k * 2) ^ rank E := (mul_pow _ _ _).symm
        _ ≤ (2 ^ t) ^ rank E := Nat.pow_le_pow_left (by omega) _
    calc (Bad k A B' E).card * (2 * k) ^ rank E * 2 ^ r0
        = (Bad k A B' E).card * ((2 * k) ^ rank E * 2 ^ r0) := by ring
      _ ≤ _ * (2 ^ t) ^ rank E := Nat.mul_le_mul h1 h3
      _ ≤ _ := h2
  | succ m ih =>
    intro E B' hB' hm hle hnd hne hdiff
    have hlt : E.length < k := by omega
    by_cases hy : ∃ y, y ∈ B'
    · obtain ⟨y, hyB⟩ := hy
      obtain ⟨P, hPc, hPcard, hPcov⟩ := hB y (hB' hyB)
      have hPne : ∀ p ∈ P, p.1 ≠ p.2 := fun p hp => (mem_coll.1 (hPc hp)).1
      have hPE : ∀ p ∈ P, p ∉ E := fun p hp hpE =>
        hdiff y hyB p hpE (mem_coll.1 (hPc hp)).2
      have hchild : ∀ p ∈ P, (Bad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} (p :: E)).card *
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
      have hin : ∀ x ∈ Bad k A B' E, ∃ p ∈ P, x p.1 = x p.2 := by
        intro x hx
        rw [mem_bad] at hx
        exact hPcov x hx.1
      by_cases himp : ∃ p ∈ P, Implied E p
      · obtain ⟨p, hp, hpi⟩ := himp
        have hsub : Bad k A B' E ⊆ Bad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} (p :: E) := by
          intro x hx
          have hsat : Sat E x := (mem_bad.1 hx).2.1
          exact bad_child hx (hPne p hp) (sat_implied hsat hpi)
        have hrk : rank (p :: E) = rank E := by simp [rank, hpi]
        have h0 := hchild p hp
        rw [hrk] at h0
        refine le_trans ?_ h0
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Finset.card_le_card hsub))
      · push Not at himp
        have hsub : Bad k A B' E ⊆
            P.biUnion fun p => Bad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} (p :: E) := by
          intro x hx
          obtain ⟨p, hp, hxp⟩ := hin x hx
          exact Finset.mem_biUnion.2 ⟨p, hp, bad_child hx (hPne p hp) hxp⟩
        have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
        have hrk : ∀ p ∈ P, rank (p :: E) = rank E + 1 := fun p hp => by
          simp [rank, himp p hp]
        have h2 : (Bad k A B' E).card * (2 * k) ^ (rank E + 1) * 2 ^ r0 ≤
            P.card * Fintype.card (Half n t) := by
          calc (Bad k A B' E).card * (2 * k) ^ (rank E + 1) * 2 ^ r0
              = (Bad k A B' E).card * ((2 * k) ^ (rank E + 1) * 2 ^ r0) := by ring
            _ ≤ (∑ p ∈ P, (Bad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} (p :: E)).card) *
                ((2 * k) ^ (rank E + 1) * 2 ^ r0) := Nat.mul_le_mul_right _ h1
            _ = ∑ p ∈ P, (Bad k A {z | z ∈ B' ∧ z p.1 ≠ z p.2} (p :: E)).card *
                (2 * k) ^ rank (p :: E) * 2 ^ r0 := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun p hp => ?_
                rw [hrk p hp]; ring
            _ ≤ ∑ p ∈ P, Fintype.card (Half n t) := Finset.sum_le_sum hchild
            _ = P.card * Fintype.card (Half n t) := by rw [Finset.sum_const, smul_eq_mul]
        have hkpos : 0 < 2 * k := by omega
        refine Nat.le_of_mul_le_mul_right ?_ hkpos
        calc (Bad k A B' E).card * (2 * k) ^ rank E * 2 ^ r0 * (2 * k)
            = (Bad k A B' E).card * (2 * k) ^ (rank E + 1) * 2 ^ r0 := by ring
          _ ≤ P.card * Fintype.card (Half n t) := h2
          _ ≤ (2 * k) * Fintype.card (Half n t) := Nat.mul_le_mul_right _ hPcard
          _ = Fintype.card (Half n t) * (2 * k) := by ring
    · push Not at hy
      have hemp : Bad k A B' E = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        rw [mem_bad] at hx
        exact hx.2.2 ∅ (Finset.empty_subset _) (by simpa using hlt)
          (fun z hz => absurd hz (hy z))
      simp [hemp]

/-- L5: if every `y ∈ B` covers `A` with at most `2 k` pairs, few `x ∈ A` fail to cover `B`
with fewer than `k` pairs. -/
theorem core (k r0 : ℕ) (hk : 4 * k ≤ 2 ^ t) (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r)
    (A B : Set (Half n t)) (hB : ∀ y ∈ B, CovLE A y (2 * k)) :
    (Finset.univ.filter fun x : Half n t => x ∈ A ∧ ¬ CovLE B x (k - 1)).card * 2 ^ r0 ≤
      Fintype.card (Half n t) := by
  have h := bad_bound k r0 hk hr A B hB k [] B subset_rfl (by simp) (by simp) List.nodup_nil
    (by simp) (by simp)
  have hsub : (Finset.univ.filter fun x : Half n t => x ∈ A ∧ ¬ CovLE B x (k - 1)) ⊆
      Bad k A B [] := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [mem_bad]
    refine ⟨hx.1, fun p hp => by simp at hp, ?_⟩
    intro S hS hc hcov
    exact hx.2 ⟨S, hS, by simp at hc; omega, hcov⟩
  simp only [rank, pow_zero, mul_one] at h
  exact (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)).trans h

/-! ## L6: the fold (Algorithm 1) -/

/-- A state of the fold: the surviving points of each player. -/
abbrev St (n t : ℕ) : Type := Set (Half n t) × Set (Half n t)

/-- The surviving x-points after processing the node `AB` at state `st`. -/
def stepX (k : ℕ) (AB st : St n t) : Set (Half n t) :=
  {x | x ∈ st.1 ∧ (x ∈ AB.1 → CovLE (AB.2 ∩ st.2) x (k - 1))}

/-- Processing the node `AB` at state `st`. -/
def step (k : ℕ) (AB st : St n t) : St n t :=
  (stepX k AB st, {y | y ∈ st.2 ∧ (y ∈ AB.2 → CovLE (AB.1 ∩ stepX k AB st) y (k - 1))})

/-- Processing a newest-first list of nodes from oldest to newest. -/
def run (k : ℕ) (σ : List (St n t)) : St n t :=
  σ.foldr (step k) (Set.univ, Set.univ)

theorem mem_step1 {k : ℕ} {AB st : St n t} {x : Half n t} :
    x ∈ (step k AB st).1 ↔ x ∈ st.1 ∧ (x ∈ AB.1 → CovLE (AB.2 ∩ st.2) x (k - 1)) := Iff.rfl

theorem mem_step2 {k : ℕ} {AB st : St n t} {y : Half n t} :
    y ∈ (step k AB st).2 ↔
      y ∈ st.2 ∧ (y ∈ AB.2 → CovLE (AB.1 ∩ (step k AB st).1) y (k - 1)) := Iff.rfl

/-- The invariant of the fold. -/
def Inv (k : ℕ) (ρ : List (St n t)) (st : St n t) : Prop :=
  ∀ AB ∈ ρ, (∀ x ∈ AB.1 ∩ st.1, CovLE (AB.2 ∩ st.2) x (k - 1)) ∧
    (∀ y ∈ AB.2 ∩ st.2, CovLE (AB.1 ∩ st.1) y (k - 1))

theorem inv_run (k : ℕ) : ∀ ρ : List (St n t), Inv k ρ (run k ρ)
  | [] => fun _ h => absurd h (List.not_mem_nil)
  | AB :: ρ => by
    have ih := inv_run k ρ
    have hrun : run k (AB :: ρ) = step k AB (run k ρ) := rfl
    rw [hrun]
    have h1 : (step k AB (run k ρ)).1 ⊆ (run k ρ).1 := fun x hx => (mem_step1.1 hx).1
    have h2 : (step k AB (run k ρ)).2 ⊆ (run k ρ).2 := fun y hy => (mem_step2.1 hy).1
    intro AB' hAB'
    rcases List.mem_cons.1 hAB' with rfl | hAB'
    · refine ⟨fun x hx => ?_, fun y hy => (mem_step2.1 hy.2).2 hy.1⟩
      exact covLE_mono (Set.inter_subset_inter_right _ h2) le_rfl ((mem_step1.1 hx.2).2 hx.1)
    · refine ⟨fun x hx => ?_, fun y hy => ?_⟩
      · exact covLE_mono (Set.inter_subset_inter_right _ h2) le_rfl
          ((ih AB' hAB').1 x ⟨hx.1, h1 hx.2⟩)
      · exact covLE_mono (Set.inter_subset_inter_right _ h1) le_rfl
          ((ih AB' hAB').2 y ⟨hy.1, h2 hy.2⟩)

/-- The number of points in a set. -/
noncomputable def cnt (S : Set (Half n t)) : ℕ := (Finset.univ.filter fun x => x ∈ S).card

/-! ## L8 per node: each node removes few points on each side -/

theorem node_bound (k r0 : ℕ) (hk : 4 * k ≤ 2 ^ t) (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r)
    (AB st : St n t) (hy : ∀ y ∈ AB.2 ∩ st.2, CovLE (AB.1 ∩ st.1) y (2 * k)) :
    cnt st.1 * 2 ^ r0 ≤ cnt (step k AB st).1 * 2 ^ r0 + Fintype.card (Half n t) ∧
    cnt st.2 * 2 ^ r0 ≤ cnt (step k AB st).2 * 2 ^ r0 + Fintype.card (Half n t) := by
  constructor
  · have hc := core k r0 hk hr (AB.1 ∩ st.1) (AB.2 ∩ st.2) hy
    have hsub : (Finset.univ.filter fun x => x ∈ st.1) ⊆
        (Finset.univ.filter fun x => x ∈ (step k AB st).1) ∪
        (Finset.univ.filter fun x : Half n t =>
          x ∈ AB.1 ∩ st.1 ∧ ¬ CovLE (AB.2 ∩ st.2) x (k - 1)) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
      by_cases h : x ∈ AB.1 → CovLE (AB.2 ∩ st.2) x (k - 1)
      · exact Or.inl (mem_step1.2 ⟨hx, h⟩)
      · push Not at h
        exact Or.inr ⟨⟨h.1, hx⟩, h.2⟩
    have h0 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    unfold cnt
    calc _ ≤ ((Finset.univ.filter fun x => x ∈ (step k AB st).1).card +
          (Finset.univ.filter fun x : Half n t =>
            x ∈ AB.1 ∩ st.1 ∧ ¬ CovLE (AB.2 ∩ st.2) x (k - 1)).card) * 2 ^ r0 :=
          Nat.mul_le_mul_right _ h0
      _ = _ := add_mul _ _ _
      _ ≤ _ := by convert Nat.add_le_add_left hc _
  · have hx : ∀ x ∈ AB.1 ∩ (step k AB st).1, CovLE (AB.2 ∩ st.2) x (2 * k) := fun x hx =>
      covLE_mono subset_rfl (by omega) ((mem_step1.1 hx.2).2 hx.1)
    have hc := core k r0 hk hr (AB.2 ∩ st.2) (AB.1 ∩ (step k AB st).1) hx
    have hsub : (Finset.univ.filter fun y => y ∈ st.2) ⊆
        (Finset.univ.filter fun y => y ∈ (step k AB st).2) ∪
        (Finset.univ.filter fun y : Half n t =>
          y ∈ AB.2 ∩ st.2 ∧ ¬ CovLE (AB.1 ∩ (step k AB st).1) y (k - 1)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
      by_cases h : y ∈ AB.2 → CovLE (AB.1 ∩ (step k AB st).1) y (k - 1)
      · exact Or.inl (mem_step2.2 ⟨hy, h⟩)
      · push Not at h
        exact Or.inr ⟨⟨h.1, hy⟩, h.2⟩
    have h0 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    unfold cnt
    calc _ ≤ ((Finset.univ.filter fun y => y ∈ (step k AB st).2).card +
          (Finset.univ.filter fun y : Half n t =>
            y ∈ AB.2 ∩ st.2 ∧ ¬ CovLE (AB.1 ∩ (step k AB st).1) y (k - 1)).card) * 2 ^ r0 :=
          Nat.mul_le_mul_right _ h0
      _ = _ := add_mul _ _ _
      _ ≤ _ := by convert Nat.add_le_add_left hc _

/-! ## L8 total: summing over the dag -/

theorem total (k r0 : ℕ) (hk1 : 0 < k) (hk : 4 * k ≤ 2 ^ t)
    (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r) {ρ : List (St n t)} (h : ADag n t ρ) :
    Fintype.card (Half n t) * 2 ^ r0 ≤
        cnt (run k ρ).1 * 2 ^ r0 + ρ.length * Fintype.card (Half n t) ∧
      Fintype.card (Half n t) * 2 ^ r0 ≤
        cnt (run k ρ).2 * 2 ^ r0 + ρ.length * Fintype.card (Half n t) := by
  induction h with
  | nil =>
    have hu : cnt (Set.univ : Set (Half n t)) = Fintype.card (Half n t) := by
      simp [cnt]
    have hr0 : run k ([] : List (St n t)) = (Set.univ, Set.univ) := rfl
    rw [hr0]
    simp [hu]
  | @sink ρ A B i j hρ hij hA hB ih =>
    have hy : ∀ y ∈ B ∩ (run k ρ).2, CovLE (A ∩ (run k ρ).1) y (2 * k) := by
      intro y hy
      refine ⟨{(i, j)}, ?_, ?_, ?_⟩
      · rw [Finset.singleton_subset_iff, mem_coll]; exact ⟨hij, hB y hy.1⟩
      · rw [Finset.card_singleton]; omega
      · intro x hx; exact ⟨(i, j), Finset.mem_singleton_self _, hA x hx.1⟩
    obtain ⟨h1, h2⟩ := node_bound k r0 hk hr (A, B) (run k ρ) hy
    obtain ⟨ih1, ih2⟩ := ih
    have hrun : run k ((A, B) :: ρ) = step k (A, B) (run k ρ) := rfl
    rw [hrun, List.length_cons]
    constructor <;> nlinarith
  | @split ρ A B A₁ B₁ A₂ B₂ hρ hm₁ hm₂ hsub ih =>
    have hinv := inv_run k ρ
    have hy : ∀ y ∈ B ∩ (run k ρ).2, CovLE (A ∩ (run k ρ).1) y (2 * k) := by
      intro y hy
      have c1 : CovLE {x | x ∈ A₁ ∩ (run k ρ).1 ∧ y ∈ B₁} y (k - 1) :=
        covLE_cond fun hyB => (hinv _ hm₁).2 y ⟨hyB, hy.2⟩
      have c2 : CovLE {x | x ∈ A₂ ∩ (run k ρ).1 ∧ y ∈ B₂} y (k - 1) :=
        covLE_cond fun hyB => (hinv _ hm₂).2 y ⟨hyB, hy.2⟩
      refine covLE_mono subset_rfl (by omega) (covLE_union ?_ c1 c2)
      intro x hx
      rcases hsub (Set.mk_mem_prod hx.1 hy.1) with h | h
      · exact Or.inl ⟨⟨h.1, hx.2⟩, h.2⟩
      · exact Or.inr ⟨⟨h.1, hx.2⟩, h.2⟩
    obtain ⟨h1, h2⟩ := node_bound k r0 hk hr (A, B) (run k ρ) hy
    obtain ⟨ih1, ih2⟩ := ih
    have hrun : run k ((A, B) :: ρ) = step k (A, B) (run k ρ) := rfl
    rw [hrun, List.length_cons]
    constructor <;> nlinarith

/-! ## L7: the root -/

theorem root (k : ℕ) (σ : List (St n t)) (hroot : ((Set.univ, Set.univ) : St n t) ∈ σ) :
    cnt (run k σ).1 = 0 ∨ cnt (run k σ).2 * 2 ^ t ≤ (k - 1) * Fintype.card (Half n t) := by
  by_cases hx : ∃ x, x ∈ (run k σ).1
  · right
    obtain ⟨x, hx⟩ := hx
    obtain ⟨S, hS, hcard, hcov⟩ := (inv_run k σ _ hroot).1 x ⟨trivial, hx⟩
    have hsub : (Finset.univ.filter fun y => y ∈ (run k σ).2) ⊆
        S.biUnion fun p => Finset.univ.filter fun y : Half n t => y p.1 = y p.2 := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨p, hp, e⟩ := hcov y ⟨trivial, hy⟩
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

/-! ## The generic lower bound -/

theorem lower (k r0 : ℕ) (hk1 : 0 < k) (hk : 4 * k = 2 ^ t) (hr0 : 1 ≤ r0)
    (hr : ∀ r, k ≤ 4 * r ^ 2 → r0 ≤ r) (σ : List (St n t)) (h : ADagFor n t σ) :
    2 ^ (r0 - 1) ≤ σ.length := by
  obtain ⟨h1, h2⟩ := total k r0 hk1 hk.le hr h.1
  have hN : 0 < Fintype.card (Half n t) := Fintype.card_pos
  have hP : 2 ^ r0 = 2 * 2 ^ (r0 - 1) := by
    rw [← pow_succ']; congr 1; omega
  set N := Fintype.card (Half n t)
  set L := σ.length
  set P := 2 ^ r0
  set Q := 2 ^ (r0 - 1)
  rcases root k σ h.2 with hX | hY
  · rw [hX, zero_mul, zero_add, mul_comm L] at h1
    have := Nat.le_of_mul_le_mul_left h1 hN
    omega
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hY
    rw [← hk] at hY
    set c := cnt (run (k' + 1) σ).2
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

/-- CORE: every abstract rectangle dag for bit pigeonhole with `n = 16 ^ (s + 1)` and
`t = 2 s + 2` has at least `2 ^ (2 ^ (s - 1) - 1)` nodes. -/
theorem adag_lower' (s : ℕ) (σ : List (Set (Half (16 ^ (s + 1)) (2 * s + 2)) ×
    Set (Half (16 ^ (s + 1)) (2 * s + 2)))) (h : ADagFor (16 ^ (s + 1)) (2 * s + 2) σ) :
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
    have := lower (4 ^ (s + 1)) (2 ^ s) (by positivity) hk Nat.one_le_two_pow hr σ h
    rw [Nat.add_sub_cancel]
    exact this

end PEqualNP.Search.Helpers.BW
