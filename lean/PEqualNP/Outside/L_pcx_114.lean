import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_114

open PEqualNP.ProofComplexity
theorem snd_res {V : Type} [DecidableEq V] {C D R : LinClause V} (h : IsLinResolvent C D R) (a : V → Bool) (hR : ¬ LinClauseSat a R) :
    ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := by
  obtain ⟨f, hC, hD, rfl⟩ := h
  by_cases hf : Odd (f.filter (fun v => a v = true)).card
  · left
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    have := hs.1 hf
    cases this
  · right
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    exact hf (hs.2 rfl)

section gen
variable {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι] (F : Set (LinClause V)) (Pt : ι → (V → Bool) → Prop)
  (H : ∀ R ∈ F, ∃ k0 : ι, ∀ k, k ≠ k0 → ∀ a, Pt k a → LinClauseSat a R)

def Hit (K : Finset ι) (N : Finset (LinClause V)) : Prop := ∀ k ∈ K, ∃ a, Pt k a ∧ ∃ R ∈ N, ¬ LinClauseSat a R

theorem hit_step {K : Finset ι} {N Q : Finset (LinClause V)} {R : LinClause V} (h : Hit Pt K N)
    (hq : ∀ a, ¬ LinClauseSat a R → ∃ D ∈ Q, ¬ LinClauseSat a D) : Hit Pt K (N.erase R ∪ Q) := by
  intro k hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  by_cases e : M = R
  · subst e
    obtain ⟨D, hD, hd⟩ := hq a hs
    exact ⟨a, ha, D, Finset.mem_union_right _ hD, hd⟩
  · exact ⟨a, ha, M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hM⟩), hs⟩

theorem hit_ax {K : Finset ι} {N : Finset (LinClause V)} {R : LinClause V} (h : Hit Pt K N) (k0 : ι)
    (hk0 : ∀ k, k ≠ k0 → ∀ a, Pt k a → LinClauseSat a R) : Hit Pt (K.erase k0) (N.erase R) := by
  intro k hk
  obtain ⟨hne, hk⟩ := Finset.mem_erase.1 hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  refine ⟨a, ha, M, Finset.mem_erase.2 ⟨?_, hM⟩, hs⟩
  rintro rfl
  exact hs (hk0 k hne a ha)

theorem card_step (N Q : Finset (LinClause V)) (R : LinClause V) (hR : R ∈ N) : (N.erase R ∪ Q).card + 1 ≤ N.card + Q.card := by
  have h1 := Finset.card_union_le (N.erase R) Q
  have h2 := Finset.card_erase_of_mem hR
  have h3 := Finset.card_pos.2 ⟨R, hR⟩
  omega

theorem tl {N : Finset (LinClause V)} {R : LinClause V} {π : List (LinClause V)} (h : ∀ M ∈ N, M ∈ R :: π) : ∀ M ∈ N.erase R, M ∈ π := by
  intro M hM
  obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hM
  rcases List.mem_cons.1 (h M h2) with e | e
  · exact absurd e h1
  · exact e

theorem tln {N : Finset (LinClause V)} {R : LinClause V} {π : List (LinClause V)} (h : ∀ M ∈ N, M ∈ R :: π) (hR : R ∉ N) : ∀ M ∈ N, M ∈ π := by
  intro M hM
  rcases List.mem_cons.1 (h M hM) with e | e
  · subst e; exact absurd hM hR
  · exact e

include H in
theorem plain {π : List (LinClause V)} (hπ : IsLinDerivation F π) : ∀ (N : Finset (LinClause V)) (K : Finset ι),
    (∀ M ∈ N, M ∈ π) → Hit Pt K N → 2 * K.card ≤ π.length + N.card := by
  induction hπ with
  | nil =>
    intro N K hN hK
    have : K = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨_, _, M, hM, _⟩ := hK k hk
      have := hN M hM
      simp at this
    simp [this]
  | @ax π C hπ hC ih =>
    intro N K hN hK
    by_cases hR : C ∈ N
    · obtain ⟨k0, hk0⟩ := H C hC
      have := ih (N.erase C) (K.erase k0) (tl hN) (hit_ax Pt hK k0 hk0)
      have h2 := Finset.card_erase_of_mem hR
      have h3 := Finset.card_pos.2 ⟨C, hR⟩
      have h4 := Finset.pred_card_le_card_erase (s := K) (a := k0)
      rw [List.length_cons]
      omega
    · have := ih N K (tln hN hR) hK
      rw [List.length_cons]; omega
  | @res π C D R hπ hC hD hr ih =>
    intro N K hN hK
    by_cases hR : R ∈ N
    · have hh := hit_step Pt (Q := {C, D}) hK (R := R) (fun a ha => by
        rcases snd_res hr a ha with h | h
        · exact ⟨C, by simp, h⟩
        · exact ⟨D, by simp, h⟩)
      have := ih _ K (fun M hM => by
        rcases Finset.mem_union.1 hM with h | h
        · exact tl hN M h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl <;> assumption) hh
      have h2 := card_step N {C, D} R hR
      have h3 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
      rw [List.length_cons]; omega
    · have := ih N K (tln hN hR) hK
      rw [List.length_cons]; omega
  | @weak π C D hπ hC hw ih =>
    intro N K hN hK
    by_cases hR : D ∈ N
    · have hh := hit_step Pt (Q := {C}) hK (R := D) (fun a ha => ⟨C, by simp, fun h => ha (hw a h)⟩)
      have := ih _ K (fun M hM => by
        rcases Finset.mem_union.1 hM with h | h
        · exact tl hN M h
        · simp only [Finset.mem_singleton] at h
          subst h; exact hC) hh
      have h2 := card_step N {C} D hR
      rw [Finset.card_singleton] at h2
      rw [List.length_cons]; omega
    · have := ih N K (tln hN hR) hK
      rw [List.length_cons]; omega

include H in
theorem marked (hF : ∀ R ∈ F, ∀ q ∈ R, q.1.card = 1) {π : List (LinClause V)} (hπ : IsLinDerivation F π) : ∀ (N : Finset (LinClause V)) (K : Finset ι),
    (∀ M ∈ N, M ∈ π) → Hit Pt K N → (∃ M ∈ N, ∃ q ∈ M, q.1.card ≠ 1) → 2 * K.card + 1 ≤ π.length + N.card := by
  induction hπ with
  | nil =>
    rintro N K hN _ ⟨M, hM, _⟩
    have := hN M hM
    simp at this
  | @ax π C hπ hC ih =>
    rintro N K hN hK ⟨M, hM, q, hq, hc⟩
    by_cases hR : C ∈ N
    · obtain ⟨k0, hk0⟩ := H C hC
      have hne : M ≠ C := by rintro rfl; exact hc (hF _ hC q hq)
      have := ih (N.erase C) (K.erase k0) (tl hN) (hit_ax Pt hK k0 hk0) ⟨M, Finset.mem_erase.2 ⟨hne, hM⟩, q, hq, hc⟩
      have h2 := Finset.card_erase_of_mem hR
      have h3 := Finset.card_pos.2 ⟨C, hR⟩
      have h4 := Finset.pred_card_le_card_erase (s := K) (a := k0)
      rw [List.length_cons]
      omega
    · have := ih N K (tln hN hR) hK ⟨M, hM, q, hq, hc⟩
      rw [List.length_cons]; omega
  | @res π C D R hπ hC hD hr ih =>
    rintro N K hN hK ⟨M, hM, q, hq, hc⟩
    by_cases hR : R ∈ N
    · have hh := hit_step Pt (Q := {C, D}) hK (R := R) (fun a ha => by
        rcases snd_res hr a ha with h | h
        · exact ⟨C, by simp, h⟩
        · exact ⟨D, by simp, h⟩)
      have hm : ∃ M ∈ N.erase R ∪ {C, D}, ∃ q ∈ M, q.1.card ≠ 1 := by
        by_cases e : M = R
        · subst e
          obtain ⟨f, _, _, rfl⟩ := hr
          rcases Finset.mem_union.1 hq with h | h
          · exact ⟨C, by simp, q, Finset.mem_of_mem_erase h, hc⟩
          · exact ⟨D, by simp, q, Finset.mem_of_mem_erase h, hc⟩
        · exact ⟨M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hM⟩), q, hq, hc⟩
      have := ih _ K (fun M hM => by
        rcases Finset.mem_union.1 hM with h | h
        · exact tl hN M h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl <;> assumption) hh hm
      have h2 := card_step N {C, D} R hR
      have h3 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
      rw [List.length_cons]; omega
    · have := ih N K (tln hN hR) hK ⟨M, hM, q, hq, hc⟩
      rw [List.length_cons]; omega
  | @weak π C D hπ hC hw ih =>
    rintro N K hN hK ⟨M, hM, q, hq, hc⟩
    by_cases hR : D ∈ N
    · have hh := hit_step Pt (Q := {C}) hK (R := D) (fun a ha => ⟨C, by simp, fun h => ha (hw a h)⟩)
      have := plain F Pt H hπ _ K (fun M hM => by
        rcases Finset.mem_union.1 hM with h | h
        · exact tl hN M h
        · simp only [Finset.mem_singleton] at h
          subst h; exact hC) hh
      have h2 := card_step N {C} D hR
      rw [Finset.card_singleton] at h2
      rw [List.length_cons]; omega
    · have := ih N K (tln hN hR) hK ⟨M, hM, q, hq, hc⟩
      rw [List.length_cons]; omega

include H in
/-- Two disjoint parts of the frontier that both lead to the same starting clause cost one line more. -/
theorem split (i : ι) (p p' : V → Bool) (hp : Pt i p) (hp' : Pt i p') {π : List (LinClause V)} (hπ : IsLinDerivation F π) :
    ∀ (A B : Finset (LinClause V)) (K : Finset ι), Disjoint A B → (∀ M ∈ A ∪ B, M ∈ π) → Hit Pt K (A ∪ B) →
      (∃ M ∈ A, ¬ LinClauseSat p M) → (∃ M ∈ B, ¬ LinClauseSat p' M) → 2 * K.card + 1 ≤ π.length + (A ∪ B).card := by
  -- one step on the part that holds the head
  have stepR : ∀ {π : List (LinClause V)} (hπ : IsLinDerivation F π) (R : LinClause V) (Q A B : Finset (LinClause V)) (K : Finset ι) (r : V → Bool),
      Q.card ≤ 2 → (∀ M ∈ Q, M ∈ π) → (∀ a, ¬ LinClauseSat a R → ∃ D ∈ Q, ¬ LinClauseSat a D) → R ∈ A → Disjoint A B →
      (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ¬ LinClauseSat r M) →
      ((∀ (A' : Finset (LinClause V)), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K (A' ∪ B) → (∃ M ∈ A', ¬ LinClauseSat r M) →
        2 * K.card + 1 ≤ π.length + (A' ∪ B).card)) → 2 * K.card + 1 ≤ (R :: π).length + (A ∪ B).card := by
    intro π hπ R Q A B K r hQ hQm hq hRA hd hN hK hA ih
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have hh := hit_step Pt hK hq
    have hmem : ∀ M ∈ (A ∪ B).erase R ∪ Q, M ∈ π := by
      intro M hM
      rcases Finset.mem_union.1 hM with h | h
      · exact tl hN M h
      · exact hQm M h
    have hcs := card_step (A ∪ B) Q R hRN
    rw [List.length_cons]
    by_cases hQB : Disjoint Q B
    · have e : (A ∪ B).erase R ∪ Q = (A.erase R ∪ Q) ∪ B := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
        ext x; simp only [Finset.mem_union]; tauto
      rw [e] at hh hmem hcs
      have hd' : Disjoint (A.erase R ∪ Q) B := by
        rw [Finset.disjoint_union_left]
        exact ⟨hd.mono_left (Finset.erase_subset _ _), hQB⟩
      have hA' : ∃ M ∈ A.erase R ∪ Q, ¬ LinClauseSat r M := by
        obtain ⟨M, hM, hs⟩ := hA
        by_cases eM : M = R
        · subst eM
          obtain ⟨D, hD, hdd⟩ := hq r hs
          exact ⟨D, Finset.mem_union_right _ hD, hdd⟩
        · exact ⟨M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨eM, hM⟩), hs⟩
      have := ih _ hd' hmem hh hA'
      omega
    · have h1 := plain F Pt H hπ _ K hmem hh
      obtain ⟨x, hxQ, hxB⟩ := Finset.not_disjoint_iff.1 hQB
      have hxN : x ∈ (A ∪ B).erase R := Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hxB, Finset.mem_union_right _ hxB⟩
      have h2 : ((A ∪ B).erase R ∪ Q).card + 1 ≤ ((A ∪ B).erase R).card + Q.card := by
        have hi := Finset.card_union_add_card_inter ((A ∪ B).erase R) Q
        have : 0 < ((A ∪ B).erase R ∩ Q).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hxN, hxQ⟩⟩
        omega
      have h3 := Finset.card_erase_of_mem hRN
      have h4 := Finset.card_pos.2 ⟨R, hRN⟩
      omega
  have stepA : ∀ {π : List (LinClause V)} (hπ : IsLinDerivation F π) (R : LinClause V) (A B : Finset (LinClause V)) (K : Finset ι) (r r' : V → Bool),
      Pt i r → Pt i r' → R ∈ F → R ∈ A → Disjoint A B → (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ¬ LinClauseSat r M) → (∃ M ∈ B, ¬ LinClauseSat r' M) →
      (∀ (A' : Finset (LinClause V)) (K' : Finset ι), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K' (A' ∪ B) → (∃ M ∈ A', ¬ LinClauseSat r M) →
        2 * K'.card + 1 ≤ π.length + (A' ∪ B).card) → 2 * K.card + 1 ≤ (R :: π).length + (A ∪ B).card := by
    intro π hπ R A B K r r' hr hr' hRF hRA hd hN hK hA hB ih
    obtain ⟨k0, hk0⟩ := H R hRF
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have h3 := Finset.card_erase_of_mem hRN
    have h4 := Finset.card_pos.2 ⟨R, hRN⟩
    rw [List.length_cons]
    by_cases hi : k0 = i
    · subst hi
      have hh : Hit Pt K ((A ∪ B).erase R) := by
        intro k hk
        by_cases hkk : k = k0
        · subst hkk
          obtain ⟨M, hM, hs⟩ := hB
          exact ⟨r', hr', M, Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hM, Finset.mem_union_right _ hM⟩, hs⟩
        · exact hit_ax Pt hK k0 hk0 k (Finset.mem_erase.2 ⟨hkk, hk⟩)
      have := plain F Pt H hπ _ K (tl hN) hh
      omega
    · have e : (A ∪ B).erase R = A.erase R ∪ B := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
      have hh := hit_ax Pt hK k0 hk0
      have hmem := tl hN
      rw [e] at hh hmem h3
      have hA' : ∃ M ∈ A.erase R, ¬ LinClauseSat r M := by
        obtain ⟨M, hM, hs⟩ := hA
        exact ⟨M, Finset.mem_erase.2 ⟨by rintro rfl; exact hs (hk0 i (Ne.symm hi) r hr), hM⟩, hs⟩
      have := ih _ _ (hd.mono_left (Finset.erase_subset _ _)) hmem hh hA'
      have h5 := Finset.pred_card_le_card_erase (s := K) (a := k0)
      omega
  induction hπ with
  | nil =>
    rintro A B K _ hN _ ⟨M, hM, _⟩ _
    have := hN M (Finset.mem_union_left _ hM)
    simp at this
  | @ax π C hπ hC ih =>
    intro A B K hd hN hK hA hB
    by_cases hRA : C ∈ A
    · exact stepA hπ C A B K p p' hp hp' hC hRA hd hN hK hA hB (fun A' K' h1 h2 h3 h4 => ih A' B K' h1 h2 h3 h4 hB)
    · by_cases hRB : C ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepA hπ C B A K p' p hp' hp hC hRB hd.symm hN hK hB hA (fun A' K' h1 h2 h3 h4 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih A A' K' h1.symm h2 h3 hA h4
      · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
        rw [List.length_cons]; omega
  | @res π C D R hπ hC hD hr ih =>
    intro A B K hd hN hK hA hB
    have q1 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
    have q2 : ∀ M ∈ ({C, D} : Finset (LinClause V)), M ∈ π := by
      intro M h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl <;> assumption
    have q3 : ∀ a, ¬ LinClauseSat a R → ∃ E ∈ ({C, D} : Finset (LinClause V)), ¬ LinClauseSat a E := by
      intro a ha
      rcases snd_res hr a ha with h | h
      · exact ⟨C, by simp, h⟩
      · exact ⟨D, by simp, h⟩
    by_cases hRA : R ∈ A
    · exact stepR hπ R _ A B K p q1 q2 q3 hRA hd hN hK hA (fun A' h1 h2 h3 h4 => ih A' B K h1 h2 h3 h4 hB)
    · by_cases hRB : R ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepR hπ R _ B A K p' q1 q2 q3 hRB hd.symm hN hK hB (fun A' h1 h2 h3 h4 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih A A' K h1.symm h2 h3 hA h4
      · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
        rw [List.length_cons]; omega
  | @weak π C D hπ hC hw ih =>
    intro A B K hd hN hK hA hB
    have q1 : ({C} : Finset (LinClause V)).card ≤ 2 := by simp
    have q2 : ∀ M ∈ ({C} : Finset (LinClause V)), M ∈ π := by
      intro M h
      simp only [Finset.mem_singleton] at h
      subst h; exact hC
    have q3 : ∀ a, ¬ LinClauseSat a D → ∃ E ∈ ({C} : Finset (LinClause V)), ¬ LinClauseSat a E :=
      fun a ha => ⟨C, by simp, fun h => ha (hw a h)⟩
    by_cases hRA : D ∈ A
    · exact stepR hπ D _ A B K p q1 q2 q3 hRA hd hN hK hA (fun A' h1 h2 h3 h4 => ih A' B K h1 h2 h3 h4 hB)
    · by_cases hRB : D ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepR hπ D _ B A K p' q1 q2 q3 hRB hd.symm hN hK hB (fun A' h1 h2 h3 h4 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih A A' K h1.symm h2 h3 hA h4
      · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
        rw [List.length_cons]; omega


include H in
theorem low [Fintype ι] [Nontrivial ι] (hF : ∀ R ∈ F, ∀ q ∈ R, q.1.card = 1) (hex : ∀ k, ∃ a, Pt k a)
    (hV : ∀ v : V, ∃ i, ∃ p p' : V → Bool, Pt i p ∧ Pt i p' ∧ p v = true ∧ p' v = false)
    {π : List (LinClause V)} (hπ : IsLinDerivation F π) : ∅ ∈ π → 2 * Fintype.card ι ≤ π.length := by
  have nos : ∀ a : V → Bool, ¬ LinClauseSat a ∅ := by rintro a ⟨q, hq, _⟩; simp at hq
  have hc : (Finset.univ : Finset ι).card = Fintype.card ι := rfl
  induction hπ with
  | nil => intro h; simp at h
  | @ax π C hπ hC ih =>
    intro h
    rcases List.mem_cons.1 h with e | e
    · exfalso
      obtain ⟨k0, hk0⟩ := H C hC
      obtain ⟨k, hk⟩ : ∃ k : ι, k ≠ k0 := exists_ne k0
      obtain ⟨a, ha⟩ := hex k
      have := hk0 k hk a ha
      rw [← e] at this
      exact nos a this
    · have := ih e
      rw [List.length_cons]; omega
  | @res π C D R hπ hC hD hr ih =>
    intro h
    rcases List.mem_cons.1 h with e | e
    · have hu : ∀ a, ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := fun a => snd_res hr a (e ▸ nos a)
      have hit : Hit Pt Finset.univ ({C, D} : Finset (LinClause V)) := by
        intro k _
        obtain ⟨a, ha⟩ := hex k
        rcases hu a with h | h
        · exact ⟨a, ha, C, by simp, h⟩
        · exact ⟨a, ha, D, by simp, h⟩
      have hm : ∀ M ∈ ({C, D} : Finset (LinClause V)), M ∈ π := by
        intro M h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> assumption
      have c2 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
      obtain ⟨f, hfC, hfD, hR⟩ := hr
      rw [← e] at hR
      have hR := hR.symm
      rw [Finset.union_eq_empty] at hR
      have eC : C = {(f, false)} := by
        rw [← Finset.insert_erase hfC, hR.1]; rfl
      have eD : D = {(f, true)} := by
        rw [← Finset.insert_erase hfD, hR.2]; rfl
      by_cases hf : f.card = 1
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hf
        obtain ⟨i, p, p', hp, hp', hv1, hv2⟩ := hV v
        have hdis : Disjoint ({C} : Finset (LinClause V)) {D} := by
          rw [Finset.disjoint_singleton, eC, eD]
          intro h
          have := Finset.singleton_injective h
          simp at this
        have hs := split F Pt H i p p' hp hp' hπ {C} {D} Finset.univ hdis
          (by rw [← Finset.insert_eq]; exact hm) (by rw [← Finset.insert_eq]; exact hit)
          ⟨C, by simp, by
            rw [eC]; rintro ⟨q, hq, hs⟩
            rw [Finset.mem_singleton] at hq; subst hq
            simp [LinEqSat, hv1, Finset.filter_singleton] at hs⟩
          ⟨D, by simp, by
            rw [eD]; rintro ⟨q, hq, hs⟩
            rw [Finset.mem_singleton] at hq; subst hq
            simp [LinEqSat, hv2, Finset.filter_singleton] at hs⟩
        rw [← Finset.insert_eq, hc] at hs
        rw [List.length_cons]; omega
      · have := marked F Pt H hF hπ {C, D} Finset.univ hm hit ⟨C, by simp, (f, false), hfC, hf⟩
        rw [hc] at this
        rw [List.length_cons]; omega
    · have := ih e
      rw [List.length_cons]; omega
  | @weak π C D hπ hC hw ih =>
    intro h
    rcases List.mem_cons.1 h with e | e
    · have hit : Hit Pt Finset.univ ({C} : Finset (LinClause V)) := by
        intro k _
        obtain ⟨a, ha⟩ := hex k
        exact ⟨a, ha, C, by simp, fun h => nos a (e ▸ hw a h)⟩
      have := plain F Pt H hπ {C} Finset.univ (by simpa using hC) hit
      rw [hc, Finset.card_singleton] at this
      rw [List.length_cons]; omega
    · have := ih e
      rw [List.length_cons]; omega


theorem pair_of {x e : LinClause V} {Q : Finset (LinClause V)} (hQ : Q.card ≤ 2) (hx : x ∈ Q) (he : e ∈ Q) (hne : x ≠ e) : Q = {x, e} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne]; exact hQ

include H in
/-- Both disjoint parts hold a line with a form of size other than one: two lines more. -/
theorem dm (hF : ∀ R ∈ F, ∀ q ∈ R, q.1.card = 1) {π : List (LinClause V)} (hπ : IsLinDerivation F π) :
    ∀ (A B : Finset (LinClause V)) (K : Finset ι), Disjoint A B → (∀ M ∈ A ∪ B, M ∈ π) → Hit Pt K (A ∪ B) →
      (∃ M ∈ A, ∃ q ∈ M, q.1.card ≠ 1) → (∃ M ∈ B, ∃ q ∈ M, q.1.card ≠ 1) → 2 * K.card + 2 ≤ π.length + (A ∪ B).card := by
  have stepQ : ∀ {π : List (LinClause V)} (hπ : IsLinDerivation F π) (R : LinClause V) (Q A B : Finset (LinClause V)) (K : Finset ι),
      Q.card ≤ 2 → (∀ M ∈ Q, M ∈ π) → (∀ a, ¬ LinClauseSat a R → ∃ D ∈ Q, ¬ LinClauseSat a D) →
      ((∃ q ∈ R, q.1.card ≠ 1) → (∃ D ∈ Q, ∃ q ∈ D, q.1.card ≠ 1) ∨ Q.card ≤ 1) → R ∈ A → Disjoint A B →
      (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ∃ q ∈ M, q.1.card ≠ 1) → (∃ M ∈ B, ∃ q ∈ M, q.1.card ≠ 1) →
      ((∀ (A' : Finset (LinClause V)), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K (A' ∪ B) → (∃ M ∈ A', ∃ q ∈ M, q.1.card ≠ 1) →
        2 * K.card + 2 ≤ π.length + (A' ∪ B).card)) → 2 * K.card + 2 ≤ (R :: π).length + (A ∪ B).card := by
    intro π hπ R Q A B K hQ hQm hq hqm hRA hd hN hK hA hB ih
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have hh := hit_step Pt hK hq
    have hmem : ∀ M ∈ (A ∪ B).erase R ∪ Q, M ∈ π := by
      intro M hM
      rcases Finset.mem_union.1 hM with h | h
      · exact tl hN M h
      · exact hQm M h
    have hcs := card_step (A ∪ B) Q R hRN
    have h3 := Finset.card_erase_of_mem hRN
    have h4 := Finset.card_pos.2 ⟨R, hRN⟩
    have hmk : ∃ M ∈ (A ∪ B).erase R ∪ Q, ∃ q ∈ M, q.1.card ≠ 1 := by
      obtain ⟨M, hM, hs⟩ := hB
      exact ⟨M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hM, Finset.mem_union_right _ hM⟩), hs⟩
    have h1 := marked F Pt H hF hπ _ K hmem hh hmk
    rw [List.length_cons]
    by_cases hQ1 : Q.card ≤ 1
    · omega
    by_cases hQB : Disjoint Q B
    · have e : (A ∪ B).erase R ∪ Q = (A.erase R ∪ Q) ∪ B := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
        ext x; simp only [Finset.mem_union]; tauto
      rw [e] at hh hmem hcs
      have hd' : Disjoint (A.erase R ∪ Q) B := by
        rw [Finset.disjoint_union_left]
        exact ⟨hd.mono_left (Finset.erase_subset _ _), hQB⟩
      have hA' : ∃ M ∈ A.erase R ∪ Q, ∃ q ∈ M, q.1.card ≠ 1 := by
        obtain ⟨M, hM, hs⟩ := hA
        by_cases eM : M = R
        · subst eM
          rcases hqm hs with ⟨D, hD, hdd⟩ | h
          · exact ⟨D, Finset.mem_union_right _ hD, hdd⟩
          · exact absurd h hQ1
        · exact ⟨M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨eM, hM⟩), hs⟩
      have := ih _ hd' hmem hh hA'
      omega
    · obtain ⟨x, hxQ, hxB⟩ := Finset.not_disjoint_iff.1 hQB
      have hxN : x ∈ (A ∪ B).erase R := Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hxB, Finset.mem_union_right _ hxB⟩
      have h2 : ((A ∪ B).erase R ∪ Q).card + 1 ≤ ((A ∪ B).erase R).card + Q.card := by
        have hi := Finset.card_union_add_card_inter ((A ∪ B).erase R) Q
        have : 0 < ((A ∪ B).erase R ∩ Q).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hxN, hxQ⟩⟩
        omega
      omega
  have stepA : ∀ {π : List (LinClause V)} (R : LinClause V) (A B : Finset (LinClause V)) (K : Finset ι),
      R ∈ F → R ∈ A → Disjoint A B → (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ∃ q ∈ M, q.1.card ≠ 1) →
      (∀ (A' : Finset (LinClause V)) (K' : Finset ι), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K' (A' ∪ B) → (∃ M ∈ A', ∃ q ∈ M, q.1.card ≠ 1) →
        2 * K'.card + 2 ≤ π.length + (A' ∪ B).card) → 2 * K.card + 2 ≤ (R :: π).length + (A ∪ B).card := by
    intro π R A B K hRF hRA hd hN hK hA ih
    obtain ⟨k0, hk0⟩ := H R hRF
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have h3 := Finset.card_erase_of_mem hRN
    have h4 := Finset.card_pos.2 ⟨R, hRN⟩
    have e : (A ∪ B).erase R = A.erase R ∪ B := by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
    have hh := hit_ax Pt hK k0 hk0
    have hmem := tl hN
    rw [e] at hh hmem h3
    have hA' : ∃ M ∈ A.erase R, ∃ q ∈ M, q.1.card ≠ 1 := by
      obtain ⟨M, hM, q, hq, hs⟩ := hA
      exact ⟨M, Finset.mem_erase.2 ⟨by rintro rfl; exact hs (hF _ hRF q hq), hM⟩, q, hq, hs⟩
    have := ih _ _ (hd.mono_left (Finset.erase_subset _ _)) hmem hh hA'
    have h5 := Finset.pred_card_le_card_erase (s := K) (a := k0)
    rw [List.length_cons]
    omega
  induction hπ with
  | nil =>
    rintro A B K _ hN _ ⟨M, hM, _⟩ _
    have := hN M (Finset.mem_union_left _ hM)
    simp at this
  | @ax π C hπ hC ih =>
    intro A B K hd hN hK hA hB
    by_cases hRA : C ∈ A
    · exact stepA C A B K hC hRA hd hN hK hA (fun A' K' h1 h2 h3 h4 => ih A' B K' h1 h2 h3 h4 hB)
    · by_cases hRB : C ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepA C B A K hC hRB hd.symm hN hK hB (fun A' K' h1 h2 h3 h4 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih A A' K' h1.symm h2 h3 hA h4
      · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
        rw [List.length_cons]; omega
  | @res π C D R hπ hC hD hr ih =>
    intro A B K hd hN hK hA hB
    have q1 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
    have q2 : ∀ M ∈ ({C, D} : Finset (LinClause V)), M ∈ π := by
      intro M h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl <;> assumption
    have q3 : ∀ a, ¬ LinClauseSat a R → ∃ E ∈ ({C, D} : Finset (LinClause V)), ¬ LinClauseSat a E := by
      intro a ha
      rcases snd_res hr a ha with h | h
      · exact ⟨C, by simp, h⟩
      · exact ⟨D, by simp, h⟩
    have q4 : (∃ q ∈ R, q.1.card ≠ 1) → (∃ E ∈ ({C, D} : Finset (LinClause V)), ∃ q ∈ E, q.1.card ≠ 1) ∨ ({C, D} : Finset (LinClause V)).card ≤ 1 := by
      rintro ⟨q, hq, hc⟩
      left
      obtain ⟨f, _, _, rfl⟩ := hr
      rcases Finset.mem_union.1 hq with h | h
      · exact ⟨C, by simp, q, Finset.mem_of_mem_erase h, hc⟩
      · exact ⟨D, by simp, q, Finset.mem_of_mem_erase h, hc⟩
    by_cases hRA : R ∈ A
    · exact stepQ hπ R _ A B K q1 q2 q3 q4 hRA hd hN hK hA hB (fun A' h1 h2 h3 h4 => ih A' B K h1 h2 h3 h4 hB)
    · by_cases hRB : R ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepQ hπ R _ B A K q1 q2 q3 q4 hRB hd.symm hN hK hB hA (fun A' h1 h2 h3 h4 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih A A' K h1.symm h2 h3 hA h4
      · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
        rw [List.length_cons]; omega
  | @weak π C D hπ hC hw ih =>
    intro A B K hd hN hK hA hB
    have q1 : ({C} : Finset (LinClause V)).card ≤ 2 := by simp
    have q2 : ∀ M ∈ ({C} : Finset (LinClause V)), M ∈ π := by
      intro M h
      simp only [Finset.mem_singleton] at h
      subst h; exact hC
    have q3 : ∀ a, ¬ LinClauseSat a D → ∃ E ∈ ({C} : Finset (LinClause V)), ¬ LinClauseSat a E :=
      fun a ha => ⟨C, by simp, fun h => ha (hw a h)⟩
    have q4 : (∃ q ∈ D, q.1.card ≠ 1) → (∃ E ∈ ({C} : Finset (LinClause V)), ∃ q ∈ E, q.1.card ≠ 1) ∨ ({C} : Finset (LinClause V)).card ≤ 1 :=
      fun _ => Or.inr (by simp)
    by_cases hRA : D ∈ A
    · exact stepQ hπ D _ A B K q1 q2 q3 q4 hRA hd hN hK hA hB (fun A' h1 h2 h3 h4 => ih A' B K h1 h2 h3 h4 hB)
    · by_cases hRB : D ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepQ hπ D _ B A K q1 q2 q3 q4 hRB hd.symm hN hK hB hA (fun A' h1 h2 h3 h4 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih A A' K h1.symm h2 h3 hA h4
      · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
        rw [List.length_cons]; omega

/-- A clause false at points that cover both values of every variable, with literal forms only, is empty. -/
theorem four {p q p' q' : V → Bool} (hcov : ∀ (v : V) (s : Bool), p v = s ∨ q v = s ∨ p' v = s ∨ q' v = s) (x : LinClause V)
    (h1 : ¬ LinClauseSat p x) (h2 : ¬ LinClauseSat q x) (h3 : ¬ LinClauseSat p' x) (h4 : ¬ LinClauseSat q' x) :
    x = ∅ ∨ ∃ e ∈ x, e.1.card ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hall⟩ := hcon
  obtain ⟨e, he⟩ := hne
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 (hall e he)
  have sat : ∀ a : V → Bool, a v = e.2 → LinClauseSat a x := by
    intro a ha
    refine ⟨e, he, ?_⟩
    unfold LinEqSat
    rw [hv, Finset.filter_singleton, ha]
    cases e.2 <;> simp
  rcases hcov v e.2 with h | h | h | h
  · exact h1 (sat _ h)
  · exact h2 (sat _ h)
  · exact h3 (sat _ h)
  · exact h4 (sat _ h)

include H in
/-- Two starting clauses needed on both sides: two lines more. -/
theorem s2 (hF : ∀ R ∈ F, ∀ q ∈ R, q.1.card = 1) (i j : ι) (p p' q q' : V → Bool) (hp : Pt i p) (hp' : Pt i p') (hq : Pt j q) (hq' : Pt j q')
    (hcov : ∀ (v : V) (s : Bool), p v = s ∨ q v = s ∨ p' v = s ∨ q' v = s) {π : List (LinClause V)} (hπ : IsLinDerivation F π) : ∅ ∉ π →
    ∀ (A B : Finset (LinClause V)) (K : Finset ι), Disjoint A B → (∀ M ∈ A ∪ B, M ∈ π) → Hit Pt K (A ∪ B) →
      (∃ M ∈ A, ¬ LinClauseSat p M) → (∃ M ∈ A, ¬ LinClauseSat q M) → (∃ M ∈ B, ¬ LinClauseSat p' M) → (∃ M ∈ B, ¬ LinClauseSat q' M) →
      2 * K.card + 2 ≤ π.length + (A ∪ B).card := by
  have stepR : ∀ {π : List (LinClause V)} (hπ : IsLinDerivation F π) (R : LinClause V) (Q A B : Finset (LinClause V)) (K : Finset ι) (p p' q q' : V → Bool),
      Pt i p → Pt i p' → Pt j q → Pt j q' → (∀ (v : V) (s : Bool), p v = s ∨ q v = s ∨ p' v = s ∨ q' v = s) → ∅ ∉ π →
      Q.card ≤ 2 → (∀ M ∈ Q, M ∈ π) → (∀ a, ¬ LinClauseSat a R → ∃ D ∈ Q, ¬ LinClauseSat a D) → R ∈ A → Disjoint A B →
      (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ¬ LinClauseSat p M) → (∃ M ∈ A, ¬ LinClauseSat q M) →
      (∃ M ∈ B, ¬ LinClauseSat p' M) → (∃ M ∈ B, ¬ LinClauseSat q' M) →
      ((∀ (A' : Finset (LinClause V)), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K (A' ∪ B) → (∃ M ∈ A', ¬ LinClauseSat p M) → (∃ M ∈ A', ¬ LinClauseSat q M) →
        2 * K.card + 2 ≤ π.length + (A' ∪ B).card)) → 2 * K.card + 2 ≤ (R :: π).length + (A ∪ B).card := by
    intro π hπ R Q A B K p p' q q' hp hp' hq hq' hcov hemp hQ hQm hqq hRA hd hN hK hA hAq hB hBq ih
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have hh := hit_step Pt hK hqq
    have hmem : ∀ M ∈ (A ∪ B).erase R ∪ Q, M ∈ π := by
      intro M hM
      rcases Finset.mem_union.1 hM with h | h
      · exact tl hN M h
      · exact hQm M h
    have hcs := card_step (A ∪ B) Q R hRN
    have h3 := Finset.card_erase_of_mem hRN
    have h4 := Finset.card_pos.2 ⟨R, hRN⟩
    have e0 : (A ∪ B).erase R = A.erase R ∪ B := by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
    rw [List.length_cons]
    by_cases hQB : Disjoint Q B
    · have e : (A ∪ B).erase R ∪ Q = (A.erase R ∪ Q) ∪ B := by
        rw [e0]
        ext x; simp only [Finset.mem_union]; tauto
      rw [e] at hh hmem hcs
      have hd' : Disjoint (A.erase R ∪ Q) B := by
        rw [Finset.disjoint_union_left]
        exact ⟨hd.mono_left (Finset.erase_subset _ _), hQB⟩
      have hA' : ∀ r : V → Bool, (∃ M ∈ A, ¬ LinClauseSat r M) → ∃ M ∈ A.erase R ∪ Q, ¬ LinClauseSat r M := by
        rintro r ⟨M, hM, hs⟩
        by_cases eM : M = R
        · subst eM
          obtain ⟨D, hD, hdd⟩ := hqq r hs
          exact ⟨D, Finset.mem_union_right _ hD, hdd⟩
        · exact ⟨M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨eM, hM⟩), hs⟩
      have := ih _ hd' hmem hh (hA' p hA) (hA' q hAq)
      omega
    obtain ⟨x, hxQ, hxB⟩ := Finset.not_disjoint_iff.1 hQB
    have hxN : x ∈ (A ∪ B).erase R := Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hxB, Finset.mem_union_right _ hxB⟩
    have h2 : ((A ∪ B).erase R ∪ Q).card + 1 ≤ ((A ∪ B).erase R).card + Q.card := by
      have hi := Finset.card_union_add_card_inter ((A ∪ B).erase R) Q
      have : 0 < ((A ∪ B).erase R ∩ Q).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hxN, hxQ⟩⟩
      omega
    by_cases hsub : Q ⊆ B
    · have hs : (A ∪ B).erase R ∪ Q = (A ∪ B).erase R := by
        apply Finset.union_eq_left.2
        intro y hy
        exact Finset.mem_erase.2 ⟨by rintro rfl; exact hRB (hsub hy), Finset.mem_union_right _ (hsub hy)⟩
      rw [hs] at hh hmem
      have h1 := plain F Pt H hπ _ K hmem hh
      omega
    · obtain ⟨y, hyQ, hyB⟩ := Finset.not_subset.1 hsub
      have hxy : x ≠ y := by rintro rfl; exact hyB hxB
      have eQ := pair_of hQ hxQ hyQ hxy
      have e : (A ∪ B).erase R ∪ Q = (A.erase R ∪ {y}) ∪ B := by
        rw [e0, eQ]
        ext z
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ((h | h) | (h | h))
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · subst h; exact Or.inr hxB
          · exact Or.inl (Or.inr h)
        · rintro ((h | h) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl (Or.inr h)
      have hd' : Disjoint (A.erase R ∪ {y}) B := by
        rw [Finset.disjoint_union_left]
        exact ⟨hd.mono_left (Finset.erase_subset _ _), Finset.disjoint_singleton_left.2 hyB⟩
      have fin1 : 2 * K.card + 1 ≤ π.length + ((A ∪ B).erase R ∪ Q).card → 2 * K.card + 2 ≤ π.length + 1 + (A ∪ B).card := by
        intro h; omega
      have look : ∀ r : V → Bool, (∃ M ∈ A, ¬ LinClauseSat r M) → (∃ M ∈ A.erase R ∪ {y}, ¬ LinClauseSat r M) ∨ ¬ LinClauseSat r x := by
        rintro r ⟨M, hM, hs⟩
        by_cases eM : M = R
        · subst eM
          obtain ⟨D, hD, hdd⟩ := hqq r hs
          rw [eQ] at hD
          simp only [Finset.mem_insert, Finset.mem_singleton] at hD
          rcases hD with rfl | rfl
          · exact Or.inr hdd
          · exact Or.inl ⟨D, Finset.mem_union_right _ (Finset.mem_singleton_self _), hdd⟩
        · exact Or.inl ⟨M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨eM, hM⟩), hs⟩
      rcases look p hA with hl | hpx
      · apply fin1
        have hh' := hh; have hmem' := hmem
        rw [e] at hh' hmem' ⊢
        exact split F Pt H i p p' hp hp' hπ _ _ K hd' hmem' hh' hl hB
      rcases look q hAq with hl | hqx
      · apply fin1
        have hh' := hh; have hmem' := hmem
        rw [e] at hh' hmem' ⊢
        exact split F Pt H j q q' hq hq' hπ _ _ K hd' hmem' hh' hl hBq
      have hxN' : x ∈ (A ∪ B).erase R ∪ Q := Finset.mem_union_right _ hxQ
      have eX : ({x} : Finset (LinClause V)) ∪ ((A ∪ B).erase R ∪ Q).erase x = (A ∪ B).erase R ∪ Q := by
        rw [← Finset.insert_eq, Finset.insert_erase hxN']
      have dX : Disjoint ({x} : Finset (LinClause V)) (((A ∪ B).erase R ∪ Q).erase x) := by
        rw [Finset.disjoint_singleton_left]; exact Finset.notMem_erase _ _
      have inN : ∀ M ∈ B, M ≠ x → M ∈ ((A ∪ B).erase R ∪ Q).erase x := by
        intro M hM hMx
        exact Finset.mem_erase.2 ⟨hMx, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hM, Finset.mem_union_right _ hM⟩)⟩
      obtain ⟨M1, hM1, hs1⟩ := hB
      by_cases hx1 : M1 = x
      swap
      · apply fin1
        have hh' := hh; have hmem' := hmem
        rw [← eX] at hh' hmem' ⊢
        exact split F Pt H i p p' hp hp' hπ _ _ K dX hmem' hh' ⟨x, by simp, hpx⟩ ⟨M1, inN M1 hM1 hx1, hs1⟩
      obtain ⟨M2, hM2, hs2⟩ := hBq
      by_cases hx2 : M2 = x
      swap
      · apply fin1
        have hh' := hh; have hmem' := hmem
        rw [← eX] at hh' hmem' ⊢
        exact split F Pt H j q q' hq hq' hπ _ _ K dX hmem' hh' ⟨x, by simp, hqx⟩ ⟨M2, inN M2 hM2 hx2, hs2⟩
      subst hx1
      rw [hx2] at hs2
      rcases four hcov M1 hpx hqx hs1 hs2 with h | h
      · exact absurd (h ▸ hQm _ hxQ) hemp
      · exact fin1 (marked F Pt H hF hπ _ K hmem hh ⟨M1, hxN', h⟩)
  have stepA : ∀ {π : List (LinClause V)} (hπ : IsLinDerivation F π) (R : LinClause V) (A B : Finset (LinClause V)) (K : Finset ι) (p p' q q' : V → Bool),
      Pt i p → Pt i p' → Pt j q → Pt j q' → R ∈ F → R ∈ A → Disjoint A B → (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) →
      (∃ M ∈ A, ¬ LinClauseSat p M) → (∃ M ∈ A, ¬ LinClauseSat q M) → (∃ M ∈ B, ¬ LinClauseSat p' M) → (∃ M ∈ B, ¬ LinClauseSat q' M) →
      (∀ (A' : Finset (LinClause V)) (K' : Finset ι), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K' (A' ∪ B) → (∃ M ∈ A', ¬ LinClauseSat p M) → (∃ M ∈ A', ¬ LinClauseSat q M) →
        2 * K'.card + 2 ≤ π.length + (A' ∪ B).card) → 2 * K.card + 2 ≤ (R :: π).length + (A ∪ B).card := by
    intro π hπ R A B K p p' q q' hp hp' hq hq' hRF hRA hd hN hK hA hAq hB hBq ih
    obtain ⟨k0, hk0⟩ := H R hRF
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have h3 := Finset.card_erase_of_mem hRN
    have h4 := Finset.card_pos.2 ⟨R, hRN⟩
    rw [List.length_cons]
    have keep : ∀ (l : ι) (r' : V → Bool), Pt l r' → (∃ M ∈ B, ¬ LinClauseSat r' M) → k0 = l → 2 * K.card + 2 ≤ π.length + 1 + (A ∪ B).card := by
      rintro l r' hr' ⟨M, hM, hs⟩ rfl
      have hh : Hit Pt K ((A ∪ B).erase R) := by
        intro k hk
        by_cases hkk : k = k0
        · subst hkk
          exact ⟨r', hr', M, Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hM, Finset.mem_union_right _ hM⟩, hs⟩
        · exact hit_ax Pt hK k0 hk0 k (Finset.mem_erase.2 ⟨hkk, hk⟩)
      have := plain F Pt H hπ _ K (tl hN) hh
      omega
    by_cases hi : k0 = i
    · exact keep i p' hp' hB hi
    by_cases hj : k0 = j
    · exact keep j q' hq' hBq hj
    have e : (A ∪ B).erase R = A.erase R ∪ B := by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
    have hh := hit_ax Pt hK k0 hk0
    have hmem := tl hN
    rw [e] at hh hmem h3
    have hA' : ∃ M ∈ A.erase R, ¬ LinClauseSat p M := by
      obtain ⟨M, hM, hs⟩ := hA
      exact ⟨M, Finset.mem_erase.2 ⟨by rintro rfl; exact hs (hk0 i (Ne.symm hi) p hp), hM⟩, hs⟩
    have hAq' : ∃ M ∈ A.erase R, ¬ LinClauseSat q M := by
      obtain ⟨M, hM, hs⟩ := hAq
      exact ⟨M, Finset.mem_erase.2 ⟨by rintro rfl; exact hs (hk0 j (Ne.symm hj) q hq), hM⟩, hs⟩
    have := ih _ _ (hd.mono_left (Finset.erase_subset _ _)) hmem hh hA' hAq'
    have h5 := Finset.pred_card_le_card_erase (s := K) (a := k0)
    omega
  have hcov' : ∀ (v : V) (s : Bool), p' v = s ∨ q' v = s ∨ p v = s ∨ q v = s := by
    intro v s; rcases hcov v s with h | h | h | h <;> simp [h]
  induction hπ with
  | nil =>
    rintro _ A B K _ hN _ ⟨M, hM, _⟩ _ _ _
    have := hN M (Finset.mem_union_left _ hM)
    simp at this
  | @ax π C hπ hC ih =>
    intro hemp A B K hd hN hK hA hAq hB hBq
    have hemp' : ∅ ∉ π := fun h => hemp (List.mem_cons_of_mem _ h)
    by_cases hRA : C ∈ A
    · exact stepA hπ C A B K p p' q q' hp hp' hq hq' hC hRA hd hN hK hA hAq hB hBq (fun A' K' h1 h2 h3 h4 h5 => ih hemp' A' B K' h1 h2 h3 h4 h5 hB hBq)
    · by_cases hRB : C ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepA hπ C B A K p' p q' q hp' hp hq' hq hC hRB hd.symm hN hK hB hBq hA hAq (fun A' K' h1 h2 h3 h4 h5 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih hemp' A A' K' h1.symm h2 h3 hA hAq h4 h5
      · have := ih hemp' A B K hd (tln hN (by simp [hRA, hRB])) hK hA hAq hB hBq
        rw [List.length_cons]; omega
  | @res π C D R hπ hC hD hr ih =>
    intro hemp A B K hd hN hK hA hAq hB hBq
    have hemp' : ∅ ∉ π := fun h => hemp (List.mem_cons_of_mem _ h)
    have q1 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
    have q2 : ∀ M ∈ ({C, D} : Finset (LinClause V)), M ∈ π := by
      intro M h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl <;> assumption
    have q3 : ∀ a, ¬ LinClauseSat a R → ∃ E ∈ ({C, D} : Finset (LinClause V)), ¬ LinClauseSat a E := by
      intro a ha
      rcases snd_res hr a ha with h | h
      · exact ⟨C, by simp, h⟩
      · exact ⟨D, by simp, h⟩
    by_cases hRA : R ∈ A
    · exact stepR hπ R _ A B K p p' q q' hp hp' hq hq' hcov hemp' q1 q2 q3 hRA hd hN hK hA hAq hB hBq (fun A' h1 h2 h3 h4 h5 => ih hemp' A' B K h1 h2 h3 h4 h5 hB hBq)
    · by_cases hRB : R ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepR hπ R _ B A K p' p q' q hp' hp hq' hq hcov' hemp' q1 q2 q3 hRB hd.symm hN hK hB hBq hA hAq (fun A' h1 h2 h3 h4 h5 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih hemp' A A' K h1.symm h2 h3 hA hAq h4 h5
      · have := ih hemp' A B K hd (tln hN (by simp [hRA, hRB])) hK hA hAq hB hBq
        rw [List.length_cons]; omega
  | @weak π C D hπ hC hw ih =>
    intro hemp A B K hd hN hK hA hAq hB hBq
    have hemp' : ∅ ∉ π := fun h => hemp (List.mem_cons_of_mem _ h)
    have q1 : ({C} : Finset (LinClause V)).card ≤ 2 := by simp
    have q2 : ∀ M ∈ ({C} : Finset (LinClause V)), M ∈ π := by
      intro M h
      simp only [Finset.mem_singleton] at h
      subst h; exact hC
    have q3 : ∀ a, ¬ LinClauseSat a D → ∃ E ∈ ({C} : Finset (LinClause V)), ¬ LinClauseSat a E :=
      fun a ha => ⟨C, by simp, fun h => ha (hw a h)⟩
    by_cases hRA : D ∈ A
    · exact stepR hπ D _ A B K p p' q q' hp hp' hq hq' hcov hemp' q1 q2 q3 hRA hd hN hK hA hAq hB hBq (fun A' h1 h2 h3 h4 h5 => ih hemp' A' B K h1 h2 h3 h4 h5 hB hBq)
    · by_cases hRB : D ∈ B
      · rw [Finset.union_comm]
        rw [Finset.union_comm] at hN hK
        refine stepR hπ D _ B A K p' p q' q hp' hp hq' hq hcov' hemp' q1 q2 q3 hRB hd.symm hN hK hB hBq hA hAq (fun A' h1 h2 h3 h4 h5 => ?_)
        rw [Finset.union_comm] at h2 h3 ⊢
        exact ih hemp' A A' K h1.symm h2 h3 hA hAq h4 h5
      · have := ih hemp' A B K hd (tln hN (by simp [hRA, hRB])) hK hA hAq hB hBq
        rw [List.length_cons]; omega

include H in
theorem low2 [Fintype ι] [Nontrivial ι] (hF : ∀ R ∈ F, ∀ q ∈ R, q.1.card = 1) (hex : ∀ k, ∃ a, Pt k a)
    (hV : ∀ v : V, ∃ i j, ∃ p p' q q' : V → Bool, Pt i p ∧ Pt i p' ∧ Pt j q ∧ Pt j q' ∧ p v = true ∧ p' v = false ∧ q v = true ∧ q' v = false ∧
      ∀ (w : V) (s : Bool), p w = s ∨ q w = s ∨ p' w = s ∨ q' w = s)
    {π : List (LinClause V)} (hπ : IsLinDerivation F π) : ∅ ∈ π → 2 * Fintype.card ι + 1 ≤ π.length := by
  have nos : ∀ a : V → Bool, ¬ LinClauseSat a ∅ := by rintro a ⟨q, hq, _⟩; simp at hq
  have hc : (Finset.univ : Finset ι).card = Fintype.card ι := rfl
  induction hπ with
  | nil => intro h; simp at h
  | @ax π C hπ hC ih =>
    intro h
    rcases List.mem_cons.1 h with e | e
    · exfalso
      obtain ⟨k0, hk0⟩ := H C hC
      obtain ⟨k, hk⟩ : ∃ k : ι, k ≠ k0 := exists_ne k0
      obtain ⟨a, ha⟩ := hex k
      have := hk0 k hk a ha
      rw [← e] at this
      exact nos a this
    · have := ih e
      rw [List.length_cons]; omega
  | @res π C D R hπ hC hD hr ih =>
    intro h
    by_cases hin : ∅ ∈ π
    · have := ih hin
      rw [List.length_cons]; omega
    rcases List.mem_cons.1 h with e | e
    · have hu : ∀ a, ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := fun a => snd_res hr a (e ▸ nos a)
      have hit : Hit Pt Finset.univ ({C, D} : Finset (LinClause V)) := by
        intro k _
        obtain ⟨a, ha⟩ := hex k
        rcases hu a with h | h
        · exact ⟨a, ha, C, by simp, h⟩
        · exact ⟨a, ha, D, by simp, h⟩
      have hm : ∀ M ∈ ({C, D} : Finset (LinClause V)), M ∈ π := by
        intro M h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> assumption
      have c2 : ({C, D} : Finset (LinClause V)).card ≤ 2 := Finset.card_le_two
      obtain ⟨f, hfC, hfD, hR⟩ := hr
      rw [← e] at hR
      have hR := hR.symm
      rw [Finset.union_eq_empty] at hR
      have eC : C = {(f, false)} := by
        rw [← Finset.insert_erase hfC, hR.1]; rfl
      have eD : D = {(f, true)} := by
        rw [← Finset.insert_erase hfD, hR.2]; rfl
      have hdis : Disjoint ({C} : Finset (LinClause V)) {D} := by
        rw [Finset.disjoint_singleton, eC, eD]
        intro h
        have := Finset.singleton_injective h
        simp at this
      by_cases hf : f.card = 1
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hf
        obtain ⟨i, j, p, p', q, q', hp, hp', hq, hq', hv1, hv2, hv3, hv4, hcov⟩ := hV v
        have fC : ∀ r : V → Bool, r v = true → ¬ LinClauseSat r C := by
          intro r hr
          rw [eC]; rintro ⟨q, hq, hs⟩
          rw [Finset.mem_singleton] at hq; subst hq
          simp [LinEqSat, hr, Finset.filter_singleton] at hs
        have fD : ∀ r : V → Bool, r v = false → ¬ LinClauseSat r D := by
          intro r hr
          rw [eD]; rintro ⟨q, hq, hs⟩
          rw [Finset.mem_singleton] at hq; subst hq
          simp [LinEqSat, hr, Finset.filter_singleton] at hs
        have hs := s2 F Pt H hF i j p p' q q' hp hp' hq hq' hcov hπ hin {C} {D} Finset.univ hdis
          (by rw [← Finset.insert_eq]; exact hm) (by rw [← Finset.insert_eq]; exact hit)
          ⟨C, by simp, fC p hv1⟩ ⟨C, by simp, fC q hv3⟩ ⟨D, by simp, fD p' hv2⟩ ⟨D, by simp, fD q' hv4⟩
        rw [← Finset.insert_eq, hc] at hs
        rw [List.length_cons]; omega
      · have hs := dm F Pt H hF hπ {C} {D} Finset.univ hdis
          (by rw [← Finset.insert_eq]; exact hm) (by rw [← Finset.insert_eq]; exact hit)
          ⟨C, by simp, (f, false), hfC, hf⟩ ⟨D, by simp, (f, true), hfD, hf⟩
        rw [← Finset.insert_eq, hc] at hs
        rw [List.length_cons]; omega
    · exact absurd e hin
  | @weak π C D hπ hC hw ih =>
    intro h
    by_cases hin : ∅ ∈ π
    · have := ih hin
      rw [List.length_cons]; omega
    rcases List.mem_cons.1 h with e | e
    · have hno : ∀ a, ¬ LinClauseSat a C := fun a h => nos a (e ▸ hw a h)
      have hit : Hit Pt Finset.univ ({C} : Finset (LinClause V)) := by
        intro k _
        obtain ⟨a, ha⟩ := hex k
        exact ⟨a, ha, C, by simp, hno a⟩
      obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.2 (show C ≠ ∅ by rintro rfl; exact hin hC)
      have hcard : q.1.card ≠ 1 := by
        intro h1
        obtain ⟨v, hv⟩ := Finset.card_eq_one.1 h1
        refine hno (fun _ => q.2) ⟨q, hq, ?_⟩
        unfold LinEqSat
        rw [hv, Finset.filter_singleton]
        cases q.2 <;> simp
      have := marked F Pt H hF hπ {C} Finset.univ (by simpa using hC) hit ⟨C, by simp, q, hq, hcard⟩
      rw [hc, Finset.card_singleton] at this
      rw [List.length_cons]; omega
    · exact absurd e hin

end gen

abbrev W := Fin 3 × Fin 2
def asg (m : ℕ) : W → Bool := fun v => m.testBit (2 * v.1.val + v.2.val)
def ptl : List (List ℕ) := [[24, 36], [18, 33], [6, 9], [37], [26], [25], [38], [22], [41]]
def pts (k : Fin 9) : List ℕ := ptl.getD k.val []
def Pt (k : Fin 9) (a : W → Bool) : Prop := ∃ m ∈ pts k, a = asg m

def satb (a : W → Bool) (C : LinClause W) : Bool :=
  decide (∃ q ∈ C, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true))
theorem satb_sat {a : W → Bool} {C : LinClause W} (h : satb a C = true) : LinClauseSat a C := by
  unfold satb at h
  rw [decide_eq_true_eq] at h
  exact h

theorem factP : ∀ i : Fin 3, ∃ k0 : Fin 9, ∀ k, k ≠ k0 → ∀ m ∈ pts k,
    satb (asg m) (linOfClause (Finset.univ.image (fun j : Fin 2 => ((i, j), true)))) = true := by decide +kernel
theorem factH : ∀ (i i' : Fin 3) (j : Fin 2), i ≠ i' → ∃ k0 : Fin 9, ∀ k, k ≠ k0 → ∀ m ∈ pts k,
    satb (asg m) (linOfClause {((i, j), false), ((i', j), false)}) = true := by decide +kernel
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem factV : ∀ v : W, ∃ i j : Fin 9, ∃ p ∈ pts i, ∃ p' ∈ pts i, ∃ q ∈ pts j, ∃ q' ∈ pts j, asg p v = true ∧ asg p' v = false ∧ asg q v = true ∧ asg q' v = false ∧
    ∀ (w : W) (s : Bool), asg p w = s ∨ asg q w = s ∨ asg p' w = s ∨ asg q' w = s := by decide +kernel
theorem factE : ∀ k : Fin 9, pts k ≠ [] := by decide +kernel

def FF : Set (LinClause W) := (fun C => linOfClause C) '' PHP 3 2

theorem HH : ∀ R ∈ FF, ∃ k0 : Fin 9, ∀ k, k ≠ k0 → ∀ a, Pt k a → LinClauseSat a R := by
  rintro R ⟨C, hC, rfl⟩
  rcases hC with ⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩
  · obtain ⟨k0, h⟩ := factP i
    exact ⟨k0, fun k hk a ⟨m, hm, e⟩ => e ▸ satb_sat (h k hk m hm)⟩
  · obtain ⟨k0, h⟩ := factH i i' j hne
    exact ⟨k0, fun k hk a ⟨m, hm, e⟩ => e ▸ satb_sat (h k hk m hm)⟩

theorem hF1 : ∀ R ∈ FF, ∀ q ∈ R, q.1.card = 1 := by
  rintro R ⟨C, hC, rfl⟩ q hq
  simp only [linOfClause, Finset.mem_image] at hq
  obtain ⟨l, _, rfl⟩ := hq
  simp

theorem exP (k : Fin 9) : ∃ a, Pt k a := by
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ (factE k)
  exact ⟨_, m, hm, rfl⟩

theorem hVV (v : W) : ∃ i j, ∃ p p' q q' : W → Bool, Pt i p ∧ Pt i p' ∧ Pt j q ∧ Pt j q' ∧ p v = true ∧ p' v = false ∧ q v = true ∧ q' v = false ∧
      ∀ (w : W) (s : Bool), p w = s ∨ q w = s ∨ p' w = s ∨ q' w = s := by
  obtain ⟨i, j, p, h1, p', h2, q, h3, q', h4, h5, h6, h7, h8, h9⟩ := factV v
  exact ⟨i, j, asg p, asg p', asg q, asg q', ⟨p, h1, rfl⟩, ⟨p', h2, rfl⟩, ⟨q, h3, rfl⟩, ⟨q', h4, rfl⟩, h5, h6, h7, h8, h9⟩

end PEqualNP.Outside.L_pcx_114

theorem PEqualNP.Outside.L_pcx_114 : ¬ (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 3 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 3 2) π ∧ π.length ≤ 18) := by
  rintro ⟨π, ⟨h1, h2⟩, h3⟩
  have := PEqualNP.Outside.L_pcx_114.low2 PEqualNP.Outside.L_pcx_114.FF PEqualNP.Outside.L_pcx_114.Pt PEqualNP.Outside.L_pcx_114.HH PEqualNP.Outside.L_pcx_114.hF1 PEqualNP.Outside.L_pcx_114.exP PEqualNP.Outside.L_pcx_114.hVV h1 h2
  rw [Fintype.card_fin] at this
  omega
