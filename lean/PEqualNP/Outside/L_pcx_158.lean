import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_158

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

end gen

theorem lin_inj {V : Type} [DecidableEq V] : Function.Injective (fun l : V × Bool => (({l.1} : Finset V), l.2)) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  simp only [Prod.mk.injEq, Finset.singleton_inj] at h
  exact Prod.ext h.1 h.2

theorem embed {V : Type} [DecidableEq V] (F : Set (Clause V)) {π : List (Clause V)} (h : IsDerivation F π) :
    IsLinDerivation ((fun C => linOfClause C) '' F) (π.map linOfClause) := by
  induction h with
  | nil => exact IsLinDerivation.nil
  | @ax π C _ hC ih => exact IsLinDerivation.ax ih ⟨C, hC, rfl⟩
  | @res π C D R _ hC hD hr ih =>
    refine IsLinDerivation.res ih (List.mem_map.2 ⟨D, hD, rfl⟩) (List.mem_map.2 ⟨C, hC, rfl⟩) ?_
    obtain ⟨v, h1, h2, rfl⟩ := hr
    refine ⟨{v}, Finset.mem_image.2 ⟨(v, false), h2, rfl⟩, Finset.mem_image.2 ⟨(v, true), h1, rfl⟩, ?_⟩
    unfold linOfClause
    rw [Finset.image_union, Finset.image_erase lin_inj, Finset.image_erase lin_inj, Finset.union_comm]

abbrev W := Fin 5 × Fin 4
def asg (m : ℕ) : W → Bool := fun v => m.testBit (4 * v.1.val + v.2.val)
def ptl : List (List ℕ) := [[164880, 540960], [83970, 295425], [528420, 540690], [262680, 524865], [8520, 8580], [164881, 272401], [268322, 295202], [137284, 164164], [136328, 266888], [164161, 295201], [98882, 266882], [136324, 533524], [268328, 272408], [266881, 268321], [272402, 533522], [82564, 147844], [98888, 99368], [75841, 84001], [137282, 149522], [268324, 295204], [529448, 532808], [164116, 270616], [295457, 541217], [74824, 529474], [137348, 149633], [136216, 529426], [74792, 532772], [84034, 147784], [164228, 295553], [75796, 98836], [164132, 164897], [266824, 270664], [533633, 541058], [266626, 528706], [270977, 533057], [148609, 541729], [165908, 296978], [74056, 82306], [148097, 164417], [267304, 271384], [530498, 534593], [70696, 71716], [140312, 141377], [278914, 279169], [557348, 558098]]
def pts (k : Fin 45) : List ℕ := ptl.getD k.val []
def Pt (k : Fin 45) (a : W → Bool) : Prop := ∃ m ∈ pts k, a = asg m

def satb (a : W → Bool) (C : LinClause W) : Bool :=
  decide (∃ q ∈ C, (Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true))
theorem satb_sat {a : W → Bool} {C : LinClause W} (h : satb a C = true) : LinClauseSat a C := by
  unfold satb at h
  rw [decide_eq_true_eq] at h
  exact h

theorem factP : ∀ i : Fin 5, ∃ k0 : Fin 45, ∀ k, k ≠ k0 → ∀ m ∈ pts k,
    satb (asg m) (linOfClause (Finset.univ.image (fun j : Fin 4 => ((i, j), true)))) = true := by decide +kernel
theorem factH : ∀ (i i' : Fin 5) (j : Fin 4), i ≠ i' → ∃ k0 : Fin 45, ∀ k, k ≠ k0 → ∀ m ∈ pts k,
    satb (asg m) (linOfClause {((i, j), false), ((i', j), false)}) = true := by decide +kernel
theorem factV : ∀ v : W, ∃ i : Fin 45, ∃ m ∈ pts i, ∃ m' ∈ pts i, asg m v = true ∧ asg m' v = false := by decide +kernel
theorem factE : ∀ k : Fin 45, pts k ≠ [] := by decide +kernel

def FF : Set (LinClause W) := (fun C => linOfClause C) '' PHP 5 4

theorem HH : ∀ R ∈ FF, ∃ k0 : Fin 45, ∀ k, k ≠ k0 → ∀ a, Pt k a → LinClauseSat a R := by
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

theorem exP (k : Fin 45) : ∃ a, Pt k a := by
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ (factE k)
  exact ⟨_, m, hm, rfl⟩

theorem hVV (v : W) : ∃ i, ∃ p p' : W → Bool, Pt i p ∧ Pt i p' ∧ p v = true ∧ p' v = false := by
  obtain ⟨i, m, h1, m', h2, h3, h4⟩ := factV v
  exact ⟨i, asg m, asg m', ⟨m, h1, rfl⟩, ⟨m', h2, rfl⟩, h3, h4⟩

end PEqualNP.Outside.L_pcx_158

theorem PEqualNP.Outside.L_pcx_158 : ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 89) := by
  rintro ⟨π, ⟨h1, h2⟩, h3⟩
  have := PEqualNP.Outside.L_pcx_158.low PEqualNP.Outside.L_pcx_158.FF PEqualNP.Outside.L_pcx_158.Pt PEqualNP.Outside.L_pcx_158.HH PEqualNP.Outside.L_pcx_158.hF1 PEqualNP.Outside.L_pcx_158.exP PEqualNP.Outside.L_pcx_158.hVV
    (PEqualNP.Outside.L_pcx_158.embed _ h1) (List.mem_map.2 ⟨∅, h2, rfl⟩)
  rw [Fintype.card_fin, List.length_map] at this
  omega
