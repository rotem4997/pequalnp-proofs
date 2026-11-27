import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_196

open PEqualNP.ProofComplexity

theorem and_intro_sound {V : Type} [DecidableEq V] {C D R : KLine V}
    (h : IsResKAndIntro C D R) (a : V → Bool) (hC : KLineSat a C) (hD : KLineSat a D) :
    KLineSat a R := by
  obtain ⟨T, U, _, _, rfl⟩ := h
  obtain ⟨P, hP, hp⟩ := hC
  obtain ⟨Q, hQ, hq⟩ := hD
  by_cases e : P = T
  · subst P
    by_cases f : Q = U
    · subst Q
      refine ⟨T ∪ U, by simp, ?_⟩
      intro l hl
      rcases Finset.mem_union.mp hl with h | h
      · exact hp l h
      · exact hq l h
    · exact ⟨Q, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨f,hQ⟩)), hq⟩
  · exact ⟨P, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hP⟩)), hp⟩

theorem and_elim_sound {V : Type} [DecidableEq V] {C R : KLine V}
    (h : IsResKAndElim C R) (a : V → Bool) (hC : KLineSat a C) : KLineSat a R := by
  obtain ⟨T, U, _, hUT, _, rfl⟩ := h
  obtain ⟨P, hP, hp⟩ := hC
  by_cases e : P = T
  · subst P
    exact ⟨U, by simp, fun l hl => hp l (hUT hl)⟩
  · exact ⟨P, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hP⟩), hp⟩

theorem cut_sound {V : Type} [DecidableEq V] {C D R : KLine V}
    (h : IsResKCut C D R) (a : V → Bool) (hC : KLineSat a C) (hD : KLineSat a D) : KLineSat a R := by
  obtain ⟨T, _, _, _, rfl⟩ := h
  obtain ⟨P, hP, hp⟩ := hC
  obtain ⟨Q, hQ, hq⟩ := hD
  by_cases e : P = T
  · subst P
    refine ⟨Q, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hQ,?_⟩), hq⟩
    intro hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
    have h1 := hp l hl
    have h2 := hq (l.1, !l.2) (Finset.mem_singleton_self _)
    simp only at h2
    rw [h1] at h2
    revert h2
    cases l.2 <;> decide
  · exact ⟨P, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hP⟩), hp⟩

def Good {V : Type} (F : Set (KLine V)) : List (KLine V) → Prop
  | [] => True
  | R :: π => Good F π ∧ (R ∈ F ∨ ∃ C ∈ π, ∃ D ∈ π, ∀ a, ¬ KLineSat a R → ¬ KLineSat a C ∨ ¬ KLineSat a D)

theorem good {V : Type} [DecidableEq V] {F : Set (KLine V)} {π : List (KLine V)}
    (h : IsResKDerivation 2 F π) : Good F π := by
  induction h with
  | nil => trivial
  | ax _ hC _ ih => exact ⟨ih, .inl hC⟩
  | weak _ hm hw _ ih =>
    refine ⟨ih, .inr ⟨_, hm, _, hm, ?_⟩⟩
    intro a hD
    exact .inl (fun ⟨T,hT,hs⟩ => hD ⟨T,hw hT,hs⟩)
  | @andIntro π C D R _ hC hD hr _ ih =>
    refine ⟨ih, .inr ⟨_,hC,_,hD,?_⟩⟩
    intro a hR
    by_cases h : KLineSat a C
    · exact .inr (fun h' => hR (and_intro_sound hr a h h'))
    · exact .inl h
  | andElim _ hC hr ih =>
    exact ⟨ih, .inr ⟨_,hC,_,hC,fun a hR => .inl (fun h => hR (and_elim_sound hr a h))⟩⟩
  | @cut π C D R _ hC hD hr ih =>
    refine ⟨ih, .inr ⟨_,hC,_,hD,?_⟩⟩
    intro a hR
    by_cases h : KLineSat a C
    · exact .inr (fun h' => hR (cut_sound hr a h h'))
    · exact .inl h

theorem resK_lines_card {V : Type} [DecidableEq V] {k : ℕ} {F : Set (KLine V)} {π : List (KLine V)}
    (h : IsResKDerivation k F π) : ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | @andElim π C R _ hC hel ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hLR | hL
    · obtain ⟨T, T', hT, hsub, -, hR⟩ := hel
      rw [hLR, hR]
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact ih C hC S (Finset.mem_of_mem_erase hS)
      · rw [Finset.mem_singleton.mp hS]
        exact (Finset.card_le_card hsub).trans (ih C hC T hT)
    · exact ih L hL
  | @cut π C D R _ hC hD hcut ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hLR | hL
    · obtain ⟨T, -, -, -, hR⟩ := hcut
      rw [hLR, hR]
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact ih C hC S (Finset.mem_of_mem_erase hS)
      · exact ih D hD S (Finset.mem_sdiff.mp hS).1
    · exact ih L hL

section gen
variable {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι] (F : Set (KLine V)) (Pt : ι → (V → Bool) → Prop)
  (H : ∀ R ∈ F, ∃ k0 : ι, ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R)

def Hit (K : Finset ι) (N : Finset (KLine V)) : Prop := ∀ k ∈ K, ∃ a, Pt k a ∧ ∃ R ∈ N, ¬ KLineSat a R

theorem hit_step {K : Finset ι} {N Q : Finset (KLine V)} {R : KLine V} (h : Hit Pt K N)
    (hq : ∀ a, ¬ KLineSat a R → ∃ D ∈ Q, ¬ KLineSat a D) : Hit Pt K (N.erase R ∪ Q) := by
  intro k hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  by_cases e : M = R
  · subst e
    obtain ⟨D, hD, hd⟩ := hq a hs
    exact ⟨a, ha, D, Finset.mem_union_right _ hD, hd⟩
  · exact ⟨a, ha, M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hM⟩), hs⟩

theorem hit_ax {K : Finset ι} {N : Finset (KLine V)} {R : KLine V} (h : Hit Pt K N) (k0 : ι)
    (hk0 : ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R) : Hit Pt (K.erase k0) (N.erase R) := by
  intro k hk
  obtain ⟨hne, hk⟩ := Finset.mem_erase.1 hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  refine ⟨a, ha, M, Finset.mem_erase.2 ⟨?_, hM⟩, hs⟩
  rintro rfl
  exact hs (hk0 k hne a ha)

theorem card_step (N Q : Finset (KLine V)) (R : KLine V) (hR : R ∈ N) : (N.erase R ∪ Q).card + 1 ≤ N.card + Q.card := by
  have h1 := Finset.card_union_le (N.erase R) Q
  have h2 := Finset.card_erase_of_mem hR
  have h3 := Finset.card_pos.2 ⟨R, hR⟩
  omega

theorem tl {N : Finset (KLine V)} {R : KLine V} {π : List (KLine V)} (h : ∀ M ∈ N, M ∈ R :: π) : ∀ M ∈ N.erase R, M ∈ π := by
  intro M hM
  obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hM
  rcases List.mem_cons.1 (h M h2) with e | e
  · exact absurd e h1
  · exact e

theorem tln {N : Finset (KLine V)} {R : KLine V} {π : List (KLine V)} (h : ∀ M ∈ N, M ∈ R :: π) (hR : R ∉ N) : ∀ M ∈ N, M ∈ π := by
  intro M hM
  rcases List.mem_cons.1 (h M hM) with e | e
  · subst e; exact absurd hM hR
  · exact e

include H in
theorem plain {π : List (KLine V)} (hπ : Good F π) : ∀ (N : Finset (KLine V)) (K : Finset ι),
    (∀ M ∈ N, M ∈ π) → Hit Pt K N → 2 * K.card ≤ π.length + N.card := by
  induction π with
  | nil =>
    intro N K hN hK
    have : K = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨_, _, M, hM, _⟩ := hK k hk
      have := hN M hM
      simp at this
    simp [this]
  | cons R π ih =>
    obtain ⟨hπ, hrule⟩ := hπ
    have ih := ih hπ
    rcases hrule with hC | ⟨C,hC,D,hD,hr⟩
    · intro N K hN hK
      by_cases hR : R ∈ N
      · obtain ⟨k0, hk0⟩ := H R hC
        have := ih (N.erase R) (K.erase k0) (tl hN) (hit_ax Pt hK k0 hk0)
        have h2 := Finset.card_erase_of_mem hR
        have h3 := Finset.card_pos.2 ⟨R, hR⟩
        have h4 := Finset.pred_card_le_card_erase (s := K) (a := k0)
        rw [List.length_cons]
        omega
      · have := ih N K (tln hN hR) hK
        rw [List.length_cons]; omega
    · intro N K hN hK
      by_cases hR : R ∈ N
      · have hh := hit_step Pt (Q := {C, D}) hK (R := R) (fun a ha => by
          rcases hr a ha with h | h
          · exact ⟨C, by simp, h⟩
          · exact ⟨D, by simp, h⟩)
        have := ih _ K (fun M hM => by
          rcases Finset.mem_union.1 hM with h | h
          · exact tl hN M h
          · simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with rfl | rfl <;> assumption) hh
        have h2 := card_step N {C, D} R hR
        have h3 : ({C, D} : Finset (KLine V)).card ≤ 2 := Finset.card_le_two
        rw [List.length_cons]; omega
      · have := ih N K (tln hN hR) hK
        rw [List.length_cons]; omega

include H in
theorem split (i : ι) (p p' : V → Bool) (hp : Pt i p) (hp' : Pt i p') {π : List (KLine V)} (hπ : Good F π) :
    ∀ (A B : Finset (KLine V)) (K : Finset ι), Disjoint A B → (∀ M ∈ A ∪ B, M ∈ π) → Hit Pt K (A ∪ B) →
      (∃ M ∈ A, ¬ KLineSat p M) → (∃ M ∈ B, ¬ KLineSat p' M) → 2 * K.card + 1 ≤ π.length + (A ∪ B).card := by
  -- one step on the part that holds the head
  have stepR : ∀ {π : List (KLine V)} (hπ : Good F π) (R : KLine V) (Q A B : Finset (KLine V)) (K : Finset ι) (r : V → Bool),
      Q.card ≤ 2 → (∀ M ∈ Q, M ∈ π) → (∀ a, ¬ KLineSat a R → ∃ D ∈ Q, ¬ KLineSat a D) → R ∈ A → Disjoint A B →
      (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ¬ KLineSat r M) →
      ((∀ (A' : Finset (KLine V)), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K (A' ∪ B) → (∃ M ∈ A', ¬ KLineSat r M) →
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
      have hA' : ∃ M ∈ A.erase R ∪ Q, ¬ KLineSat r M := by
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
  have stepA : ∀ {π : List (KLine V)} (hπ : Good F π) (R : KLine V) (A B : Finset (KLine V)) (K : Finset ι) (r r' : V → Bool),
      Pt i r → Pt i r' → R ∈ F → R ∈ A → Disjoint A B → (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ¬ KLineSat r M) → (∃ M ∈ B, ¬ KLineSat r' M) →
      (∀ (A' : Finset (KLine V)) (K' : Finset ι), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K' (A' ∪ B) → (∃ M ∈ A', ¬ KLineSat r M) →
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
      have hA' : ∃ M ∈ A.erase R, ¬ KLineSat r M := by
        obtain ⟨M, hM, hs⟩ := hA
        exact ⟨M, Finset.mem_erase.2 ⟨by rintro rfl; exact hs (hk0 i (Ne.symm hi) r hr), hM⟩, hs⟩
      have := ih _ _ (hd.mono_left (Finset.erase_subset _ _)) hmem hh hA'
      have h5 := Finset.pred_card_le_card_erase (s := K) (a := k0)
      omega
  induction π with
  | nil =>
    rintro A B K _ hN _ ⟨M, hM, _⟩ _
    have := hN M (Finset.mem_union_left _ hM)
    simp at this
  | cons R π ih =>
    obtain ⟨hπ, hrule⟩ := hπ
    have ih := ih hπ
    rcases hrule with hC | ⟨C,hC,D,hD,hr⟩
    · intro A B K hd hN hK hA hB
      by_cases hRA : R ∈ A
      · exact stepA hπ R A B K p p' hp hp' hC hRA hd hN hK hA hB (fun A' K' h1 h2 h3 h4 => ih A' B K' h1 h2 h3 h4 hB)
      · by_cases hRB : R ∈ B
        · rw [Finset.union_comm]
          rw [Finset.union_comm] at hN hK
          refine stepA hπ R B A K p' p hp' hp hC hRB hd.symm hN hK hB hA (fun A' K' h1 h2 h3 h4 => ?_)
          rw [Finset.union_comm] at h2 h3 ⊢
          exact ih A A' K' h1.symm h2 h3 hA h4
        · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
          rw [List.length_cons]; omega
    · intro A B K hd hN hK hA hB
      have q1 : ({C, D} : Finset (KLine V)).card ≤ 2 := Finset.card_le_two
      have q2 : ∀ M ∈ ({C, D} : Finset (KLine V)), M ∈ π := by
        intro M h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> assumption
      have q3 : ∀ a, ¬ KLineSat a R → ∃ E ∈ ({C, D} : Finset (KLine V)), ¬ KLineSat a E := by
        intro a ha
        rcases hr a ha with h | h
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

end gen

def Big {V : Type} (S : Fin 5 → (V → Bool) → Prop) (R : KLine V) : Prop :=
  ∀ i a, S i a → ¬ KLineSat a R

theorem walk {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι]
    (F : Set (KLine V)) (Pt : ι → (V → Bool) → Prop)
    (H : ∀ R ∈ F, ∃ k0 : ι, ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R)
    (S : Fin 5 → (V → Bool) → Prop) (tag : Fin 5 → ι)
    (track : ∀ i a, S i a → Pt (tag i) a)
    (smallAx : ∀ R ∈ F, ¬ Big S R)
    (overlap : ∀ C D : KLine V, (∀ T ∈ C, T.card ≤ 2) → (∀ T ∈ D, T.card ≤ 2) →
      ¬ Big S C → ¬ Big S D → ∃ i a b, S i a ∧ S i b ∧ KLineSat a C ∧ KLineSat b D)
    {π : List (KLine V)} (hπ : Good F π) (hw : ∀ C ∈ π, ∀ T ∈ C, T.card ≤ 2) :
    ∀ (N : Finset (KLine V)) (K : Finset ι), (∀ M ∈ N, M ∈ π) → Hit Pt K N →
      (∃ M ∈ N, Big S M) → 2 * K.card + 1 ≤ π.length + N.card := by
  classical
  induction π with
  | nil =>
    rintro N K hn _ ⟨M, hm, _⟩
    have := hn M hm
    simp at this
  | cons R π ih =>
    obtain ⟨hπ, rule⟩ := hπ
    have hwt : ∀ C ∈ π, ∀ T ∈ C, T.card ≤ 2 := fun C h => hw C (List.mem_cons_of_mem R h)
    have ih := ih hπ hwt
    rintro N K hn hit ⟨M,hM,big⟩
    by_cases hR : R ∈ N
    · rcases rule with ax | ⟨C,hC,D,hD,hrule⟩
      · obtain ⟨k0,h0⟩ := H R ax
        have ne : M ≠ R := by rintro rfl; exact smallAx M ax big
        have h1 := ih (N.erase R) (K.erase k0) (tl hn) (hit_ax Pt hit k0 h0)
          ⟨M, Finset.mem_erase.mpr ⟨ne,hM⟩, big⟩
        have := Finset.card_erase_of_mem hR
        have := Finset.card_pos.mpr ⟨R,hR⟩
        have := Finset.pred_card_le_card_erase (s := K) (a := k0)
        rw [List.length_cons]
        omega
      · let Q : Finset (KLine V) := {C,D}
        let F' := N.erase R ∪ Q
        have hCQ : C ∈ Q := by simp [Q]
        have hDQ : D ∈ Q := by simp [Q]
        have hc' : C ∈ F' := Finset.mem_union_right _ hCQ
        have hd' : D ∈ F' := Finset.mem_union_right _ hDQ
        have qfail : ∀ a, ¬ KLineSat a R → ∃ E ∈ Q, ¬ KLineSat a E := by
          intro a ha
          rcases hrule a ha with hc | hd
          · exact ⟨C,hCQ,hc⟩
          · exact ⟨D,hDQ,hd⟩
        have hhit : Hit Pt K F' := hit_step Pt hit qfail
        have hmem : ∀ E ∈ F', E ∈ π := by
          intro E he
          rcases Finset.mem_union.mp he with e | e
          · exact tl hn _ e
          · simp only [Q, Finset.mem_insert, Finset.mem_singleton] at e
            rcases e with rfl | rfl <;> assumption
        have cards : F'.card + 1 ≤ N.card + Q.card := card_step N Q R hR
        have two : Q.card ≤ 2 := Finset.card_le_two
        suffices hgoal : 2 * K.card + 1 ≤ π.length + F'.card by
          rw [List.length_cons]
          omega
        by_cases e : M = R
        · subst M
          by_cases bc : Big S C
          · exact ih F' K hmem hhit ⟨C,hc',bc⟩
          by_cases bd : Big S D
          · exact ih F' K hmem hhit ⟨D,hd',bd⟩
          obtain ⟨i,a,b,ha,hb,sa,sb⟩ := overlap C D (hwt _ hC) (hwt _ hD) bc bd
          have na : ¬ KLineSat a D := (hrule a (big i a ha)).resolve_left (not_not_intro sa)
          have nb : ¬ KLineSat b C := (hrule b (big i b hb)).resolve_right (not_not_intro sb)
          have ne : D ≠ C := by rintro rfl; exact na sa
          let A : Finset (KLine V) := {C}
          let B := F'.erase C
          have hAB : A ∪ B = F' := by
            ext L
            by_cases e : L = C <;> simp_all [A,B]
          have dj : Disjoint A B := by simp [A,B]
          have hret := split F Pt H (tag i) b a (track i b hb) (track i a ha) hπ A B K dj
            (by rwa [hAB]) (by rwa [hAB]) ⟨C,by simp [A],nb⟩
            ⟨D,Finset.mem_erase.mpr ⟨ne,hd'⟩,na⟩
          rwa [hAB] at hret
        · exact ih F' K hmem hhit
            ⟨M,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hM⟩),big⟩
    · have := ih N K (tln hn hR) hit ⟨M,hM,big⟩
      rw [List.length_cons]
      omega

abbrev W := Fin 5 × Fin 4

def asg (m : ℕ) : W → Bool := fun v => m.testBit (4 * v.1.val + v.2.val)

def groups : List (List ℕ) := [[541200, 295440, 533520, 164880, 272400, 149520, 540960, 295200, 529440, 99360, 268320, 84000, 532800, 164160, 528960, 98880, 137280, 75840, 270720, 147840, 266880, 82560, 136320, 74880], [541185, 295425, 533505, 164865, 272385, 149505, 540930, 295170, 529410, 99330, 268290, 83970, 532740, 164100, 528900, 98820, 137220, 75780, 270600, 147720, 266760, 82440, 136200, 74760], [540705, 294945, 532545, 163905, 270465, 147585, 540690, 294930, 528450, 98370, 266370, 82050, 532500, 163860, 528420, 98340, 135300, 73860, 270360, 147480, 266280, 81960, 135240, 73800], [525345, 264225, 524865, 133185, 262785, 132225, 525330, 264210, 524610, 67650, 262530, 66690, 524820, 133140, 524580, 67620, 131460, 66180, 262680, 132120, 262440, 66600, 131400, 66120], [33825, 18465, 33345, 10305, 17025, 9345, 33810, 18450, 33090, 6210, 16770, 5250, 33300, 10260, 33060, 6180, 8580, 4740, 16920, 9240, 16680, 5160, 8520, 4680], [541201], [540962], [532804], [270728], [540961], [541202], [533524], [272408], [540946], [541217], [533569], [272513], [529441], [533522], [541204], [295448], [529426], [533537], [541249], [295553], [528706], [533057], [541729], [296993], [99361], [164882], [295444], [541208], [99346], [164897], [295489], [541313], [98626], [164417], [295969], [542753], [71746], [141377], [280609], [558113]]

def pts (k : Fin 45) : List ℕ := groups.getD k.val []

def Pt (k : Fin 45) (a : W → Bool) : Prop := ∃ m ∈ pts k, a = asg m

def kP (i : Fin 5) : Fin 45 := ⟨i.val, by omega⟩

def kH (i j : Fin 5) (h : Fin 4) : Fin 45 :=
  ⟨(5 + 4 * (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val) + h.val) % 45,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 12000 in
theorem factP : ∀ (i : Fin 5) (k : Fin 45), k ≠ kP i → ∀ m ∈ pts k,
    ∃ j : Fin 4, asg m (i,j) = true := by decide +kernel

set_option maxRecDepth 12000 in
theorem factH : ∀ (i j : Fin 5) (h : Fin 4), i ≠ j → ∀ k : Fin 45, k ≠ kH i j h →
    ∀ m ∈ pts k, asg m (i,h) = false ∨ asg m (j,h) = false := by decide +kernel

theorem inhabitedPts : ∀ k : Fin 45, pts k ≠ [] := by decide +kernel

def FF : Set (KLine W) := (fun C => kLineOfClause C) '' PHP 5 4

theorem liftSat {C : Clause W} {a : W → Bool} (h : ClauseSat a C) : KLineSat a (kLineOfClause C) := by
  obtain ⟨l,hl,hs⟩ := h
  exact ⟨{l}, Finset.mem_image_of_mem _ hl, fun x hx => (Finset.mem_singleton.mp hx) ▸ hs⟩

theorem HH : ∀ R ∈ FF, ∃ k0 : Fin 45, ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R := by
  rintro R ⟨C,hC,rfl⟩
  rcases hC with ⟨i,rfl⟩ | ⟨i,j,h,hij,rfl⟩
  · refine ⟨kP i, ?_⟩
    rintro k hk _ ⟨m,hm,rfl⟩
    obtain ⟨j,hj⟩ := factP i k hk m hm
    exact liftSat ⟨((i,j),true), Finset.mem_image_of_mem _ (Finset.mem_univ j), hj⟩
  · refine ⟨kH i j h, ?_⟩
    rintro k hk _ ⟨m,hm,rfl⟩
    rcases factH i j h hij k hk m hm with q | q
    · exact liftSat ⟨((i,h),false), by simp, q⟩
    · exact liftSat ⟨((j,h),false), by simp, q⟩

def S (i : Fin 5) := Pt (kP i)

def admits (T : KTerm W) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => (pts (kP i)).any (fun m => decide (∀ l ∈ T, asg m l.1 = l.2)) = true)

def owner (m : ℕ) (h : Fin 4) : Fin 5 :=
  if asg m (0,h) then 0 else if asg m (1,h) then 1 else if asg m (2,h) then 2
  else if asg m (3,h) then 3 else 4

def moved (i : Fin 5) (m : ℕ) (h : Fin 4) : ℕ :=
  m ^^^ 2 ^ (4*i.val + h.val) ^^^ 2 ^ (4*(owner m h).val + h.val)

set_option maxRecDepth 12000 in
theorem swapOK : ∀ i : Fin 5, ∀ m ∈ pts (kP i), ∀ h : Fin 4,
    moved i m h ∈ pts (kP (owner m h)) ∧ owner m h ≠ i ∧
    (∀ t : Fin 4, owner m t = owner m h → t = h) := by decide +kernel

theorem offColumn (i : Fin 5) (m : ℕ) (h : Fin 4) (v : W) (hv : v.2 ≠ h) :
    asg (moved i m h) v = asg m v := by
  have hne : v.2.val ≠ h.val := fun he => hv (Fin.ext he)
  have b1 := v.2.isLt
  have b2 := h.isLt
  have d1 : 4*i.val + h.val ≠ 4*v.1.val + v.2.val := by omega
  have d2 : 4*(owner m h).val + h.val ≠ 4*v.1.val + v.2.val := by omega
  simp [asg,moved,Nat.testBit_xor,Nat.testBit_two_pow,d1,d2]

theorem largeTerm {T : KTerm W} (h : T.card ≤ 2) (ne : (admits T).Nonempty) : 3 ≤ (admits T).card := by
  classical
  obtain ⟨i,hi⟩ := ne
  obtain ⟨m,hm,hs⟩ := List.any_eq_true.mp (Finset.mem_filter.mp hi).2
  have goodm : ∀ l ∈ T, asg m l.1 = l.2 := of_decide_eq_true hs
  let used := T.image (fun l : Literal W => l.1.2)
  let free := Finset.univ \ used
  have hsze : used.card ≤ 2 := le_trans Finset.card_image_le h
  have hfree : 2 ≤ free.card := by
    have z : free.card = 4 - used.card := by
      simpa [free] using Finset.card_sdiff_of_subset (Finset.subset_univ used)
    omega
  let dest := free.image (owner m)
  have inj : Function.Injective (owner m) := fun a b he => (swapOK i m hm b).2.2 a he
  have dc : dest.card = free.card := Finset.card_image_of_injective _ inj
  have ni : i ∉ dest := by
    rintro mem
    obtain ⟨t,_,eq⟩ := Finset.mem_image.mp mem
    exact (swapOK i m hm t).2.1 eq
  have sub : insert i dest ⊆ admits T := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    obtain ⟨t,ft,rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.any_eq_true.mpr
      ⟨moved i m t,(swapOK i m hm t).1,decide_eq_true ?_⟩⟩
    intro l hl
    have hv : l.1.2 ≠ t := by
      rintro rfl
      exact (Finset.mem_sdiff.mp ft).2 (Finset.mem_image_of_mem _ hl)
    rw [offColumn _ _ _ _ hv]
    exact goodm l hl
  have z := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem ni,dc] at z
  omega

theorem termMem {T : KTerm W} {i : Fin 5} {a : W → Bool} (ha : S i a)
    (sat : ∀ l ∈ T, a l.1 = l.2) : i ∈ admits T := by
  obtain ⟨m,hm,rfl⟩ := ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.any_eq_true.mpr ⟨m,hm,decide_eq_true sat⟩⟩

theorem getWitness {C : KLine W} {T : KTerm W} {i : Fin 5}
    (h : i ∈ admits T) (hT : T ∈ C) : ∃ a, S i a ∧ KLineSat a C := by
  have hh := (Finset.mem_filter.mp h).2
  obtain ⟨m,hm,hs⟩ := List.any_eq_true.mp hh
  exact ⟨asg m,⟨m,hm,rfl⟩,T,hT,of_decide_eq_true hs⟩

theorem overlap : ∀ C D : KLine W, (∀ T ∈ C, T.card ≤ 2) → (∀ T ∈ D, T.card ≤ 2) →
    ¬ Big S C → ¬ Big S D → ∃ i a b, S i a ∧ S i b ∧ KLineSat a C ∧ KLineSat b D := by
  classical
  intro C D wC wD nc nd
  unfold Big at nc nd
  push_neg at nc nd
  obtain ⟨i,a,ha,T,hT,hs⟩ := nc
  obtain ⟨j,b,hb,U,hU,hu⟩ := nd
  have t3 := largeTerm (wC T hT) ⟨i,termMem ha hs⟩
  have u3 := largeTerm (wD U hU) ⟨j,termMem hb hu⟩
  have inter : ¬ Disjoint (admits T) (admits U) := by
    intro hd
    have hcard := Finset.card_union_of_disjoint hd
    have bound : (admits T ∪ admits U).card ≤ 5 := by
      simpa using Finset.card_le_univ (admits T ∪ admits U)
    omega
  obtain ⟨k,ht,hu⟩ := Finset.not_disjoint_iff.mp inter
  obtain ⟨p,hp,cp⟩ := getWitness ht hT
  obtain ⟨q,hq,dq⟩ := getWitness hu hU
  exact ⟨k,p,q,hp,hq,cp,dq⟩

theorem present (k : Fin 45) : ∃ a, Pt k a := by
  obtain ⟨m,hm⟩ := List.exists_mem_of_ne_nil (pts k) (inhabitedPts k)
  exact ⟨asg m,m,hm,rfl⟩

theorem smallAx : ∀ R ∈ FF, ¬ Big S R := by
  intro R hr big
  obtain ⟨k,h⟩ := HH R hr
  have hx : ∃ i : Fin 5, kP i ≠ k := by
    by_cases z : kP 0 = k
    · exact ⟨1,z ▸ (by decide : kP 1 ≠ kP 0)⟩
    · exact ⟨0,z⟩
  obtain ⟨i,hi⟩ := hx
  obtain ⟨a,ha⟩ := present (kP i)
  exact big i a ha (h _ hi _ ha)

theorem bound {π : List (KLine W)} (h : IsResKRefutation 2 (PHP 5 4) π) : 90 ≤ π.length := by
  obtain ⟨hd,hem⟩ := h
  have noSat : ∀ a : W → Bool, ¬ KLineSat a ∅ := by
    rintro a ⟨T,hT,_⟩
    exact Finset.notMem_empty _ hT
  have hit : Hit Pt Finset.univ ({∅} : Finset (KLine W)) := by
    intro k _
    obtain ⟨a,ha⟩ := present k
    exact ⟨a,ha,∅,by simp,noSat a⟩
  have hret := walk FF Pt HH S kP (fun _ _ x => x) smallAx overlap (good hd) (resK_lines_card hd)
    {∅} Finset.univ (fun _ hm => (Finset.mem_singleton.mp hm) ▸ hem) hit
      ⟨∅,by simp,fun _ a _ => noSat a⟩
  simp only [Finset.card_univ,Fintype.card_fin, Finset.card_singleton] at hret
  omega

end PEqualNP.Outside.L_pcx_196

theorem PEqualNP.Outside.L_pcx_196 : ¬ (∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 89) := by
  rintro ⟨π,hπ,hlen⟩
  have := PEqualNP.Outside.L_pcx_196.bound hπ
  omega
