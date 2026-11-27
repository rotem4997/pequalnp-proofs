import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10061

variable {α β : Type} [DecidableEq α] [DecidableEq β]

private def Bic (A : α → β → Bool) (R : Finset α) (C : Finset β) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ C, ∀ d ∈ C,
    A a c = true → A b c = true → A a d = true → A b d = true

private def Twins (A : α → β → Bool) (R X : Finset α) (C Y : Finset β) : Prop :=
  (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ C, A a c = A b c) ∧
  (∀ a ∈ Y, ∀ b ∈ Y, ∀ r ∈ R, A r a = A r b)

-- One round can delete a class of equal rows and a class of equal columns.
private def Rank (A : α → β → Bool) : ℕ → Finset α → Finset β → Prop
  | 0, R, C => Bic A R C
  | n + 1, R, C => ∃ X ⊆ R, ∃ Y ⊆ C, Twins A R X C Y ∧ Rank A n (R \ X) (C \ Y)

private theorem rank_extend {A : α → β → Bool} {k : ℕ} {R S : Finset α} {C D : Finset β}
    (hS : S ⊆ R) (hD : D ⊆ C) (h : Rank A k S D)
    (hsub : Bic A (R \ S) (C \ D))
    (h1 : ∀ a ∈ S, ∀ b ∈ C \ D, A a b = false)
    (h2 : ∀ a ∈ R \ S, ∀ b ∈ D, A a b = false) : Rank A k R C := by
  induction k generalizing R S C D with
  | zero =>
    intro a ha b hb c hc d hd hac hbc had
    have key : ∀ x ∈ R, ∀ y ∈ C, A x y = true → (x ∈ S ↔ y ∈ D) := by
      intro x hx y hy hxy
      constructor
      · intro hxS
        by_contra hn
        rw [h1 x hxS y (Finset.mem_sdiff.2 ⟨hy, hn⟩)] at hxy
        contradiction
      · intro hyD
        by_contra hn
        rw [h2 x (Finset.mem_sdiff.2 ⟨hx, hn⟩) y hyD] at hxy
        contradiction
    have e1 := key a ha c hc hac
    have e2 := key b hb c hc hbc
    have e3 := key a ha d hd had
    by_cases hs : a ∈ S
    · exact h a hs b (e2.mpr (e1.mp hs)) c (e1.mp hs) d (e3.mp hs) hac hbc had
    · exact hsub a (Finset.mem_sdiff.2 ⟨ha, hs⟩)
        b (Finset.mem_sdiff.2 ⟨hb, hs ∘ e1.mpr ∘ e2.mp⟩)
        c (Finset.mem_sdiff.2 ⟨hc, hs ∘ e1.mpr⟩)
        d (Finset.mem_sdiff.2 ⟨hd, hs ∘ e3.mpr⟩) hac hbc had
  | succ k ih =>
    obtain ⟨X, hX, Y, hY, hT, h⟩ := h
    refine ⟨X, hX.trans hS, Y, hY.trans hD, ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb c hc
      by_cases hd : c ∈ D
      · exact hT.1 a ha b hb c hd
      · rw [h1 a (hX ha) c (Finset.mem_sdiff.2 ⟨hc, hd⟩), h1 b (hX hb) c (Finset.mem_sdiff.2 ⟨hc, hd⟩)]
    · intro a ha b hb r hr
      by_cases hs : r ∈ S
      · exact hT.2 a ha b hb r hs
      · rw [h2 r (Finset.mem_sdiff.2 ⟨hr, hs⟩) a (hY ha), h2 r (Finset.mem_sdiff.2 ⟨hr, hs⟩) b (hY hb)]
    · have eR : (R \ X) \ (S \ X) = R \ S := by
        ext a
        simp only [Finset.mem_sdiff]
        have := @hX a
        tauto
      have eC : (C \ Y) \ (D \ Y) = C \ D := by
        ext a
        simp only [Finset.mem_sdiff]
        have := @hY a
        tauto
      have Incl {T U V : Finset α} (h : T ⊆ U) : T \ V ⊆ U \ V :=
        fun _ hmem => Finset.mem_sdiff.2 ⟨h (Finset.mem_sdiff.1 hmem).1, (Finset.mem_sdiff.1 hmem).2⟩
      have Incl' {T U V : Finset β} (h : T ⊆ U) : T \ V ⊆ U \ V :=
        fun _ hmem => Finset.mem_sdiff.2 ⟨h (Finset.mem_sdiff.1 hmem).1, (Finset.mem_sdiff.1 hmem).2⟩
      apply ih (Incl hS) (Incl' hD) h
      · simpa only [eR, eC] using hsub
      · intro a ha b hb
        exact h1 a (Finset.mem_sdiff.1 ha).1 b (eC ▸ hb)
      · intro a ha b hb
        exact h2 a (eR ▸ ha) b (Finset.mem_sdiff.1 hb).1

private def Pairing (F : Finset ℕ → Bool) (A : α → β → Bool) (l : α → ℕ) (r : β → ℕ)
    (N : Finset ℕ) (R : Finset α) (C : Finset β) : Prop :=
  (∀ a ∈ R, l a ∈ N ∧ F {l a} = false) ∧
  (∀ b ∈ C, r b ∈ N ∧ F {r b} = false) ∧
  (∀ a ∈ R, ∀ b ∈ C, A a b = F {l a, r b})

private def Depends (F : Finset ℕ → Bool) (N : Finset ℕ) : Prop :=
  ∀ P Q : Finset ℕ, (∀ i ∈ N, i ∈ P ↔ i ∈ Q) → F P = F Q

private def Budgets (F : Finset ℕ → Bool) (N : Finset ℕ) (k : ℕ) : Prop :=
  ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (A : α → β → Bool)
    (l : α → ℕ) (r : β → ℕ) (R : Finset α) (C : Finset β),
    Pairing F A l r N R C → Rank A k R C

private def avoid {γ : Type} (S : Finset γ) (w : γ → ℕ) (J : Finset ℕ) : Finset γ :=
  S.filter fun a => w a ∉ J

private theorem charge {F : Finset ℕ → Bool} {A : α → β → Bool} {l : α → ℕ} {r : β → ℕ}
    {N R C} (h : Pairing F A l r N R C) (J : Finset ℕ) {k : ℕ}
    (hk : Rank A k (avoid R l J) (avoid C r J)) : Rank A (k + J.card) R C := by
  induction J using Finset.induction_on generalizing R C with
  | empty => simpa [avoid] using hk
  | @insert j J hj ih =>
    let X := R.filter fun a => l a = j
    let Y := C.filter fun b => r b = j
    rw [Finset.card_insert_of_notMem hj, ← Nat.add_assoc]
    refine ⟨X, Finset.filter_subset _ _, Y, Finset.filter_subset _ _, ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb c hc
      obtain ⟨ha, e₁⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb, e₂⟩ := Finset.mem_filter.1 hb
      rw [h.2.2 a ha c hc, h.2.2 b hb c hc, e₁, e₂]
    · intro a ha b hb c hc
      obtain ⟨ha, e₁⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb, e₂⟩ := Finset.mem_filter.1 hb
      rw [h.2.2 c hc a ha, h.2.2 c hc b hb, e₁, e₂]
    · apply ih
      · exact ⟨fun a ha => h.1 a (Finset.mem_sdiff.1 ha).1,
          fun b hb => h.2.1 b (Finset.mem_sdiff.1 hb).1,
          fun a ha b hb => h.2.2 a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1⟩
      · have eR : avoid (R \ X) l J = avoid R l (insert j J) := by
          ext a
          simp only [avoid, X, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        have eC : avoid (C \ Y) r J = avoid C r (insert j J) := by
          ext a
          simp only [avoid, Y, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        rw [eR, eC]
        exact hk

private def put (t : ℕ) (b : Bool) (P : Finset ℕ) : Finset ℕ :=
  if b then insert t P else P.erase t

private def trigger (S : Finset ℕ) (isAnd : Bool) (P : Finset ℕ) : Bool :=
  if isAnd then decide (S ⊆ P) else decide (∃ i ∈ S, i ∈ P)

private theorem trigger_congr (S : Finset ℕ) (a : Bool) (P Q : Finset ℕ)
    (h : ∀ i ∈ S, i ∈ P ↔ i ∈ Q) : trigger S a P = trigger S a Q := by
  cases a
  · simp only [trigger, Bool.false_eq_true, ite_false, decide_eq_decide]
    exact exists_congr fun i => and_congr_right (h i)
  · simp only [trigger, ite_true, decide_eq_decide]
    exact forall_congr' fun i => imp_congr_right (h i)

private theorem trigger_zero (S : Finset ℕ) (a : Bool)
    (ha : a = true → S.card = 2) : trigger S a ∅ = false := by
  cases a
  · simp [trigger]
  · have h : S ≠ ∅ := fun e => by simpa [e] using ha rfl
    simp [trigger, h]

private theorem put_mem_self (t : ℕ) (b : Bool) (P : Finset ℕ) :
    t ∈ put t b P ↔ b = true := by cases b <;> simp [put]

private theorem put_mem_other {i t : ℕ} (h : i ≠ t) (b : Bool) (P : Finset ℕ) :
    i ∈ put t b P ↔ i ∈ P := by cases b <;> simp [put, h]

private theorem replace_depends {F : Finset ℕ → Bool} {N S : Finset ℕ} {t : ℕ} {a : Bool}
    (hd : Depends F N) : Depends (fun P => F (put t (trigger S a P) P)) (N.erase t ∪ S) := by
  intro P Q hPQ
  apply hd
  intro i hi
  by_cases h : i = t
  · subst i
    rw [put_mem_self, put_mem_self, trigger_congr S a P Q (fun i hi => hPQ i (Finset.mem_union_right _ hi))]
  · rw [put_mem_other h, put_mem_other h]
    exact hPQ i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨h, hi⟩))

private theorem ignored_update {F : Finset ℕ → Bool} {N : Finset ℕ} {t : ℕ}
    (hd : Depends F N) (ht : t ∉ N) (P : Finset ℕ) (b : Bool) : F (put t b P) = F P := by
  apply hd
  intro i hi
  have hn : i ≠ t := fun e => ht (e ▸ hi)
  exact put_mem_other hn b P

private theorem or_pair {F : Finset ℕ → Bool} {N S : Finset ℕ} {t u v : ℕ}
    (hd : Depends F N) (ht : t ∈ N)
    (hu : u ∈ N.erase t ∪ S) (hv : v ∈ N.erase t ∪ S)
    (hu' : u ∉ N.erase t ∩ S) (hv' : v ∉ N.erase t ∩ S) :
    let m (w : ℕ) := if w ∈ S then t else w
    m u ∈ N ∧ m v ∈ N ∧ F (put t (trigger S false {u,v}) {u,v}) = F {m u,m v} := by
  dsimp
  have hm : ∀ w ∈ N.erase t ∪ S, (if w ∈ S then t else w) ∈ N := by
    intro w hw
    split_ifs with hh
    · exact ht
    · exact (Finset.mem_erase.1 ((Finset.mem_union.1 hw).resolve_right hh)).2
  refine ⟨hm u hu, hm v hv, ?_⟩
  apply hd
  intro i hi
  have mt : ∀ w ∈ N.erase t ∪ S, (if w ∈ S then t else w) = t ↔ w ∈ S := by
    intro w hw
    by_cases hh : w ∈ S
    · simp [hh]
    · have hne := (Finset.mem_erase.1 ((Finset.mem_union.1 hw).resolve_right hh)).1
      simp [hh, hne]
  have mo : ∀ w, w ∉ N.erase t ∩ S → i ≠ t →
      (i = (if w ∈ S then t else w) ↔ i = w) := by
    intro w hw hn
    by_cases hS : w ∈ S
    · have hw' : i ≠ w := fun e => hw (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨e ▸ hn, e ▸ hi⟩, hS⟩)
      simp [hS, hn, hw']
    · simp [hS]
  by_cases he : i = t
  · subst i
    rw [put_mem_self]
    simp only [trigger, Bool.false_eq_true, ite_false, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    rw [eq_comm (a := t) (b := if u ∈ S then t else u),
      eq_comm (a := t) (b := if v ∈ S then t else v), mt u hu, mt v hv]
    constructor
    · rintro ⟨j, hj, (rfl | rfl)⟩
      · exact Or.inl hj
      · exact Or.inr hj
    · rintro (h | h)
      · exact ⟨u, h, Or.inl rfl⟩
      · exact ⟨v, h, Or.inr rfl⟩
  · rw [put_mem_other he]
    simp only [Finset.mem_insert, Finset.mem_singleton, mo u hu' he, mo v hv' he]

private theorem and_pair {F : Finset ℕ → Bool} {N S : Finset ℕ} {t u v : ℕ}
    (hd : Depends F N) (hS : S.card = 2) (htS : t ∉ S)
    (hu : u ∈ N.erase t ∪ S) (hv : v ∈ N.erase t ∪ S)
    (hu' : u ∉ N.erase t ∩ S) (hv' : v ∉ N.erase t ∩ S) :
    F (put t (trigger S true {u,v}) {u,v}) =
      if u ∈ S then
        if v ∈ S then (if S ⊆ {u,v} then F {t} else F ∅) else F {v}
      else if v ∈ S then F {u} else F {u,v} := by
  have ht : t ≠ u ∧ t ≠ v := by
    constructor
    · rintro rfl
      exact (Finset.mem_union.1 hu).elim (by simp) htS
    · rintro rfl
      exact (Finset.mem_union.1 hv).elim (by simp) htS
  have hnot : ∀ w : ℕ, ¬ S ⊆ {w} := by
    intro w hn
    have := Finset.card_le_card hn
    simp [hS] at this
  have htno : ∀ i ∈ N, i ≠ t → i ≠ u ∨ u ∉ S := by
    intro i hi hit
    by_cases d : i = u
    · subst i
      exact Or.inr (fun h => hu' (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hit, hi⟩, h⟩))
    · exact Or.inl d
  have htno' : ∀ i ∈ N, i ≠ t → i ≠ v ∨ v ∉ S := by
    intro i hi hit
    by_cases d : i = v
    · subst i
      exact Or.inr (fun h => hv' (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hit, hi⟩, h⟩))
    · exact Or.inl d
  have off : u ∉ S ∨ v ∉ S → ¬ S ⊆ ({u,v} : Finset ℕ) := by
    rintro (h | h) hs
    · apply hnot v
      intro x hx
      have := hs hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact this.resolve_left (fun e => h (e ▸ hx))
    · apply hnot u
      intro x hx
      have := hs hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact this.resolve_right (fun e => h (e ▸ hx))
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
  · simp only [huS, hvS, ite_true]
    split_ifs with e
    · apply hd
      intro i hi
      by_cases ht' : i = t
      · subst i
        simp [put_mem_self, trigger, e]
      · rw [put_mem_other ht']
        have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
        have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
        simp [h₁, h₂, ht']
    · apply hd
      intro i hi
      by_cases ht' : i = t
      · subst i
        simp [put_mem_self, trigger, e]
      · rw [put_mem_other ht']
        have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
        have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
        simp [h₁, h₂]
  · simp only [huS, hvS, ite_true, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inr hvS), ht.2]
    · rw [put_mem_other ht']
      have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
      simp [h₁]
  · simp only [huS, hvS, ite_true, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inl huS), ht.1]
    · rw [put_mem_other ht']
      have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
      simp [h₂]
  · simp only [huS, hvS, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inl huS), ht.1, ht.2]
    · exact put_mem_other ht' _ _

-- Shared operands spend deletion rounds. Fresh OR operands merge into the old
-- label, and the fresh AND operands contribute only isolated rectangles.
private theorem replace_budget {F : Finset ℕ → Bool} {N S : Finset ℕ} {t k : ℕ} {a : Bool}
    (hd : Depends F N) (h0 : F ∅ = false) (hB : Budgets F N k)
    (ht : t ∈ N) (htS : t ∉ S) (ha : a = true → S.card = 2) :
    Budgets (fun P => F (put t (trigger S a P) P)) (N.erase t ∪ S) (k + (N.erase t ∩ S).card) := by
  intro α β _ _ A l r R C h
  let J := N.erase t ∩ S
  apply charge h J
  let R' := avoid R l J
  let C' := avoid C r J
  have hL : ∀ i ∈ R', l i ∈ N.erase t ∪ S ∧ l i ∉ J := fun i hi =>
    ⟨(h.1 i (Finset.mem_filter.1 hi).1).1, (Finset.mem_filter.1 hi).2⟩
  have hR : ∀ j ∈ C', r j ∈ N.erase t ∪ S ∧ r j ∉ J := fun j hj =>
    ⟨(h.2.1 j (Finset.mem_filter.1 hj).1).1, (Finset.mem_filter.1 hj).2⟩
  have hLS : ∀ i ∈ R', F (put t (trigger S a {l i}) {l i}) = false := fun i hi =>
    (h.1 i (Finset.mem_filter.1 hi).1).2
  have hRS : ∀ j ∈ C', F (put t (trigger S a {r j}) {r j}) = false := fun j hj =>
    (h.2.1 j (Finset.mem_filter.1 hj).1).2
  have hP : ∀ i ∈ R', ∀ j ∈ C', A i j = F (put t (trigger S a {l i,r j}) {l i,r j}) := fun i hi j hj =>
    h.2.2 i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1
  cases a
  · let m (w : ℕ) := if w ∈ S then t else w
    apply hB A (m ∘ l) (m ∘ r) R' C'
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have e := or_pair hd ht (hL i hi).1 (hL i hi).1 (hL i hi).2 (hL i hi).2
      have q : F (put t (trigger S false {l i}) {l i}) = F {m (l i)} := by
        simpa [m] using e.2.2
      exact ⟨e.1, q.symm.trans (hLS i hi)⟩
    · intro j hj
      have e := or_pair hd ht (hR j hj).1 (hR j hj).1 (hR j hj).2 (hR j hj).2
      have q : F (put t (trigger S false {r j}) {r j}) = F {m (r j)} := by
        simpa [m] using e.2.2
      exact ⟨e.1, q.symm.trans (hRS j hj)⟩
    · intro i hi j hj
      exact (hP i hi j hj).trans (or_pair hd ht (hL i hi).1 (hR j hj).1 (hL i hi).2 (hR j hj).2).2.2
  · have hS := ha rfl
    let X := avoid R' l S
    let Y := avoid C' r S
    let e u v hu hv hu' hv' := and_pair (u := u) (v := v) hd hS htS hu hv hu' hv'
    have lzero : ∀ i ∈ X, F {l i} = false := by
      intro i hi
      obtain ⟨hr, hs⟩ := Finset.mem_filter.1 hi
      have q := e (l i) (l i) (hL i hr).1 (hL i hr).1 (hL i hr).2 (hL i hr).2
      have q' : F (put t (trigger S true {l i}) {l i}) = F {l i} := by simpa [hs] using q
      exact q'.symm.trans (hLS i hr)
    have rzero : ∀ j ∈ Y, F {r j} = false := by
      intro j hj
      obtain ⟨hr, hs⟩ := Finset.mem_filter.1 hj
      have q := e (r j) (r j) (hR j hr).1 (hR j hr).1 (hR j hr).2 (hR j hr).2
      have q' : F (put t (trigger S true {r j}) {r j}) = F {r j} := by simpa [hs] using q
      exact q'.symm.trans (hRS j hr)
    have hX : X ⊆ R' := Finset.filter_subset _ _
    have hY : Y ⊆ C' := Finset.filter_subset _ _
    have hx : ∀ i ∈ R' \ X, l i ∈ S := by
      intro i hi
      by_contra hn
      exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hi).1, hn⟩)
    have hy : ∀ j ∈ C' \ Y, r j ∈ S := by
      intro j hj
      by_contra hn
      exact (Finset.mem_sdiff.1 hj).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hj).1, hn⟩)
    have evalP : ∀ i ∈ R', ∀ j ∈ C', A i j =
        if l i ∈ S then if r j ∈ S then (if S ⊆ {l i,r j} then F {t} else F ∅) else F {r j}
        else if r j ∈ S then F {l i} else F {l i,r j} := by
      intro i hi j hj
      exact (hP i hi j hj).trans (e _ _ (hL i hi).1 (hR j hj).1 (hL i hi).2 (hR j hj).2)
    apply rank_extend hX hY (hB A l r X Y ?_)
    · intro a ha b hb c hc d hd' hac hbc had
      have E : ∀ i ∈ R' \ X, ∀ j ∈ C' \ Y, A i j = (if S ⊆ {l i,r j} then F {t} else false) := by
        intro i hi j hj
        simpa [hx i hi, hy j hj, h0] using evalP i (Finset.mem_sdiff.1 hi).1 j (Finset.mem_sdiff.1 hj).1
      rw [E a ha c hc] at hac
      rw [E a ha d hd'] at had
      rw [E b hb c hc] at hbc
      rw [E b hb d hd']
      have h₁ : S ⊆ ({l a,r c} : Finset ℕ) := by
        by_contra e
        simp [e] at hac
      have h₂ : S ⊆ ({l a,r d} : Finset ℕ) := by
        by_contra e
        simp [e] at had
      have same : ({l a,r c} : Finset ℕ) = {l a,r d} := by
        have eq : ∀ x y : ℕ, S ⊆ {x,y} → S = {x,y} := by
          intro x y hxy
          apply Finset.eq_of_subset_of_card_le hxy
          rw [hS]
          exact le_trans (Finset.card_insert_le _ _) (by simp)
        exact (eq _ _ h₁).symm.trans (eq _ _ h₂)
      have neq : r d ≠ l a := by
        intro he
        have := Finset.card_le_card h₂
        simp [he, hS] at this
      have hr' : r d = r c := by
        have hm : r d ∈ ({l a,r c} : Finset ℕ) := by rw [same]; simp
        exact (Finset.mem_insert.1 hm).resolve_left neq |> Finset.mem_singleton.1
      simpa only [hr'] using hbc
    · intro i hi j hj
      simpa [(Finset.mem_filter.1 hi).2, hy j hj, lzero i hi] using
        evalP i (hX hi) j (Finset.mem_sdiff.1 hj).1
    · intro i hi j hj
      simpa [hx i hi, (Finset.mem_filter.1 hj).2, rzero j hj] using
        evalP i (Finset.mem_sdiff.1 hi).1 j (hY hj)
    · refine ⟨?_, ?_, ?_⟩
      · intro i hi
        have nue := (Finset.mem_filter.1 hi).2
        exact ⟨(Finset.mem_erase.1 ((Finset.mem_union.1 (hL i (hX hi)).1).resolve_right nue)).2, lzero i hi⟩
      · intro j hj
        have nue := (Finset.mem_filter.1 hj).2
        exact ⟨(Finset.mem_erase.1 ((Finset.mem_union.1 (hR j (hY hj)).1).resolve_right nue)).2, rzero j hj⟩
      · intro i hi j hj
        simpa [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hj).2] using evalP i (hX hi) j (hY hj)


-- For distinct equal rows, at most one common column needs deletion to
-- disconnect the class from every other row.
private def Separates (A : α → β → Bool) : Prop :=
  ∀ a b, a ≠ b → ∃ q, ∀ c, c ≠ q → A a c = true → A b c = true →
    ∀ r, A r c = true → r = a ∨ r = b

private def Raw (A : α → β → Bool) (k : ℕ) (R : Finset α) (C : Finset β) : Prop :=
  ∃ S ⊆ R, ∃ D ⊆ C, (R \ S).card + (C \ D).card ≤ k ∧ Bic A S D

private theorem restore_rows {A : α → β → Bool} (hsep : Separates A)
    {R X : Finset α} {C : Finset β} {k : ℕ} (hX : X ⊆ R)
    (ht : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ C, A a c = A b c)
    (hr : Raw A k (R \ X) C) : Raw A (k + 1) R C := by
  obtain ⟨S, hS, D, hD, hcard, hbic⟩ := hr
  by_cases hbig : 1 < X.card
  · obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp hbig
    obtain ⟨q, hq⟩ := hsep a b hne
    have rows_left : R \ (S ∪ X) = (R \ X) \ S := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    have cols_left : (C \ D.erase q) ⊆ (C \ D) ∪ {q} := by
      intro c hc
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union,
        Finset.mem_singleton] at hc ⊢
      tauto
    have hcols := (Finset.card_le_card cols_left).trans
      (Finset.card_union_le (C \ D) {q})
    have isolate : ∀ x ∈ X, ∀ u ∈ S, ∀ c ∈ D.erase q,
        A x c = true → A u c ≠ true := by
      intro x hx u hu c hc he hu'
      have hcD := (Finset.mem_erase.mp hc).2
      have hca := (ht a ha x hx c (hD hcD)).trans he
      have hcb := (ht b hb x hx c (hD hcD)).trans he
      have hx' : u ∈ X := (hq c (Finset.mem_erase.mp hc).1 hca hcb u hu').elim
        (fun e => e.symm ▸ ha) (fun e => e.symm ▸ hb)
      exact (Finset.mem_sdiff.mp (hS hu)).2 hx'
    refine ⟨S ∪ X, Finset.union_subset (hS.trans Finset.sdiff_subset) hX,
      D.erase q, (Finset.erase_subset _ _).trans hD, ?_, ?_⟩
    · rw [rows_left]
      simp only [Finset.card_singleton] at hcols
      omega
    · intro u hu v hv c hc d hd huc hvc hud
      rcases Finset.mem_union.mp hu with hu | hu <;>
        rcases Finset.mem_union.mp hv with hv | hv
      · exact hbic _ hu _ hv _ (Finset.mem_erase.mp hc).2 _
          (Finset.mem_erase.mp hd).2 huc hvc hud
      · exact (isolate v hv u hu c hc hvc huc).elim
      · exact (isolate u hu v hv c hc huc hvc).elim
      · exact (ht v hv u hu d (hD (Finset.mem_erase.mp hd).2)).trans hud
  · have hs : (R \ S) ⊆ ((R \ X) \ S) ∪ X := by
      intro i hi
      simp only [Finset.mem_union, Finset.mem_sdiff] at hi ⊢
      tauto
    have hh := (Finset.card_le_card hs).trans
      (Finset.card_union_le ((R \ X) \ S) X)
    exact ⟨S, hS.trans Finset.sdiff_subset, D, hD, by omega, hbic⟩

private theorem raw_swap {A : α → α → Bool} (hs : ∀ a b, A a b = A b a)
    {k : ℕ} {R C : Finset α} (h : Raw A k R C) : Raw A k C R := by
  obtain ⟨S, hS, D, hD, hcard, hB⟩ := h
  refine ⟨D, hD, S, hS, by omega, ?_⟩
  intro a ha b hb c hc d hd hac hbc had
  rw [hs a c] at hac
  rw [hs b c] at hbc
  rw [hs a d] at had
  exact (hs b d).trans (hB c hc d hd a ha b hb hac had hbc)

private theorem rank_to_raw {A : α → α → Bool} (hs : ∀ a b, A a b = A b a)
    (hsep : Separates A) {k : ℕ} {R C : Finset α} (h : Rank A k R C) :
    Raw A (2 * k) R C := by
  induction k generalizing R C with
  | zero =>
    exact ⟨R, Finset.Subset.rfl, C, Finset.Subset.rfl, by simp, h⟩
  | succ k ih =>
    obtain ⟨X, hX, Y, hY, hT, h⟩ := h
    have hr := raw_swap hs (ih h)
    have hr' : Raw A (2 * k + 1) C (R \ X) := by
      apply restore_rows hsep hY _ hr
      intro a ha b hb c hc
      rw [hs a c, hs b c]
      exact hT.2 a ha b hb c (Finset.mem_sdiff.mp hc).1
    have hr'' := restore_rows hsep hX hT.1 (raw_swap hs hr')
    simpa only [Nat.mul_succ] using hr''

-- The circuit cut and ring counting arguments are adapted from sheganinans,
-- pequalnp-proofs PR 13556, under the Apache License, Version 2.0.
-- This version adds the twin class replacement bound.

-- The literal graph is a ring of 26 squares, one satellite per square end.
private def A : Fin 39 → Fin 39 → Bool := fun a b => decide (∃ i : Fin 13,
  ((a.val = i.val ∨ a.val = 13 + i.val) ∧ (b.val = (i.val + 1) % 13 ∨ b.val = 26 + i.val)) ∨
  ((b.val = i.val ∨ b.val = 13 + i.val) ∧ (a.val = (i.val + 1) % 13 ∨ a.val = 26 + i.val)))

private theorem A_sym : ∀ a b, A a b = A b a := by decide +kernel

private abbrev V := Fin 39 ⊕ Fin 39

private def G : V → V → Bool
  | .inl a, .inr b => A a b
  | .inr b, .inl a => A a b
  | _, _ => false

private def next (i : Fin 26) : Fin 26 := Fin.ofNat 26 (i.val + 1)
private def prev (i : Fin 26) : Fin 26 := Fin.ofNat 26 (i.val + 25)

private theorem next_prev : ∀ i, next (prev i) = i := by decide +kernel
private theorem prev_next : ∀ i, prev (next i) = i := by decide +kernel

private def token (i : Fin 26) (kind : Fin 3) : V :=
  let v := Fin.ofNat 39 (if kind = 0 then i.val % 13 else
    if kind = 1 then 13 + i.val % 13 else 26 + (i.val + 12) % 13)
  if i.val % 2 = 0 then .inl v else .inr v

private abbrev mid (i : Fin 26) := token i 0
private abbrev aft (i : Fin 26) := token i 1
private abbrev bef (i : Fin 26) := token i 2

private theorem token_inj : ∀ (i j : Fin 26) (p q : Fin 3),
    token i p = token j q → i = j ∧ p = q := by decide +kernel

private theorem localDiamond : ∀ (i : Fin 26) (p q : Bool),
    let a := if p then mid (prev i) else aft (prev i)
    let b := if q then mid (next i) else bef (next i)
    G (mid i) a = true ∧ G (mid i) b = true ∧
      G (bef i) a = true ∧ G (bef i) b = false ∧
      G (aft i) b = true ∧ G (aft i) a = false := by decide +kernel

private def assign (D : Finset V) (i : Fin 26) : Fin 26 × Fin 3 :=
  if mid i ∈ D then (i, 0) else
  if mid (prev i) ∈ D ∧ aft (prev i) ∈ D then (prev i, 1) else
  if mid (next i) ∈ D ∧ bef (next i) ∈ D then (next i, 2) else (i, 1)

private def retrieve (D : Finset V) (x : Fin 26 × Fin 3) : Fin 26 :=
  if x.2 = 0 ∨ mid x.1 ∉ D then x.1 else if x.2 = 1 then next x.1 else prev x.1

private theorem retrieve_assign (D : Finset V) (i : Fin 26) : retrieve D (assign D i) = i := by
  unfold assign
  split_ifs with hi hp hn
  · simp [retrieve]
  · simp [retrieve, hp.1, next_prev]
  · simp [retrieve, hn.1, prev_next]
  · simp [retrieve, hi]

private theorem charge_mid (D : Finset V)
    (h : ∀ a b c d : V, a ∉ D → b ∉ D → c ∉ D → d ∉ D →
      G a c = true → G b c = true → G a d = true → G b d = true) :
    ∀ i, token (assign D i).1 (assign D i).2 ∈ D := by
  intro i
  unfold assign
  split_ifs with hi hp hn
  · exact hi
  · exact hp.2
  · exact hn.2
  · by_contra hb
    let p := decide (mid (prev i) ∉ D)
    let q := decide (mid (next i) ∉ D)
    let a := if p then mid (prev i) else aft (prev i)
    let b := if q then mid (next i) else bef (next i)
    have ha : a ∉ D := by
      by_cases e : mid (prev i) ∈ D
      · have h' : aft (prev i) ∉ D := fun h' => hp ⟨e, h'⟩
        simpa [a, p, e] using h'
      · simp [a, p, e]
    have hc : b ∉ D := by
      by_cases e : mid (next i) ∈ D
      · have h' : bef (next i) ∉ D := fun h' => hn ⟨e, h'⟩
        simpa [b, q, e] using h'
      · simp [b, q, e]
    obtain ⟨hia, hib, _, _, hfb, hfa⟩ := localDiamond i p q
    exact Bool.false_ne_true (hfa.symm.trans (h _ _ _ _ hi hb hc ha hib hfb hia))

private def absent (R C : Finset (Fin 39)) : Finset V :=
  ((Finset.univ \ R).image Sum.inl) ∪ ((Finset.univ \ C).image Sum.inr)

private theorem absent_left {R C : Finset (Fin 39)} (a : Fin 39) :
    Sum.inl a ∉ absent R C ↔ a ∈ R := by simp [absent]

private theorem absent_right {R C : Finset (Fin 39)} (a : Fin 39) :
    Sum.inr a ∉ absent R C ↔ a ∈ C := by simp [absent]

private theorem raw_lower (R C : Finset (Fin 39)) (h : Bic A R C) :
    26 ≤ ((Finset.univ \ R).card + (Finset.univ \ C).card) := by
  let D := absent R C
  have hG : ∀ a b c d : V, a ∉ D → b ∉ D → c ∉ D → d ∉ D →
      G a c = true → G b c = true → G a d = true → G b d = true := by
    intro a b c d ha hb hc hd hac hbc had
    cases a <;> cases b <;> cases c <;> cases d <;> simp only [G] at *
    all_goals try contradiction
    · exact h _ ((absent_left _).1 ha) _ ((absent_left _).1 hb)
        _ ((absent_right _).1 hc) _ ((absent_right _).1 hd) hac hbc had
    · exact h _ ((absent_left _).1 hc) _ ((absent_left _).1 hd)
        _ ((absent_right _).1 ha) _ ((absent_right _).1 hb) hac had hbc
  let f : Fin 26 → V := fun i => token (assign D i).1 (assign D i).2
  have inj : Function.Injective f := by
    intro i j hij
    have h := token_inj _ _ _ _ hij
    have e : assign D i = assign D j := Prod.ext h.1 h.2
    simpa only [retrieve_assign] using congrArg (retrieve D) e
  have hs : Finset.univ.image f ⊆ D := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
    exact charge_mid D hG i
  have h₁ := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at h₁
  have h₂ := Finset.card_union_le ((Finset.univ \ R).image (Sum.inl : Fin 39 → V))
    ((Finset.univ \ C).image (Sum.inr : Fin 39 → V))
  have h₃ := Finset.card_image_le (s := Finset.univ \ R) (f := (Sum.inl : Fin 39 → V))
  have h₄ := Finset.card_image_le (s := Finset.univ \ C) (f := (Sum.inr : Fin 39 → V))
  change 26 ≤ (absent R C).card at h₁
  unfold absent at h₁
  omega


private def centralCommon (a b : Fin 39) : Finset (Fin 13) :=
  Finset.univ.filter fun c => A a (Fin.castLE (by decide) c) = true ∧
    A b (Fin.castLE (by decide) c) = true

private theorem central_unique : ∀ a b, a ≠ b → (centralCommon a b).card ≤ 1 := by
  decide +kernel

private def column (c : Fin 39) : Finset (Fin 39) :=
  Finset.univ.filter fun a => A a c = true

private theorem auxiliary_degree : ∀ c : Fin 39, 13 ≤ c.val → (column c).card ≤ 2 := by
  decide +kernel

private theorem separating : Separates A := by
  intro a b hab
  let T := centralCommon a b
  obtain hT | ⟨j, hj⟩ := T.eq_empty_or_nonempty
  · refine ⟨0, ?_⟩
    intro c _ hac hbc r hrc
    have hlarge : 13 ≤ c.val := by
      by_contra! hsmall
      let i : Fin 13 := ⟨c.val, hsmall⟩
      have he : Fin.castLE (by decide : 13 ≤ 39) i = c := Fin.ext rfl
      have hi : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [he] using And.intro hac hbc⟩
      rw [hT] at hi
      exact Finset.notMem_empty _ hi
    have hpair : ({a,b} : Finset (Fin 39)) ⊆ column c := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by assumption⟩
    have he := Finset.eq_of_subset_of_card_le hpair (by
      rw [Finset.card_pair hab]
      exact auxiliary_degree c hlarge)
    have hr : r ∈ column c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrc⟩
    simpa [← he] using hr
  · refine ⟨Fin.castLE (by decide) j, ?_⟩
    intro c hc hac hbc r hrc
    have hlarge : 13 ≤ c.val := by
      by_contra! hsmall
      let i : Fin 13 := ⟨c.val, hsmall⟩
      have he : Fin.castLE (by decide : 13 ≤ 39) i = c := Fin.ext rfl
      have hi : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [he] using And.intro hac hbc⟩
      have e := Finset.card_le_one.mp (central_unique a b hab) _ hi _ hj
      exact hc (he.symm.trans (congrArg (Fin.castLE (by decide : 13 ≤ 39)) e))
    have hpair : ({a,b} : Finset (Fin 39)) ⊆ column c := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by assumption⟩
    have he := Finset.eq_of_subset_of_card_le hpair (by
      rw [Finset.card_pair hab]
      exact auxiliary_degree c hlarge)
    have hr : r ∈ column c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrc⟩
    simpa [← he] using hr

private theorem rank_lower {k : ℕ} (h : Rank A k Finset.univ Finset.univ) :
    26 ≤ 2 * k := by
  obtain ⟨R, _, C, _, hcard, hB⟩ := rank_to_raw A_sym separating h
  exact (raw_lower R C hB).trans hcard

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def wiresFrom (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst i; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

private theorem run_eq (gs : List Gate) : ∀ w : List Bool, ∀ i,
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    have e : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [e, ih, List.length_append, List.length_singleton, run]
    congr 2
    funext j
    rw [getD_snoc, Function.update_apply]

private theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

private theorem run_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ t (x y : ℕ → Bool), (∀ i, x i = true → y i = true) →
      ∀ o, run gs t x o = true → run gs t y o = true := by
  induction gs with
  | nil => exact fun _ x y h o => h o
  | cons g gs ih =>
    intro t x y h o
    simp only [run]
    apply ih (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) _ _ _ _ o
    intro i
    by_cases hi : i = t
    · subst i
      simpa using op_mono g (hg g (by simp)) x y h
    · simpa only [Function.update_of_ne hi] using h i

-- The cut records changes from the all-zero evaluation of the earlier gates.
private def readCut (b : List Bool) (P : Finset ℕ) (i : ℕ) : Bool :=
  b.getD i false || decide (i < b.length ∧ i ∈ P)

private def cut (gs : List Gate) (b : List Bool) (o : ℕ) (P : Finset ℕ) : Bool :=
  run gs b.length (readCut b P) o

private theorem cut_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (b : List Bool) (o : ℕ) {P Q : Finset ℕ} (h : P ⊆ Q) : cut gs b o P = true → cut gs b o Q = true := by
  apply run_mono gs hg
  intro i
  simp only [readCut, Bool.or_eq_true, decide_eq_true_eq]
  rintro (hi | ⟨hlt, hp⟩)
  · exact Or.inl hi
  · exact Or.inr ⟨hlt, h hp⟩

private theorem readCut_snoc (b : List Bool) (v : Bool) (P : Finset ℕ) (e : Bool) :
    readCut (b ++ [v]) (put b.length e P) = Function.update (readCut b P) b.length (v || e) := by
  funext i
  unfold readCut
  rw [getD_snoc, Function.update_apply]
  split_ifs with hi
  · subst i
    simp [put_mem_self]
  · have hh : i < b.length + 1 ↔ i < b.length := by omega
    simp [hh, put_mem_other hi]

private abbrev Atom := ℕ ⊕ Bool

private def readAtom (b : List Bool) (i : ℕ) : Atom :=
  if b.getD i false then .inr true else if i < b.length then .inl i else .inr false

private def val (P : Finset ℕ) : Atom → Bool
  | .inl i => decide (i ∈ P)
  | .inr b => b

private theorem val_atom (b : List Bool) (i : ℕ) (P : Finset ℕ) :
    val P (readAtom b i) = readCut b P i := by
  unfold readAtom readCut
  by_cases h : b.getD i false = true
  · simp only [h, ite_true, val, Bool.true_or]
  · have h' : b.getD i false = false := by
      cases e : b.getD i false
      · rfl
      · exact (h e).elim
    rw [h']
    by_cases e : i < b.length
    · simp only [Bool.false_eq_true, ite_false, e, ite_true, val, Bool.false_or, true_and]
    · simp only [Bool.false_eq_true, ite_false, e, val, Bool.false_or, false_and, decide_false]

private theorem atom_lt (b : List Bool) (i x : ℕ) (h : readAtom b i = .inl x) : x < b.length := by
  unfold readAtom at h
  split_ifs at h with h₁ h₂; simp_all

private def Normal (t : ℕ) (f : Finset ℕ → Bool) : Prop :=
  ∃ v : Bool, ∃ S : Finset ℕ, ∃ a : Bool,
    (∀ i ∈ S, i < t) ∧ S.card ≤ 2 ∧ (a = true → S.card = 2) ∧
    ∀ P, f P = (v || trigger S a P)

private theorem norm_const (t : ℕ) (v : Bool) : Normal t (fun _ => v) := by
  refine ⟨v, ∅, false, ?_, by simp, by simp, ?_⟩
  · simp
  · intro P; simp [trigger]

private theorem norm_atom (t : ℕ) (x : Atom) (hx : ∀ i, x = .inl i → i < t) :
    Normal t (fun P => val P x) := by
  cases x with
  | inr b => exact norm_const t b
  | inl i =>
    refine ⟨false, {i}, false, ?_, by simp, by simp, ?_⟩
    · intro j hj
      have e := Finset.mem_singleton.1 hj
      exact hx j (congrArg Sum.inl e.symm)
    · intro P; simp [trigger, val]

private def combine (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

private theorem norm_two (t : ℕ) (a : Bool) (x y : Atom)
    (hx : ∀ i, x = .inl i → i < t) (hy : ∀ i, y = .inl i → i < t) :
    Normal t (fun P => combine a (val P x) (val P y)) := by
  cases x with
  | inr b =>
    cases a <;> cases b
    · simpa [combine, val] using norm_atom t y hy
    · simpa [combine, val] using norm_const t true
    · simpa [combine, val] using norm_const t false
    · simpa [combine, val] using norm_atom t y hy
  | inl p =>
    cases y with
    | inr b =>
      cases a <;> cases b
      · simpa [combine, val] using norm_atom t (.inl p) hx
      · simpa [combine, val] using norm_const t true
      · simpa [combine, val] using norm_const t false
      · simpa [combine, val] using norm_atom t (.inl p) hx
    | inl q =>
      by_cases e : p = q
      · subst q
        cases a <;> simpa [combine] using norm_atom t (.inl p) hx
      · refine ⟨false, {p,q}, a, ?_, by simp [e], fun _ => by simp [e], ?_⟩
        · intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hx _ rfl
          · exact hy _ rfl
        · intro P
          cases a <;> simp [combine, val, trigger, Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem norm_gate (b : List Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Normal b.length (fun P => g.op.eval (g.inputs.map (readCut b P))) := by
  rcases g with ⟨op, l⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with ⟨hop, hl⟩
  rcases l with _ | ⟨p, _ | ⟨q, l⟩⟩
  · rcases hop with rfl | rfl
    · exact norm_const _ true
    · exact norm_const _ false
  · rcases hop with rfl | rfl <;>
      simpa [GateOp.eval, val_atom] using norm_atom b.length (readAtom b p) (atom_lt b p)
  · have e : l = [] := by
      cases l with
      | nil => rfl
      | cons u l =>
        simp only [List.length_cons] at hl
        omega
    subst l
    rcases hop with rfl | rfl
    · simpa [GateOp.eval, combine, val_atom] using
        norm_two b.length true (readAtom b p) (readAtom b q) (atom_lt b p) (atom_lt b q)
    · simpa [GateOp.eval, combine, val_atom] using
        norm_two b.length false (readAtom b p) (readAtom b q) (atom_lt b p) (atom_lt b q)

private theorem cut_normal (gs : List Gate) (b : List Bool) (o : ℕ) (g : Gate)
    (v : Bool) (S : Finset ℕ) (a : Bool)
    (he : ∀ P, g.op.eval (g.inputs.map (readCut b P)) = (v || trigger S a P)) :
    cut (g :: gs) b o = fun P => cut gs (b ++ [v]) o (put b.length (trigger S a P) P) := by
  funext P
  simp only [cut, run, List.length_append, List.length_singleton, readCut_snoc, he]

-- Each gate increases the dependency count plus deletion budget by at most one.
private theorem cut_budget (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ b o, cut gs b o ∅ = false → ∃ N : Finset ℕ, ∃ k : ℕ,
    Depends (cut gs b o) N ∧ Budgets (cut gs b o) N k ∧ N.card + k ≤ gs.length + 1 := by
  induction gs with
  | nil =>
    intro b o h0
    refine ⟨{o}, 0, ?_, ?_, by simp⟩
    · intro P Q he
      have e := he o (Finset.mem_singleton_self _)
      unfold cut run readCut
      have hh : (o < b.length ∧ o ∈ P) ↔ (o < b.length ∧ o ∈ Q) := by rw [e]
      rw [decide_eq_decide.2 hh]
    · intro α β _ _ A l r R C h i hi j hj c hc d hd e₁ e₂ e₃
      have ho := (h.2.2 i hi c hc).symm.trans e₁
      have hli : l i = o := Finset.mem_singleton.1 (h.1 i hi).1
      have hrc : r c = o := Finset.mem_singleton.1 (h.2.1 c hc).1
      have hf := (h.1 i hi).2
      rw [hli] at hf
      have ht : cut [] b o {o} = true := by simpa [hli, hrc] using ho
      exact Bool.false_ne_true (hf.symm.trans ht) |>.elim
  | cons g gs ih =>
    intro b o h0
    obtain ⟨v, S, a, hS, hS2, ha, he⟩ := norm_gate b g (hg g (by simp))
    have eq := cut_normal gs b o g v S a he
    rw [eq] at h0 ⊢
    have h0' : cut gs (b ++ [v]) o ∅ = false := by
      simpa [trigger_zero S a ha, put] using h0
    obtain ⟨N, k, hd, hb, hsz⟩ := ih (fun h hh => hg h (List.mem_cons_of_mem _ hh)) _ _ h0'
    by_cases ht : b.length ∈ N
    · have htS : b.length ∉ S := fun h => (Nat.lt_irrefl _ (hS _ h))
      refine ⟨N.erase b.length ∪ S, k + (N.erase b.length ∩ S).card,
        replace_depends hd, replace_budget hd h0' hb ht htS ha, ?_⟩
      have h₁ := Finset.card_union_add_card_inter (N.erase b.length) S
      have h₂ := Finset.card_erase_of_mem ht
      have h₃ : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
      simp only [List.length_cons]
      omega
    · have e : (fun P => cut gs (b ++ [v]) o (put b.length (trigger S a P) P)) = cut gs (b ++ [v]) o := by
        funext P
        exact ignored_update hd ht P _
      rw [e]
      exact ⟨N, k, hd, hb, by simp only [List.length_cons]; omega⟩

private def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

private theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

private theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega

private theorem see_pair (C : Circuit) (i j : Fin 39) : C.eval (oneEach i j) =
    cut C.gates (List.replicate 78 false) C.output {i.val, 39 + j.val} := by
  rw [oneEach_eq]
  change (wiresFrom C.gates (inp 78 _)).getD C.output false = _
  rw [run_eq]
  unfold cut
  have hlen : (inp 78 {i.val,39 + j.val}).length = 78 := by simp [inp]
  rw [hlen, List.length_replicate]
  congr 2
  funext k
  rw [inp_getD]
  have hoff : ∀ n w, (List.replicate n false).getD w false = false := by
    intro n
    induction n with
    | zero => intro w; simp [List.getD_eq_getElem?_getD]
    | succ n ih =>
      intro w
      cases w with
      | zero => simp [List.replicate_succ, List.getD_eq_getElem?_getD]
      | succ w => simp [List.replicate_succ, List.getD_eq_getElem?_getD]
  simp only [readCut, hoff, List.length_replicate, Bool.false_or]

private theorem rows_vary : ∀ i : Fin 39, (∃ j : Fin 39, A i j = true) ∧ (∃ j : Fin 39, A i j = false) := by decide +kernel

private theorem forced_bound : ¬ RepSizeAtMost A 86 := by
  rintro ⟨C, hg, hs, hrep⟩
  let F := cut C.gates (List.replicate 78 false) C.output
  have hm : ∀ {P Q}, P ⊆ Q → F P = true → F Q = true :=
    fun h => cut_mono C.gates (fun g hg' => (hg g hg').1) _ _ h
  have hv : ∀ a b : Fin 39, F {a.val, 39 + b.val} = A a b := by
    intro a b
    change cut C.gates (List.replicate 78 false) C.output {a.val, 39 + b.val} = A a b
    rw [← see_pair]
    exact hrep a b
  have hS₁ : ∀ a : Fin 39, F {a.val} = false := by
    intro a
    obtain ⟨b, hb⟩ := (rows_vary a).2
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {a.val, 39 + b.val}) (by simp) h
    rw [hv, hb] at h'
    contradiction
  have hS₂ : ∀ b : Fin 39, F {39 + b.val} = false := by
    intro b
    obtain ⟨a, ha⟩ := (rows_vary b).2
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {a.val, 39 + b.val}) (by simp) h
    rw [hv, A_sym, ha] at h'
    contradiction
  have h0 : F ∅ = false := by
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {0}) (by simp) h
    have e := hS₁ 0
    exact Bool.false_ne_true (e.symm.trans h')
  obtain ⟨N, k, hd, hb, hsN⟩ := cut_budget C.gates hg _ _ h0
  have hN₁ : ∀ a : Fin 39, a.val ∈ N := by
    intro a
    obtain ⟨b, hb⟩ := (rows_vary a).1
    by_contra h
    have e : F {a.val, 39 + b.val} = F {39 + b.val} := by
      apply hd
      intro i hi
      have hne : i ≠ a.val := fun e => h (e ▸ hi)
      simp [hne]
    rw [hv, hb, hS₂] at e
    contradiction
  have hN₂ : ∀ b : Fin 39, 39 + b.val ∈ N := by
    intro b
    obtain ⟨a, ha⟩ := (rows_vary b).1
    by_contra h
    have e : F {a.val, 39 + b.val} = F {a.val} := by
      apply hd
      intro i hi
      have hne : i ≠ 39 + b.val := fun e => h (e ▸ hi)
      simp [hne]
    rw [hv, A_sym, ha, hS₁] at e
    contradiction
  have hN : Finset.range 78 ⊆ N := by
    intro i hi
    have hh := Finset.mem_range.1 hi
    by_cases h : i < 39
    · exact hN₁ ⟨i, h⟩
    · have hey := hN₂ ⟨i - 39, by omega⟩
      simpa [Nat.add_sub_of_le (by omega : 39 ≤ i)] using hey
  have hc := Finset.card_le_card hN
  rw [Finset.card_range] at hc
  have hsz : C.gates.length ≤ 86 := hs
  have hR := hb A Fin.val (fun b => 39 + b.val) Finset.univ Finset.univ
    ⟨fun a _ => ⟨hN₁ a, hS₁ a⟩, fun b _ => ⟨hN₂ b, hS₂ b⟩, fun a _ b _ => (hv a b).symm⟩
  have hbound := rank_lower hR
  omega

end PEqualNP.Outside.L_meta_10061

theorem PEqualNP.Outside.L_meta_10061 :
¬ (PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 39 => decide (∃ i : Fin 13, ((a.val = i.val ∨ a.val = 13 + i.val) ∧ (b.val = (i.val + 1) % 13 ∨ b.val = 26 + i.val)) ∨ ((b.val = i.val ∨ b.val = 13 + i.val) ∧ (a.val = (i.val + 1) % 13 ∨ a.val = 26 + i.val)))) 86) := by
  exact PEqualNP.Outside.L_meta_10061.forced_bound
