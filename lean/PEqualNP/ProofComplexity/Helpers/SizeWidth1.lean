import PEqualNP.ProofComplexity.Helpers.Completeness
import Mathlib.Tactic

/-!
# Short resolution refutations give narrow ones: the combinatorial part

The system of `Defs/ProofComplexity.lean` has no weakening rule, so the argument runs with two
notions of our own:

* `Der F W C`: the clause `C` has a derivation from `F` in which every clause has at most `W`
  literals (a real derivation, no weakening);
* `SDer F π`: the list `π` is a derivation with weakening allowed at every line. Restricting
  by a literal keeps this notion line by line (`SDer.restrict`), which the real notion does
  not.

`main` is the counting induction: a weakened refutation with few fat clauses gives a real
refutation of small width.
-/

namespace PEqualNP.ProofComplexity.Helpers.SizeWidth

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- The opposite literal. -/
def neg (l : Literal V) : Literal V := (l.1, !l.2)

theorem neg_neg (l : Literal V) : neg (neg l) = l := by
  rcases l with ⟨v, b⟩; simp [neg]

theorem neg_ne (l : Literal V) : neg l ≠ l := by
  rcases l with ⟨v, b⟩; simp [neg]

/-- `Der F W C`: `C` is derivable from `F` by resolution through clauses of at most `W`
literals. -/
inductive Der (F : Set (Clause V)) (W : ℕ) : Clause V → Prop
  | ax {C : Clause V} : C ∈ F → C.card ≤ W → Der F W C
  | res {C D : Clause V} (l : Literal V) : Der F W C → Der F W D → l ∈ C → neg l ∈ D →
      (C.erase l ∪ D.erase (neg l)).card ≤ W → Der F W (C.erase l ∪ D.erase (neg l))

theorem Der.mono {F : Set (Clause V)} {W W' : ℕ} (hW : W ≤ W') {C : Clause V}
    (h : Der F W C) : Der F W' C := by
  induction h with
  | ax hC hc => exact Der.ax hC (hc.trans hW)
  | res l _ _ hl hnl hc ihC ihD => exact Der.res l ihC ihD hl hnl (hc.trans hW)

/-- A `Der` derivation unfolds to a list derivation of the same width. -/
theorem Der.toList {F : Set (Clause V)} {W : ℕ} {C : Clause V} (h : Der F W C) :
    ∃ π : List (Clause V), IsDerivation F π ∧ C ∈ π ∧ ∀ D ∈ π, D.card ≤ W := by
  induction h with
  | @ax C hC hc =>
    refine ⟨[C], IsDerivation.ax IsDerivation.nil hC, by simp, ?_⟩
    intro D hD
    simp only [List.mem_singleton] at hD
    subst hD; exact hc
  | @res C D l _ _ hl hnl hc ihC ihD =>
    obtain ⟨π₁, h₁, hC₁, hw₁⟩ := ihC
    obtain ⟨π₂, h₂, hD₂, hw₂⟩ := ihD
    have happ := Helpers.derivation_append h₁ h₂
    have hCm : C ∈ π₁ ++ π₂ := List.mem_append_left _ hC₁
    have hDm : D ∈ π₁ ++ π₂ := List.mem_append_right _ hD₂
    have hR : IsResolvent C D (C.erase l ∪ D.erase (neg l)) ∨
        IsResolvent D C (C.erase l ∪ D.erase (neg l)) := by
      rcases l with ⟨v, b⟩
      cases b with
      | true => exact Or.inl ⟨v, hl, hnl, rfl⟩
      | false => exact Or.inr ⟨v, hnl, hl, Finset.union_comm _ _⟩
    refine ⟨(C.erase l ∪ D.erase (neg l)) :: (π₁ ++ π₂), ?_, by simp, ?_⟩
    · rcases hR with hR | hR
      · exact IsDerivation.res happ hCm hDm hR
      · exact IsDerivation.res happ hDm hCm hR
    · intro E hE
      rcases List.mem_cons.1 hE with rfl | hE
      · exact hc
      · rcases List.mem_append.1 hE with hE | hE
        · exact hw₁ E hE
        · exact hw₂ E hE

/-- A derivation with weakening at every line, newest clause first. -/
inductive SDer (F : Set (Clause V)) : List (Clause V) → Prop
  | nil : SDer F []
  | ax {π : List (Clause V)} {C A : Clause V} : SDer F π → A ∈ F → A ⊆ C → SDer F (C :: π)
  | res {π : List (Clause V)} {C C1 C2 : Clause V} (l : Literal V) : SDer F π → C1 ∈ π →
      C2 ∈ π → C1.erase l ∪ C2.erase (neg l) ⊆ C → SDer F (C :: π)

theorem SDer.of_derivation {F : Set (Clause V)} {π : List (Clause V)}
    (h : IsDerivation F π) : SDer F π := by
  induction h with
  | nil => exact SDer.nil
  | ax _ hC ih => exact SDer.ax ih hC (Finset.Subset.refl _)
  | res _ hC hD hR ih =>
    obtain ⟨v, hv1, hv2, rfl⟩ := hR
    exact SDer.res (v, true) ih hC hD (Finset.Subset.refl _)

/-- Subsumption in place of weakening: every line of a weakened derivation of width `W` has a
subclause with a real derivation of width `W`. -/
theorem SDer.sub {F : Set (Clause V)} {W : ℕ} (hF : ∀ A ∈ F, A.card ≤ W)
    {π : List (Clause V)} (h : SDer F π) (hw : ∀ C ∈ π, C.card ≤ W) :
    ∀ C ∈ π, ∃ C' : Clause V, C' ⊆ C ∧ Der F W C' := by
  induction h with
  | nil => intro C hC; simp at hC
  | @ax π C A _ hA hAC ih =>
    intro E hE
    rcases List.mem_cons.1 hE with rfl | hE
    · exact ⟨A, hAC, Der.ax hA (hF A hA)⟩
    · exact ih (fun C hC => hw C (List.mem_cons_of_mem _ hC)) E hE
  | @res π C C1 C2 l _ h1 h2 hsub ih =>
    have ih' := ih (fun C hC => hw C (List.mem_cons_of_mem _ hC))
    intro E hE
    rcases List.mem_cons.1 hE with rfl | hE
    · obtain ⟨C1', hs1, hd1⟩ := ih' C1 h1
      obtain ⟨C2', hs2, hd2⟩ := ih' C2 h2
      by_cases hl : l ∈ C1'
      · by_cases hnl : neg l ∈ C2'
        · have hss : C1'.erase l ∪ C2'.erase (neg l) ⊆ E :=
            (Finset.union_subset_union (Finset.erase_subset_erase _ hs1)
              (Finset.erase_subset_erase _ hs2)).trans hsub
          exact ⟨_, hss, Der.res l hd1 hd2 hl hnl
            ((Finset.card_le_card hss).trans (hw E (by simp)))⟩
        · refine ⟨C2', ?_, hd2⟩
          intro x hx
          exact hsub (Finset.mem_union_right _
            (Finset.mem_erase.2 ⟨fun e => hnl (e ▸ hx), hs2 hx⟩))
      · refine ⟨C1', ?_, hd1⟩
        intro x hx
        exact hsub (Finset.mem_union_left _
          (Finset.mem_erase.2 ⟨fun e => hl (e ▸ hx), hs1 hx⟩))
    · exact ih' E hE

/-- The clause set after setting the literal `l` true. -/
def rF (l : Literal V) (F : Set (Clause V)) : Set (Clause V) :=
  {C | ∃ A ∈ F, l ∉ A ∧ C = A.erase (neg l)}

/-- A list of clauses after setting the literal `l` true. -/
def rs (l : Literal V) (π : List (Clause V)) : List (Clause V) :=
  (π.filter (fun C => l ∉ C)).map (fun C => C.erase (neg l))

theorem rs_cons_of_mem {l : Literal V} {C : Clause V} (π : List (Clause V)) (h : l ∈ C) :
    rs l (C :: π) = rs l π := by
  simp [rs, h]

theorem rs_cons_of_not_mem {l : Literal V} {C : Clause V} (π : List (Clause V)) (h : l ∉ C) :
    rs l (C :: π) = C.erase (neg l) :: rs l π := by
  simp [rs, h]

theorem mem_rs {l : Literal V} {π : List (Clause V)} {C : Clause V} (hC : C ∈ π)
    (h : l ∉ C) : C.erase (neg l) ∈ rs l π := by
  simp only [rs, List.mem_map, List.mem_filter]
  exact ⟨C, ⟨hC, by simpa using h⟩, rfl⟩

theorem of_mem_rs {l : Literal V} {π : List (Clause V)} {C' : Clause V} (h : C' ∈ rs l π) :
    ∃ C ∈ π, l ∉ C ∧ C' = C.erase (neg l) := by
  simp only [rs, List.mem_map, List.mem_filter] at h
  obtain ⟨C, ⟨hC, hl⟩, rfl⟩ := h
  exact ⟨C, hC, by simpa using hl, rfl⟩

theorem rF_card {l : Literal V} {F : Set (Clause V)} {k : ℕ} (hF : ∀ A ∈ F, A.card ≤ k) :
    ∀ A ∈ rF l F, A.card ≤ k := by
  rintro _ ⟨A, hA, _, rfl⟩
  exact (Finset.card_erase_le).trans (hF A hA)

/-- Restriction keeps weakened derivations, line by line. -/
theorem SDer.restrict (l : Literal V) {F : Set (Clause V)} {π : List (Clause V)}
    (h : SDer F π) : SDer (rF l F) (rs l π) := by
  induction h with
  | nil => exact SDer.nil
  | @ax π C A _ hA hAC ih =>
    by_cases hl : l ∈ C
    · rw [rs_cons_of_mem π hl]; exact ih
    · rw [rs_cons_of_not_mem π hl]
      exact SDer.ax ih ⟨A, hA, fun h => hl (hAC h), rfl⟩ (Finset.erase_subset_erase _ hAC)
  | @res π C C1 C2 m _ h1 h2 hsub ih =>
    by_cases hl : l ∈ C
    · rw [rs_cons_of_mem π hl]; exact ih
    · rw [rs_cons_of_not_mem π hl]
      by_cases hl1 : l ∈ C1
      · -- then `m = l`, and `C2` survives
        have hml : l = m := by
          by_contra hne
          exact hl (hsub (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hl1⟩)))
        subst hml
        have hl2 : l ∉ C2 := fun h2' =>
          hl (hsub (Finset.mem_union_right _
            (Finset.mem_erase.2 ⟨(neg_ne l).symm, h2'⟩)))
        refine SDer.res l ih (mem_rs h2 hl2) (mem_rs h2 hl2) ?_
        intro x hx
        have hx2 : x ∈ C2.erase (neg l) := by
          rcases Finset.mem_union.1 hx with hx | hx
          · exact Finset.mem_of_mem_erase hx
          · exact Finset.mem_of_mem_erase hx
        exact Finset.mem_erase.2
          ⟨(Finset.mem_erase.1 hx2).1, hsub (Finset.mem_union_right _ hx2)⟩
      · by_cases hl2 : l ∈ C2
        · -- then `l = neg m`, and `C1` survives
          have hml : l = neg m := by
            by_contra hne
            exact hl (hsub (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hne, hl2⟩)))
          have hmn : neg l = m := by rw [hml, neg_neg]
          refine SDer.res l ih (mem_rs h1 hl1) (mem_rs h1 hl1) ?_
          intro x hx
          have hx1 : x ∈ C1.erase (neg l) := by
            rcases Finset.mem_union.1 hx with hx | hx
            · exact Finset.mem_of_mem_erase hx
            · exact Finset.mem_of_mem_erase hx
          refine Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx1).1, ?_⟩
          rw [hmn] at hx1
          exact hsub (Finset.mem_union_left _ hx1)
        · refine SDer.res m ih (mem_rs h1 hl1) (mem_rs h2 hl2) ?_
          intro x hx
          rcases Finset.mem_union.1 hx with hx | hx
          · obtain ⟨hxm, hx⟩ := Finset.mem_erase.1 hx
            obtain ⟨hxl, hx⟩ := Finset.mem_erase.1 hx
            exact Finset.mem_erase.2
              ⟨hxl, hsub (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hxm, hx⟩))⟩
          · obtain ⟨hxm, hx⟩ := Finset.mem_erase.1 hx
            obtain ⟨hxl, hx⟩ := Finset.mem_erase.1 hx
            exact Finset.mem_erase.2
              ⟨hxl, hsub (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hxm, hx⟩))⟩

/-- The number of lines with more than `d` literals. -/
def fat (d : ℕ) (π : List (Clause V)) : ℕ := π.countP (fun C => d < C.card)

/-- The number of lines with more than `d` literals that hold the literal `l`. -/
def cnt (d : ℕ) (l : Literal V) (π : List (Clause V)) : ℕ :=
  π.countP (fun C => d < C.card ∧ l ∈ C)

theorem fat_le_length (d : ℕ) (π : List (Clause V)) : fat d π ≤ π.length :=
  List.countP_le_length

theorem fat_rs (d : ℕ) (l : Literal V) (π : List (Clause V)) :
    fat d (rs l π) + cnt d l π ≤ fat d π := by
  induction π with
  | nil => simp [fat, cnt, rs]
  | cons C π ih =>
    by_cases hl : l ∈ C
    · rw [rs_cons_of_mem π hl]
      by_cases hd : d < C.card
      · simp only [fat, cnt, List.countP_cons, hd, hl] at ih ⊢
        simp only [and_self, decide_true, if_true]
        omega
      · simp only [fat, cnt, List.countP_cons, hd, hl] at ih ⊢
        simp only [false_and, decide_false, Bool.false_eq_true, if_false]
        omega
    · rw [rs_cons_of_not_mem π hl]
      have hc : (C.erase (neg l)).card ≤ C.card := Finset.card_erase_le
      by_cases hd : d < C.card
      · by_cases hd' : d < (C.erase (neg l)).card
        · simp only [fat, cnt, List.countP_cons, hd, hd', hl] at ih ⊢
          simp only [and_false, decide_true, decide_false, Bool.false_eq_true, if_true,
            if_false]
          omega
        · simp only [fat, cnt, List.countP_cons, hd, hd', hl] at ih ⊢
          simp only [and_false, decide_true, decide_false, Bool.false_eq_true, if_true,
            if_false]
          omega
      · have hd' : ¬ d < (C.erase (neg l)).card := by omega
        simp only [fat, cnt, List.countP_cons, hd, hd', hl] at ih ⊢
        simp only [and_false, decide_false, Bool.false_eq_true, if_false]
        omega

theorem sum_cnt (d : ℕ) (L : Finset (Literal V)) :
    ∀ π : List (Clause V), (∀ C ∈ π, C ⊆ L) → (d + 1) * fat d π ≤ ∑ l ∈ L, cnt d l π := by
  intro π
  induction π with
  | nil => intro _; simp [fat, cnt]
  | cons C π ih =>
    intro hsub
    have ih' := ih (fun D hD => hsub D (List.mem_cons_of_mem _ hD))
    have hCL : C ⊆ L := hsub C (by simp)
    have hsplit : ∑ l ∈ L, cnt d l (C :: π) =
        ∑ l ∈ L, cnt d l π + ∑ l ∈ L, (if d < C.card ∧ l ∈ C then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro l _
      by_cases hp : d < C.card ∧ l ∈ C
      · simp [cnt, List.countP_cons, hp]
      · simp [cnt, List.countP_cons, hp]
    rw [hsplit]
    by_cases hd : d < C.card
    · have hsum : ∑ l ∈ L, (if d < C.card ∧ l ∈ C then 1 else 0) = C.card := by
        have : ∀ l ∈ L, (if d < C.card ∧ l ∈ C then 1 else 0) = if l ∈ C then 1 else 0 := by
          intro l _; simp [hd]
        rw [Finset.sum_congr rfl this, ← Finset.card_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.2 hCL]
      have hf : fat d (C :: π) = fat d π + 1 := by simp [fat, List.countP_cons, hd]
      rw [hsum, hf]
      have : (d + 1) * (fat d π + 1) = (d + 1) * fat d π + (d + 1) := by ring
      omega
    · have hsum : ∑ l ∈ L, (if d < C.card ∧ l ∈ C then 1 else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro l _; simp [hd]
      have hf : fat d (C :: π) = fat d π := by simp [fat, List.countP_cons, hd]
      rw [hsum, hf]
      omega

/-- Pigeonhole: some literal lies in a `(d + 1) / |L|` fraction of the fat lines. -/
theorem exists_popular (d : ℕ) (L : Finset (Literal V)) (π : List (Clause V))
    (hsub : ∀ C ∈ π, C ⊆ L) (hpos : 0 < fat d π) :
    ∃ l ∈ L, (d + 1) * fat d π ≤ cnt d l π * L.card := by
  have hs := sum_cnt d L π hsub
  rcases L.eq_empty_or_nonempty with rfl | hne
  · simp at hs; omega
  · refine Finset.exists_le_of_sum_le hne ?_
    rw [Finset.sum_const, smul_eq_mul, ← Finset.sum_mul, mul_comm]
    exact Nat.mul_le_mul_right _ hs

/-- Lifting back: a width `W` derivation from `F` with `l` set true gives a width `W + 1`
derivation from `F` of the same clause, or of that clause with the opposite literal added. -/
theorem lift (l : Literal V) {F : Set (Clause V)} {W : ℕ} {C : Clause V}
    (h : Der (rF l F) W C) :
    (l ∉ C ∧ neg l ∉ C) ∧ (Der F (W + 1) C ∨ Der F (W + 1) (insert (neg l) C)) := by
  induction h with
  | ax hC hW =>
    obtain ⟨A, hA, hl, rfl⟩ := hC
    refine ⟨⟨fun h => hl (Finset.mem_of_mem_erase h), fun h => (Finset.mem_erase.1 h).1 rfl⟩,
      ?_⟩
    by_cases hn : neg l ∈ A
    · right
      rw [Finset.insert_erase hn]
      have := Finset.card_erase_of_mem hn
      exact Der.ax hA (by omega)
    · left
      have he : A.erase (neg l) = A := Finset.erase_eq_self.2 hn
      rw [he] at hW ⊢
      exact Der.ax hA (by omega)
  | @res C D m _ _ hm hnm hW ihC ihD =>
    obtain ⟨⟨hlC, hnC⟩, hC'⟩ := ihC
    obtain ⟨⟨hlD, hnD⟩, hD'⟩ := ihD
    have h1 : neg l ≠ m := fun e => hnC (e ▸ hm)
    have h2 : neg l ≠ neg m := fun e => hnD (e ▸ hnm)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro h
      rcases Finset.mem_union.1 h with h | h
      · exact hlC (Finset.mem_of_mem_erase h)
      · exact hlD (Finset.mem_of_mem_erase h)
    · intro h
      rcases Finset.mem_union.1 h with h | h
      · exact hnC (Finset.mem_of_mem_erase h)
      · exact hnD (Finset.mem_of_mem_erase h)
    · have hcard : (insert (neg l) (C.erase m ∪ D.erase (neg m))).card ≤ W + 1 :=
        (Finset.card_insert_le _ _).trans (by omega)
      rcases hC' with hC' | hC' <;> rcases hD' with hD' | hD'
      · exact Or.inl (Der.res m hC' hD' hm hnm (by omega))
      · right
        have e : C.erase m ∪ (insert (neg l) D).erase (neg m) =
            insert (neg l) (C.erase m ∪ D.erase (neg m)) := by
          rw [Finset.erase_insert_of_ne h2, Finset.union_insert]
        rw [← e]
        exact Der.res m hC' hD' hm (Finset.mem_insert_of_mem hnm) (by rw [e]; exact hcard)
      · right
        have e : (insert (neg l) C).erase m ∪ D.erase (neg m) =
            insert (neg l) (C.erase m ∪ D.erase (neg m)) := by
          rw [Finset.erase_insert_of_ne h1, Finset.insert_union]
        rw [← e]
        exact Der.res m hC' hD' (Finset.mem_insert_of_mem hm) hnm (by rw [e]; exact hcard)
      · right
        have e : (insert (neg l) C).erase m ∪ (insert (neg l) D).erase (neg m) =
            insert (neg l) (C.erase m ∪ D.erase (neg m)) := by
          rw [Finset.erase_insert_of_ne h1, Finset.erase_insert_of_ne h2, Finset.insert_union,
            Finset.union_insert, Finset.insert_idem]
        rw [← e]
        exact Der.res m hC' hD' (Finset.mem_insert_of_mem hm) (Finset.mem_insert_of_mem hnm)
          (by rw [e]; exact hcard)

/-- With the unit clause `{m}` in hand, every derivation from `F` with `m` set true is a
derivation from `F`. -/
theorem unit_resolve (m : Literal V) {F : Set (Clause V)} {W : ℕ} (hu : Der F W {m})
    (hk : ∀ A ∈ F, A.card ≤ W) {C : Clause V} (h : Der (rF m F) W C) : Der F W C := by
  induction h with
  | ax hC hW =>
    obtain ⟨A, hA, hl, rfl⟩ := hC
    by_cases hn : neg m ∈ A
    · have he : A.erase (neg m) ∪ ({m} : Clause V).erase (neg (neg m)) = A.erase (neg m) := by
        rw [neg_neg, Finset.erase_singleton, Finset.union_empty]
      have hmem : neg (neg m) ∈ ({m} : Clause V) := by rw [neg_neg]; simp
      have := Der.res (neg m) (Der.ax hA (hk A hA)) hu hn hmem (by rw [he]; exact hW)
      rwa [he] at this
    · have he : A.erase (neg m) = A := Finset.erase_eq_self.2 hn
      rw [he]
      exact Der.ax hA (hk A hA)
  | res l _ _ hl hnl hW ihC ihD => exact Der.res l ihC ihD hl hnl hW

theorem arith {f f1 c M d Lc b : ℕ} (h1 : f1 + c ≤ f) (h2 : (d + 1) * f ≤ c * Lc)
    (hL : Lc ≤ M) (hM : 0 < M) (h : f * (M - d) ^ (b + 1) < M ^ (b + 1)) :
    f1 * (M - d) ^ b < M ^ b := by
  have h3 : (d + 1) * f ≤ c * M := h2.trans (Nat.mul_le_mul_left _ hL)
  have key : f1 * M ≤ f * (M - d) := by
    by_cases hd : d ≤ M
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
      have he : d + e - d = e := by omega
      rw [he]
      have := Nat.mul_le_mul_right (d + e) h1
      nlinarith
    · have hfc : f ≤ c := by
        by_contra hcf
        have hcf : c + 1 ≤ f := by omega
        have h4 := Nat.mul_le_mul_right M hcf
        have h5 : f * M ≤ f * d := Nat.mul_le_mul_left _ (by omega)
        nlinarith
      have : f1 = 0 := by omega
      simp [this]
  have h6 : f1 * (M - d) ^ b * M < M ^ b * M := by
    calc f1 * (M - d) ^ b * M = f1 * M * (M - d) ^ b := by ring
      _ ≤ f * (M - d) * (M - d) ^ b := Nat.mul_le_mul_right _ key
      _ = f * (M - d) ^ (b + 1) := by ring
      _ < M ^ (b + 1) := h
      _ = M ^ b * M := by ring
  exact Nat.lt_of_mul_lt_mul_right h6

/-- The counting induction: a weakened refutation of `F` over the literals `L`, with fewer
than `(M / (M - d)) ^ b` fat lines, gives a real refutation of width `d + b + k`. -/
theorem main (M d k : ℕ) : ∀ (n : ℕ) (L : Finset (Literal V)) (F : Set (Clause V))
    (π : List (Clause V)) (b : ℕ), L.card ≤ n → L.card ≤ M → (∀ A ∈ F, A.card ≤ k) →
    SDer F π → (∅ : Clause V) ∈ π → (∀ C ∈ π, C ⊆ L) →
    fat d π * (M - d) ^ b < M ^ b → Der F (d + b + k) ∅ := by
  have base : ∀ (F : Set (Clause V)) (π : List (Clause V)) (b : ℕ),
      (∀ A ∈ F, A.card ≤ k) → SDer F π → (∅ : Clause V) ∈ π → fat d π = 0 →
      Der F (d + b + k) ∅ := by
    intro F π b hk hS hemp hf
    have hw : ∀ C ∈ π, C.card ≤ d + b + k := by
      intro C hC
      have := (List.countP_eq_zero.1 hf) C hC
      simp only [decide_eq_true_eq, not_lt] at this
      omega
    obtain ⟨C', hsub, hder⟩ :=
      hS.sub (W := d + b + k) (fun A hA => (hk A hA).trans (by omega)) hw ∅ hemp
    rw [Finset.subset_empty.1 hsub] at hder
    exact hder
  intro n
  induction n with
  | zero =>
    intro L F π b hLn hLM hk hS hemp hsub hb
    by_cases hf : fat d π = 0
    · exact base F π b hk hS hemp hf
    · obtain ⟨l, hl, -⟩ := exists_popular d L π hsub (Nat.pos_of_ne_zero hf)
      have : L = ∅ := Finset.card_eq_zero.1 (by omega)
      rw [this] at hl
      simp at hl
  | succ n ih =>
    intro L F π b hLn hLM hk hS hemp hsub hb
    by_cases hf : fat d π = 0
    · exact base F π b hk hS hemp hf
    · have hpos : 0 < fat d π := Nat.pos_of_ne_zero hf
      obtain ⟨l, hl, hpop⟩ := exists_popular d L π hsub hpos
      have hLe : (L.erase l).card ≤ n := by
        rw [Finset.card_erase_of_mem hl]; omega
      have hLeM : (L.erase l).card ≤ M := (Finset.card_erase_le).trans hLM
      cases b with
      | zero => simp at hb; omega
      | succ b =>
        have hM : 0 < M := by
          rcases Nat.eq_zero_or_pos M with h0 | h0
          · subst h0; simp at hb
          · exact h0
        have hb1 : fat d (rs l π) * (M - d) ^ b < M ^ b :=
          arith (fat_rs d l π) hpop hLM hM hb
        have hemp1 : (∅ : Clause V) ∈ rs l π := by
          have := mem_rs (l := l) hemp (by simp)
          simpa using this
        have hsub1 : ∀ C ∈ rs l π, C ⊆ L.erase l := by
          intro C' hC'
          obtain ⟨C, hC, hlC, rfl⟩ := of_mem_rs hC'
          intro x hx
          have hxC := Finset.mem_of_mem_erase hx
          exact Finset.mem_erase.2 ⟨fun e => hlC (e ▸ hxC), hsub C hC hxC⟩
        have ih1 := ih (L.erase l) (rF l F) (rs l π) b hLe hLeM (rF_card hk)
          (hS.restrict l) hemp1 hsub1 hb1
        obtain ⟨-, h | h⟩ := lift l ih1
        · exact h.mono (by omega)
        · have hu : Der F (d + (b + 1) + k) {neg l} := by
            have h' : Der F (d + b + k + 1) {neg l} := by simpa using h
            exact h'.mono (by omega)
          have hemp2 : (∅ : Clause V) ∈ rs (neg l) π := by
            have := mem_rs (l := neg l) hemp (by simp)
            simpa using this
          have hsub2 : ∀ C ∈ rs (neg l) π, C ⊆ L.erase l := by
            intro C' hC'
            obtain ⟨C, hC, hlC, rfl⟩ := of_mem_rs hC'
            rw [neg_neg]
            exact Finset.erase_subset_erase _ (hsub C hC)
          have hb2 : fat d (rs (neg l) π) * (M - d) ^ (b + 1) < M ^ (b + 1) := by
            have := fat_rs d (neg l) π
            exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hb
          have ih2 := ih (L.erase l) (rF (neg l) F) (rs (neg l) π) (b + 1) hLe hLeM
            (rF_card hk) (hS.restrict (neg l)) hemp2 hsub2 hb2
          exact unit_resolve (neg l) hu (fun A hA => (hk A hA).trans (by omega)) ih2

end PEqualNP.ProofComplexity.Helpers.SizeWidth
