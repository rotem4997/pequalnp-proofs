import Mathlib
import PEqualNP.Defs.CoverPromise

/-!
# Promise vertex cover: the combinatorial core of its coNP-hardness

From a CNF formula `φ` an explicit graph and an explicit vertex cover of it are built, such that
the cover is always within one of a minimum cover, and it is a minimum cover exactly when `φ` is
unsatisfiable.

The construction: `φ' = {C ∨ y : C ∈ φ} ∪ {¬y}` with `y` a fresh variable, then the textbook
reduction from CNF satisfiability to vertex cover on `φ'` (an edge between the two literals of
every variable that occurs, a clique on the occurrences of every clause, every occurrence joined
to its literal). The cover is the one read off the assignment "everything true".

The definitions are in `Defs/CoverPromise.lean`.
-/

namespace PEqualNP.MetaComplexity.CoverPromise

open PEqualNP.Search

/-! ## Basic facts -/

lemma mem_vars {ψ : CNF} {x : ℕ} : x ∈ vars ψ ↔ ∃ c ∈ ψ, ∃ b, (x, b) ∈ c := by
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨c, hc, ⟨y, b⟩, hl, rfl⟩
    exact ⟨c, hc, b, hl⟩
  · rintro ⟨c, hc, b, hl⟩
    exact ⟨c, hc, (x, b), hl, rfl⟩

lemma clauseAt_mem {ψ : CNF} {i : ℕ} (h : i < ψ.length) : clauseAt ψ i ∈ ψ := by
  simp [clauseAt, List.getElem?_eq_getElem h]

lemma lt_length_of_clauseAt {ψ : CNF} {i : ℕ} (h : 0 < (clauseAt ψ i).length) :
    i < ψ.length := by
  by_contra h'
  simp [clauseAt, List.getElem?_eq_none (Nat.le_of_not_lt h')] at h

lemma mem_vars_of_get {ψ : CNF} {i j x : ℕ} {b : Bool}
    (h : (clauseAt ψ i)[j]? = some (x, b)) : x ∈ vars ψ := by
  have hj : j < (clauseAt ψ i).length := (List.getElem?_eq_some_iff.mp h).1
  have hi : i < ψ.length := lt_length_of_clauseAt (by omega)
  exact mem_vars.mpr ⟨_, clauseAt_mem hi, b, List.mem_of_getElem? h⟩

lemma mem_coverOf_inl {ψ : CNF} {σ : Assignment} {x : ℕ} {a : Bool} :
    Sum.inl (x, a) ∈ coverOf ψ σ ↔ x ∈ vars ψ ∧ σ x = a := by
  simp [coverOf]

lemma mem_coverOf_inr {ψ : CNF} {σ : Assignment} {i j : ℕ} :
    Sum.inr (i, j) ∈ coverOf ψ σ ↔ i < ψ.length ∧ j < (clauseAt ψ i).length ∧
      j ≠ (clauseAt ψ i).findIdx (Literal.eval σ) := by
  simp [coverOf]

/-! ## The cover read off an assignment -/

theorem coverOf_isVertexCover (ψ : CNF) (σ : Assignment) :
    IsVertexCover (satGraph ψ) (coverOf ψ σ) := by
  rintro (⟨x, a⟩ | ⟨i, j⟩) (⟨y, b⟩ | ⟨k, l⟩) h <;>
    simp only [satGraph, satAdj] at h <;>
    simp only [mem_coverOf_inl, mem_coverOf_inr]
  · obtain ⟨rfl, hab, hx⟩ := h
    cases a <;> cases b <;> cases hσ : σ x <;> simp_all
  · -- an occurrence `(k, l)` and its literal `(x, a)`
    have hl : l < (clauseAt ψ k).length := (List.getElem?_eq_some_iff.mp h).1
    have hk : k < ψ.length := lt_length_of_clauseAt (by omega)
    by_cases hf : l = (clauseAt ψ k).findIdx (Literal.eval σ)
    · left
      refine ⟨mem_vars_of_get h, ?_⟩
      have hlt : (clauseAt ψ k).findIdx (Literal.eval σ) < (clauseAt ψ k).length := hf ▸ hl
      have := List.findIdx_getElem (w := hlt)
      have he : (clauseAt ψ k)[(clauseAt ψ k).findIdx (Literal.eval σ)] = (x, a) := by
        have := (List.getElem?_eq_some_iff.mp h).2
        subst hf
        exact this
      rw [he] at this
      simpa [Literal.eval] using this
    · right
      exact ⟨hk, hl, hf⟩
  · have hj : j < (clauseAt ψ i).length := (List.getElem?_eq_some_iff.mp h).1
    have hi : i < ψ.length := lt_length_of_clauseAt (by omega)
    by_cases hf : j = (clauseAt ψ i).findIdx (Literal.eval σ)
    · right
      refine ⟨mem_vars_of_get h, ?_⟩
      have hlt : (clauseAt ψ i).findIdx (Literal.eval σ) < (clauseAt ψ i).length := hf ▸ hj
      have := List.findIdx_getElem (w := hlt)
      have he : (clauseAt ψ i)[(clauseAt ψ i).findIdx (Literal.eval σ)] = (y, b) := by
        have := (List.getElem?_eq_some_iff.mp h).2
        subst hf
        exact this
      rw [he] at this
      simpa [Literal.eval] using this
    · left
      exact ⟨hi, hj, hf⟩
  · obtain ⟨rfl, hjl, hj, hl⟩ := h
    have hi : i < ψ.length := lt_length_of_clauseAt (by omega)
    by_cases hf : j = (clauseAt ψ i).findIdx (Literal.eval σ)
    · right
      exact ⟨hi, hl, fun h' => hjl (hf.trans h'.symm)⟩
    · left
      exact ⟨hi, hj, hf⟩

theorem card_coverOf (ψ : CNF) (σ : Assignment) :
    (coverOf ψ σ).card = (vars ψ).card + ∑ i ∈ Finset.range ψ.length,
      ((clauseAt ψ i).length - if Clause.eval σ (clauseAt ψ i) then 1 else 0) := by
  rw [coverOf, Finset.card_disjSum,
    Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1), Finset.card_biUnion]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2), Finset.filter_ne',
      Clause.eval]
    by_cases h : (clauseAt ψ i).findIdx (Literal.eval σ) < (clauseAt ψ i).length
    · have h' : (clauseAt ψ i).any (Literal.eval σ) = true := by
        obtain ⟨e, he, hp⟩ := List.findIdx_lt_length.mp h
        exact List.any_eq_true.mpr ⟨e, he, hp⟩
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr h), Finset.card_range, h']
      simp
    · have h' : (clauseAt ψ i).any (Literal.eval σ) = false := by
        rw [Bool.eq_false_iff]
        intro hh
        obtain ⟨e, he, hp⟩ := List.any_eq_true.mp hh
        exact h (List.findIdx_lt_length.mpr ⟨e, he, hp⟩)
      rw [Finset.erase_eq_of_notMem (by simpa using h), Finset.card_range, h']
      simp
  · intro i _ k _ hik
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨_, _, rfl⟩ := hp
    obtain ⟨_, _, h⟩ := hp'
    exact hik (Prod.mk.inj h).1.symm

/-! ## Every cover is large -/

section Lower

variable {ψ : CNF} {S : Finset Vertex}

lemma vars_subset (hS : IsVertexCover (satGraph ψ) S) :
    vars ψ ⊆ S.toLeft.image Prod.fst := by
  intro x hx
  have := hS (.inl (x, true)) (.inl (x, false)) ⟨rfl, by simp, hx⟩
  rcases this with h | h
  · exact Finset.mem_image.mpr ⟨(x, true), by simpa using h, rfl⟩
  · exact Finset.mem_image.mpr ⟨(x, false), by simpa using h, rfl⟩

lemma card_left (hS : IsVertexCover (satGraph ψ) S) : (vars ψ).card ≤ S.toLeft.card :=
  (Finset.card_le_card (vars_subset hS)).trans Finset.card_image_le

lemma card_left_strict (hS : IsVertexCover (satGraph ψ) S) {x : ℕ} (hx : x ∈ vars ψ)
    (ht : Sum.inl (x, true) ∈ S) (hf : Sum.inl (x, false) ∈ S) :
    (vars ψ).card + 1 ≤ S.toLeft.card := by
  have hsub : vars ψ ⊆ (S.toLeft.erase (x, false)).image Prod.fst := by
    intro z hz
    by_cases hzx : z = x
    · subst hzx
      exact Finset.mem_image.mpr ⟨(z, true), by simpa using ht, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (vars_subset hS hz)
      refine Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨?_, hp⟩, rfl⟩
      rintro rfl
      exact hzx rfl
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 := Finset.card_erase_add_one (s := S.toLeft) (a := (x, false)) (by simpa using hf)
  omega

/-- The occurrences of clause `i` that lie in `S`. -/
def inClause (S : Finset Vertex) (ψ : CNF) (i : ℕ) : Finset ℕ :=
  (Finset.range (clauseAt ψ i).length).filter fun j => Sum.inr (i, j) ∈ S

lemma card_inClause (hS : IsVertexCover (satGraph ψ) S) (i : ℕ) :
    (clauseAt ψ i).length - 1 ≤ (inClause S ψ i).card := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.range (clauseAt ψ i).length) (fun j => Sum.inr (i, j) ∈ S)
  have h2 : ((Finset.range (clauseAt ψ i).length).filter
      fun j => ¬ Sum.inr (i, j) ∈ S).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro j hj l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hj hl
    by_contra hjl
    rcases hS _ _ (show (satGraph ψ).Adj (.inr (i, j)) (.inr (i, l)) from
      ⟨rfl, hjl, hj.1, hl.1⟩) with h | h
    · exact hj.2 h
    · exact hl.2 h
  rw [Finset.card_range] at h1
  unfold inClause
  omega

lemma card_right_aux :
    ∑ i ∈ Finset.range ψ.length, (inClause S ψ i).card ≤ S.toRight.card := by
  calc ∑ i ∈ Finset.range ψ.length, (inClause S ψ i).card
      = ((Finset.range ψ.length).biUnion fun i =>
          (inClause S ψ i).image fun j => (i, j)).card := by
        rw [Finset.card_biUnion]
        · exact Finset.sum_congr rfl fun i _ =>
            (Finset.card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)).symm
        · intro i _ k _ hik
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro p hp hp'
          simp only [Finset.mem_image] at hp hp'
          obtain ⟨_, _, rfl⟩ := hp
          obtain ⟨_, _, h⟩ := hp'
          exact hik (Prod.mk.inj h).1.symm
    _ ≤ S.toRight.card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_biUnion, Finset.mem_image, inClause, Finset.mem_filter] at hp
        obtain ⟨i, -, j, ⟨-, h⟩, rfl⟩ := hp
        simpa using h

lemma card_right (hS : IsVertexCover (satGraph ψ) S) :
    ∑ i ∈ Finset.range ψ.length, ((clauseAt ψ i).length - 1) ≤ S.toRight.card :=
  (Finset.sum_le_sum fun i _ => card_inClause hS i).trans card_right_aux

lemma card_right_strict (hS : IsVertexCover (satGraph ψ) S) {i : ℕ}
    (hpos : 0 < (clauseAt ψ i).length)
    (hall : ∀ j < (clauseAt ψ i).length, Sum.inr (i, j) ∈ S) :
    ∑ i ∈ Finset.range ψ.length, ((clauseAt ψ i).length - 1) + 1 ≤ S.toRight.card := by
  have hi : i ∈ Finset.range ψ.length := Finset.mem_range.mpr (lt_length_of_clauseAt hpos)
  have hfull : (inClause S ψ i).card = (clauseAt ψ i).length := by
    unfold inClause
    rw [Finset.filter_true_of_mem (fun j hj => hall j (Finset.mem_range.mp hj)),
      Finset.card_range]
  have : ∑ i ∈ Finset.range ψ.length, ((clauseAt ψ i).length - 1) <
      ∑ i ∈ Finset.range ψ.length, (inClause S ψ i).card :=
    Finset.sum_lt_sum (fun k _ => card_inClause hS k) ⟨i, hi, by omega⟩
  exact (Nat.succ_le_of_lt this).trans card_right_aux

/-- The lower bound of the textbook reduction: the number of occurring variables plus, per
clause, its length minus one. -/
def base (ψ : CNF) : ℕ :=
  (vars ψ).card + ∑ i ∈ Finset.range ψ.length, ((clauseAt ψ i).length - 1)

theorem base_le_card (hS : IsVertexCover (satGraph ψ) S) : base ψ ≤ S.card := by
  have := card_left hS
  have := card_right hS
  have := Finset.card_toLeft_add_card_toRight (u := S)
  unfold base
  omega

theorem base_lt_card (hS : IsVertexCover (satGraph ψ) S) (hne : ∀ c ∈ ψ, c ≠ [])
    (hns : ¬ Satisfiable ψ) : base ψ < S.card := by
  let σ : Assignment := fun x => decide (Sum.inl (x, true) ∈ S)
  have hev : ¬ CNF.eval σ ψ = true := fun h => hns ⟨σ, h⟩
  simp only [CNF.eval, List.all_eq_true, not_forall] at hev
  obtain ⟨c, hc, hcf⟩ := hev
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hci : clauseAt ψ i = ψ[i] := by simp [clauseAt, List.getElem?_eq_getElem hi]
  have hL := card_left hS
  have hR := card_right hS
  have hsum := Finset.card_toLeft_add_card_toRight (u := S)
  unfold base
  by_cases hall : ∀ j < (clauseAt ψ i).length, Sum.inr (i, j) ∈ S
  · have hpos : 0 < (clauseAt ψ i).length := by
      rw [hci]; exact List.length_pos_iff.mpr (hne _ hc)
    have := card_right_strict hS hpos hall
    omega
  · push Not at hall
    obtain ⟨j, hj, hjS⟩ := hall
    have hget : (clauseAt ψ i)[j]? = some ((clauseAt ψ i)[j]) := List.getElem?_eq_getElem hj
    rcases hlit : (clauseAt ψ i)[j] with ⟨x, b⟩
    rw [hlit] at hget
    have hin : Sum.inl (x, b) ∈ S :=
      (hS _ _ (show (satGraph ψ).Adj (.inr (i, j)) (.inl (x, b)) from hget)).resolve_left hjS
    have hmem : (x, b) ∈ ψ[i] := by rw [← hci]; exact List.mem_of_getElem? hget
    have hfalse : ¬ Literal.eval σ (x, b) = true := by
      intro h
      exact hcf (List.any_eq_true.mpr ⟨_, hmem, h⟩)
    cases b
    · have ht : Sum.inl (x, true) ∈ S := by simpa [Literal.eval, σ] using hfalse
      have := card_left_strict hS (mem_vars_of_get hget) ht hin
      omega
    · exact absurd (by simpa [Literal.eval, σ] using hin) hfalse

end Lower

/-! ## Sums over clauses -/

lemma sum_range_clauseAt (f : Clause → ℕ) :
    ∀ ψ : CNF, ∑ i ∈ Finset.range ψ.length, f (clauseAt ψ i) = (ψ.map f).sum
  | [] => by simp
  | c :: ψ => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
      ← sum_range_clauseAt f ψ]
    simp [clauseAt, add_comm]

lemma base_eq (ψ : CNF) : base ψ = (vars ψ).card + (ψ.map fun c => c.length - 1).sum := by
  rw [base, sum_range_clauseAt (fun c => c.length - 1)]

lemma card_coverOf' (ψ : CNF) (σ : Assignment) :
    (coverOf ψ σ).card = (vars ψ).card +
      (ψ.map fun c => c.length - if Clause.eval σ c then 1 else 0).sum := by
  rw [card_coverOf, sum_range_clauseAt (fun c => c.length - if Clause.eval σ c then 1 else 0)]

lemma card_coverOf_of_eval {ψ : CNF} {σ : Assignment} (h : CNF.eval σ ψ = true) :
    (coverOf ψ σ).card = base ψ := by
  rw [card_coverOf', base_eq]
  congr 2
  refine List.map_congr_left fun c hc => ?_
  have : Clause.eval σ c = true := List.all_eq_true.mp h c hc
  simp [this]

/-! ## The vertices that carry edges -/

/-- The vertices carrying an edge of the textbook graph of `ψ` lie in an explicit finite set:
both literals of every occurring variable, and every occurrence `(i, j)` with `i` a clause index
and `j` a position in that clause. Its size is at most twice the number of variables plus the
number of literal occurrences. -/
theorem support_finite (ψ : CNF) :
    ∃ T : Finset Vertex, (∀ u v, (satGraph ψ).Adj u v → u ∈ T ∧ v ∈ T) ∧
      T.card ≤ 2 * (vars ψ).card + (ψ.map List.length).sum := by
  refine ⟨((vars ψ) ×ˢ (Finset.univ : Finset Bool)).disjSum
    ((Finset.range ψ.length).biUnion fun i =>
      (Finset.range (clauseAt ψ i).length).image fun j => (i, j)), ?_, ?_⟩
  · have hocc : ∀ {i j : ℕ}, j < (clauseAt ψ i).length →
        (Sum.inr (i, j) : Vertex) ∈ ((vars ψ) ×ˢ (Finset.univ : Finset Bool)).disjSum
          ((Finset.range ψ.length).biUnion fun i =>
            (Finset.range (clauseAt ψ i).length).image fun j => (i, j)) := by
      intro i j hj
      have hi : i < ψ.length := lt_length_of_clauseAt (by omega)
      simp only [Finset.inr_mem_disjSum, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
      exact ⟨i, hi, j, hj, rfl⟩
    rintro (⟨x, a⟩ | ⟨i, j⟩) (⟨y, b⟩ | ⟨k, l⟩) h <;> simp only [satGraph, satAdj] at h
    · obtain ⟨rfl, -, hx⟩ := h
      simp [hx]
    · refine ⟨?_, hocc (List.getElem?_eq_some_iff.mp h).1⟩
      simp [mem_vars_of_get h]
    · refine ⟨hocc (List.getElem?_eq_some_iff.mp h).1, ?_⟩
      simp [mem_vars_of_get h]
    · obtain ⟨rfl, -, hj, hl⟩ := h
      exact ⟨hocc hj, hocc hl⟩
  · rw [Finset.card_disjSum, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    have hR : ((Finset.range ψ.length).biUnion fun i =>
        (Finset.range (clauseAt ψ i).length).image fun j => (i, j)).card ≤
          (ψ.map List.length).sum := by
      rw [← sum_range_clauseAt List.length]
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.card_image_le.trans (Finset.card_range _).le
    omega

/-! ## The formula `φ'` -/

lemma fresh_not_mem (φ : CNF) : fresh φ ∉ vars φ := by
  intro h
  have : fresh φ ≤ (vars φ).sup id := Finset.le_sup (f := id) h
  unfold fresh at this
  omega

lemma cvcFormula_ne_nil (φ : CNF) : ∀ c ∈ cvcFormula φ, c ≠ [] := by
  simp only [cvcFormula, List.mem_append, List.mem_map, List.mem_singleton]
  rintro c (⟨a, -, rfl⟩ | rfl) <;> simp

theorem sat_cvcFormula (φ : CNF) : Satisfiable (cvcFormula φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨σ, h⟩
    refine ⟨σ, ?_⟩
    simp only [cvcFormula, CNF.eval, List.all_append, List.all_map, Bool.and_eq_true,
      List.all_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have hy : σ (fresh φ) = false := by
      simpa [Function.comp, Clause.eval, Literal.eval] using h2
    intro c hc
    have := h1 c hc
    simpa [Function.comp, Clause.eval, Literal.eval, hy] using this
  · rintro ⟨σ, h⟩
    refine ⟨Function.update σ (fresh φ) false, ?_⟩
    simp only [cvcFormula, CNF.eval, List.all_append, List.all_map, Bool.and_eq_true,
      List.all_eq_true] at h ⊢
    refine ⟨fun c hc => ?_, by simp [Clause.eval, Literal.eval]⟩
    obtain ⟨⟨x, b⟩, hl, hv⟩ := List.any_eq_true.mp (h c hc)
    have hx : x ≠ fresh φ := by
      rintro rfl
      exact fresh_not_mem φ (mem_vars.mpr ⟨c, hc, b, hl⟩)
    simp only [Function.comp, Clause.eval, List.any_append, Bool.or_eq_true]
    left
    exact List.any_eq_true.mpr ⟨(x, b), hl, by simpa [Literal.eval, hx] using hv⟩

lemma card_cvcCover (φ : CNF) : (cvcCover φ).card = base (cvcFormula φ) + 1 := by
  rw [cvcCover, card_coverOf', base_eq]
  have h1 : ∀ c : Clause, Clause.eval (fun _ => true) (c ++ [(fresh φ, true)]) = true := by
    intro c; simp [Clause.eval, Literal.eval]
  have h2 : Clause.eval (fun _ => true) [(fresh φ, false)] = false := by
    simp [Clause.eval, Literal.eval]
  simp only [cvcFormula, List.map_append, List.map_map, List.sum_append, Function.comp_def, h1,
    h2, ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp
  omega

/-! ## The theorems -/

/-- The explicit cover is a vertex cover of the explicit graph. -/
theorem cvc_cover (φ : CNF) : IsVertexCover (cvcGraph φ) (cvcCover φ) :=
  coverOf_isVertexCover _ _

/-- The explicit cover is within one of every vertex cover. -/
theorem cvc_within_one (φ : CNF) :
    ∀ S, IsVertexCover (cvcGraph φ) S → (cvcCover φ).card ≤ S.card + 1 := by
  intro S hS
  rw [card_cvcCover]
  have := base_le_card hS
  omega

/-- The explicit cover is a minimum vertex cover exactly when `φ` is unsatisfiable. -/
theorem cvc_minimum_iff (φ : CNF) :
    (∀ S, IsVertexCover (cvcGraph φ) S → (cvcCover φ).card ≤ S.card) ↔ ¬ Satisfiable φ := by
  constructor
  · intro h hsat
    obtain ⟨σ, hσ⟩ := (sat_cvcFormula φ).mpr hsat
    have h1 := h _ (coverOf_isVertexCover (cvcFormula φ) σ)
    rw [card_cvcCover, card_coverOf_of_eval hσ] at h1
    omega
  · intro hns S hS
    rw [card_cvcCover]
    exact base_lt_card hS (cvcFormula_ne_nil φ) (fun h => hns ((sat_cvcFormula φ).mp h))

/-! ## Sanity: the definitions are not degenerate -/

/-- Every variable occurring in `φ` gives an edge of the graph. -/
theorem cvcGraph_adj_of_occurs {φ : CNF} {c : Clause} {x : ℕ} {b : Bool} (hc : c ∈ φ)
    (hx : (x, b) ∈ c) : (cvcGraph φ).Adj (.inl (x, true)) (.inl (x, false)) := by
  refine ⟨rfl, by simp, mem_vars.mpr ⟨c ++ [(fresh φ, true)], ?_, b, ?_⟩⟩
  · simp only [cvcFormula, List.mem_append, List.mem_map]
    exact Or.inl ⟨c, hc, rfl⟩
  · simp [hx]

/-- A satisfiable formula: the cover is not minimum. -/
example : ¬ ∀ S, IsVertexCover (cvcGraph [[(0, true)]]) S →
    (cvcCover [[(0, true)]]).card ≤ S.card := by
  rw [cvc_minimum_iff, not_not]
  exact ⟨fun _ => true, by decide⟩

/-- An unsatisfiable formula: the cover is minimum. -/
example : ∀ S, IsVertexCover (cvcGraph [[(0, true)], [(0, false)]]) S →
    (cvcCover [[(0, true)], [(0, false)]]).card ≤ S.card := by
  rw [cvc_minimum_iff]
  rintro ⟨σ, h⟩
  cases h0 : σ 0 <;> simp [CNF.eval, Clause.eval, Literal.eval, h0] at h

/-- The cover of the unsatisfiable example has five vertices. -/
example : (cvcCover [[(0, true)], [(0, false)]]).card = 5 := by
  decide

end PEqualNP.MetaComplexity.CoverPromise
