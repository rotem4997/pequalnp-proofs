import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6262

def U {α : Type} (F : Set (Set α)) : Set (Set α) := {x8 : Set α | ∃ x9 ⊆ F, x8 = ⋃₀ x9}

def ext8 {α : Type} (F : Set (Set α)) (p : Set α × Set α) : Set (Set α) :=
  F ∪ {x10 : Set α | p.1 ∈ U F ∧ p.2 ∈ U F ∧ x10 = p.1 ∩ p.2}

def Z {α : Type} (f : α → List Bool) (i : ℕ) : Set α :=
  {a : α | (f a).getD i Bool.false = Bool.false}

def stepf (w : List Bool) (p : Finset ℕ × Finset ℕ) : List Bool :=
  w ++ [Decidable.decide (∀ x13 ∈ p.1, w.getD x13 Bool.false = Bool.true) ||
    Decidable.decide (∀ x13 ∈ p.2, w.getD x13 Bool.false = Bool.true)]

theorem g1 (w : List Bool) (v : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem g2 (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem g3 (w : List Bool) (v : Bool) (i : ℕ) (h : w.length < i) :
    (w ++ [v]).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem fin {α : Type} (g : α → List Bool) (x6 : Finset ℕ) (F : Set (Set α))
    (h : Set.range (Z g) ⊆ F) :
    {a : α | ∃ i ∈ x6, (g a).getD i Bool.false = Bool.false} ∈ U F := by
  show ∃ x9 ⊆ F, _ = ⋃₀ x9
  refine ⟨Z g '' (↑x6 : Set ℕ), (Set.image_subset_range _ _).trans h, ?_⟩
  ext a
  simp [Z]

theorem key {α : Type} (ps : List (Finset ℕ × Finset ℕ)) :
    ∀ (f : α → List Bool) (n : ℕ), (∀ a, (f a).length = n) → ∀ F : Set (Set α),
      Set.range (Z f) ⊆ F →
      ∃ l : List (Set α × Set α), l.length = ps.length ∧
        Set.range (Z fun a => List.foldl stepf (f a) ps) ⊆ List.foldl ext8 F l := by
  induction ps with
  | nil =>
    intro f n _ F hF
    exact ⟨[], rfl, hF⟩
  | cons p ps ih =>
    intro f n hlen F hF
    have hA := fin f p.1 F hF
    have hB := fin f p.2 F hF
    obtain ⟨l, hl, hsub⟩ := ih (fun a => stepf (f a) p) (n + 1)
      (by intro a; simp [stepf, hlen a])
      (ext8 F ({a : α | ∃ i ∈ p.1, (f a).getD i Bool.false = Bool.false},
        {a : α | ∃ i ∈ p.2, (f a).getD i Bool.false = Bool.false})) (by
      rintro _ ⟨i, rfl⟩
      rcases lt_trichotomy i n with h | h | h
      · left
        apply hF
        refine ⟨i, ?_⟩
        ext a
        simp only [Z, stepf, Set.mem_setOf_eq]
        rw [g1 _ _ _ (by rw [hlen a]; exact h)]
      · right
        refine ⟨hA, hB, ?_⟩
        subst h
        ext a
        simp only [Z, stepf, Set.mem_setOf_eq, Set.mem_inter_iff]
        rw [← hlen a, g2]
        simp
      · left
        apply hF
        refine ⟨i, ?_⟩
        ext a
        simp only [Z, stepf, Set.mem_setOf_eq]
        rw [g3 _ _ _ (by rw [hlen a]; exact h)])
    exact ⟨(_, _) :: l, by simp [hl], hsub⟩

end PEqualNP.Outside.L_meta_6262

theorem PEqualNP.Outside.L_meta_6262 : ∀ (x1 : Type) (x2 : x1 → List Bool) (x3 : ℕ),   (∀ (x4 : x1), (x2 x4).length = x3) →     ∀ (x5 : List (Finset ℕ × Finset ℕ)) (x6 : Finset ℕ),       have x7 : Set (Set x1) → Set (Set x1) := fun (x7 : Set (Set x1)) => {x8 : Set x1 | ∃ x9 ⊆ x7, x8 = ⋃₀ x9};       have x8 : Set (Set x1) → Set x1 × Set x1 → Set (Set x1) := fun (x8 : Set (Set x1)) (x9 : Set x1 × Set x1) => x8 ∪ {x10 : Set x1 | x9.1 ∈ x7 x8 ∧ x9.2 ∈ x7 x8 ∧ x10 = x9.1 ∩ x9.2};       have x9 : (x1 → List Bool) → ℕ → Set x1 := fun (x9 : x1 → List Bool) (x10 : ℕ) => {x11 : x1 | (x9 x11).getD x10 Bool.false = Bool.false};       have x10 : x1 → List Bool := fun (x10 : x1) => List.foldl (fun (x11 : List Bool) (x12 : Finset ℕ × Finset ℕ) => x11 ++ [Decidable.decide (∀ x13 ∈ x12.1, x11.getD x13 Bool.false = Bool.true) || Decidable.decide (∀ x13 ∈ x12.2, x11.getD x13 Bool.false = Bool.true)]) (x2 x10) x5;       ∃ (x11 : List (Set x1 × Set x1)), x11.length = x5.length ∧ {x12 : x1 | ∃ x13 ∈ x6, (x10 x12).getD x13 Bool.false = Bool.false} ∈ x7 (List.foldl x8 (Set.range (x9 x2)) x11) := by
  intro x1 x2 x3 hlen x5 x6
  obtain ⟨l, hl, hsub⟩ := PEqualNP.Outside.L_meta_6262.key x5 x2 x3 hlen
    (Set.range (PEqualNP.Outside.L_meta_6262.Z x2)) subset_rfl
  exact ⟨l, hl, PEqualNP.Outside.L_meta_6262.fin _ x6 _ hsub⟩
