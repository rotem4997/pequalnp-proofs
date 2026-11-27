import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9250

open PEqualNP.ProofComplexity PEqualNP.Search

abbrev VV : Type := Fin (4 + 1) × Fin 4

def c0 : Clause VV := ({((0, 1), false), ((2, 2), true), ((4, 0), false)} : Clause VV)

def c1 : Clause VV := ({((3, 2), false), ((4, 0), false)} : Clause VV)

def c2 : Clause VV := ({((1, 1), false), ((4, 0), false)} : Clause VV)

def c3 : Clause VV := ({((1, 2), true), ((4, 0), false)} : Clause VV)

def c4 : Clause VV := ({((4, 0), false)} : Clause VV)

def c5 : Clause VV := ({((0, 0), false), ((2, 2), true), ((4, 1), false)} : Clause VV)

def c6 : Clause VV := ({((3, 2), false), ((4, 1), false)} : Clause VV)

def c7 : Clause VV := ({((1, 0), false), ((4, 1), false)} : Clause VV)

def c8 : Clause VV := ({((1, 2), true), ((4, 1), false)} : Clause VV)

def c9 : Clause VV := ({((4, 1), false)} : Clause VV)

def c10 : Clause VV := ({((0, 0), false), ((2, 1), true), ((4, 2), false)} : Clause VV)

def c11 : Clause VV := ({((3, 1), false), ((4, 2), false)} : Clause VV)

def c12 : Clause VV := ({((1, 0), false), ((4, 2), false)} : Clause VV)

def c13 : Clause VV := ({((1, 1), true), ((4, 2), false)} : Clause VV)

def c14 : Clause VV := ({((4, 2), false)} : Clause VV)

def c15 : Clause VV := ({((0, 0), false), ((2, 1), true), ((4, 3), false)} : Clause VV)

def c16 : Clause VV := ({((3, 1), false), ((4, 3), false)} : Clause VV)

def c17 : Clause VV := ({((1, 0), false), ((4, 3), false)} : Clause VV)

def c18 : Clause VV := ({((1, 1), true), ((4, 3), false)} : Clause VV)

def c19 : Clause VV := (∅ : Clause VV)

def p0 : List (Clause VV) := [c0]

def p1 : List (Clause VV) := c1 :: p0

def p2 : List (Clause VV) := c2 :: p1

def p3 : List (Clause VV) := c3 :: p2

def p4 : List (Clause VV) := c4 :: p3

def p5 : List (Clause VV) := c5 :: p4

def p6 : List (Clause VV) := c6 :: p5

def p7 : List (Clause VV) := c7 :: p6

def p8 : List (Clause VV) := c8 :: p7

def p9 : List (Clause VV) := c9 :: p8

def p10 : List (Clause VV) := c10 :: p9

def p11 : List (Clause VV) := c11 :: p10

def p12 : List (Clause VV) := c12 :: p11

def p13 : List (Clause VV) := c13 :: p12

def p14 : List (Clause VV) := c14 :: p13

def p15 : List (Clause VV) := c15 :: p14

def p16 : List (Clause VV) := c16 :: p15

def p17 : List (Clause VV) := c17 :: p16

def p18 : List (Clause VV) := c18 :: p17

def p19 : List (Clause VV) := c19 :: p18

def G0 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ ([] : List (Clause VV))})

def A0 : Set (Literal VV) := negLit '' (↑c0 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r0 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ ([] : List (Clause VV))}) c0 := by
  show ∃ D ∈ G0, ∀ l ∈ D, UPForces G0 A0 (negLit l)
  have f_0_1_t : UPForces G0 A0 ((0, 1), true) := UPForces.hyp ⟨((0, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_2_2_f : UPForces G0 A0 ((2, 2), false) := UPForces.hyp ⟨((2, 2), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_0_t : UPForces G0 A0 ((4, 0), true) := UPForces.hyp ⟨((4, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_1_0_f : UPForces G0 A0 ((1, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_2_0_f : UPForces G0 A0 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_3_0_f : UPForces G0 A0 ((3, 0), false) := by
    refine UPForces.unit (D := ({((3, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_1_1_f : UPForces G0 A0 ((1, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((1, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((1, 1), false)} : Clause VV), l ≠ ((1, 1), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_1_t
    · exact absurd rfl hne
  have f_2_1_f : UPForces G0 A0 ((2, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((2, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((2, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_1_t
    · exact absurd rfl hne
  have f_2_3_t : UPForces G0 A0 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  have f_3_1_f : UPForces G0 A0 ((3, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_1_t
    · exact absurd rfl hne
  have f_1_3_f : UPForces G0 A0 ((1, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_2_3_t
  have f_1_2_t : UPForces G0 A0 ((1, 2), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 2), true) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact f_1_1_f
    · exact absurd rfl hne
    · exact f_1_3_f
  have f_3_2_f : UPForces G0 A0 ((3, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_2_t
    · exact absurd rfl hne
  have f_3_3_t : UPForces G0 A0 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G0 A0 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  refine ⟨({((2, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_2_3_t
  · exact f_3_3_t

def G1 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p0})

def A1 : Set (Literal VV) := negLit '' (↑c1 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r1 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p0}) c1 := by
  show ∃ D ∈ G1, ∀ l ∈ D, UPForces G1 A1 (negLit l)
  have f_4_0_t : UPForces G1 A1 ((4, 0), true) := UPForces.hyp ⟨((4, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_3_2_t : UPForces G1 A1 ((3, 2), true) := UPForces.hyp ⟨((3, 2), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_f : UPForces G1 A1 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_1_0_f : UPForces G1 A1 ((1, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_2_0_f : UPForces G1 A1 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_0_2_f : UPForces G1 A1 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_2_t
  have f_1_2_f : UPForces G1 A1 ((1, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((1, 2), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_2_t
  have f_2_2_f : UPForces G1 A1 ((2, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_2_t
  have f_0_1_f : UPForces G1 A1 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((2, 2), true), ((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((2, 2), true), ((4, 0), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_2_f
    · exact f_4_0_t
  have f_0_3_t : UPForces G1 A1 ((0, 3), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 3), true) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact f_0_2_f
    · exact absurd rfl hne
  have f_1_3_f : UPForces G1 A1 ((1, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((1, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((1, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_3_t
    · exact absurd rfl hne
  have f_1_1_t : UPForces G1 A1 ((1, 1), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 1), true) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact absurd rfl hne
    · exact f_1_2_f
    · exact f_1_3_f
  have f_2_1_f : UPForces G1 A1 ((2, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((2, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((2, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_1_t
    · exact absurd rfl hne
  have f_2_3_t : UPForces G1 A1 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G1 A1 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  refine ⟨({((0, 3), false), ((2, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_3_t
  · exact f_2_3_t

def G2 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p1})

def A2 : Set (Literal VV) := negLit '' (↑c2 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r2 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p1}) c2 := by
  show ∃ D ∈ G2, ∀ l ∈ D, UPForces G2 A2 (negLit l)
  have f_1_1_t : UPForces G2 A2 ((1, 1), true) := UPForces.hyp ⟨((1, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_0_t : UPForces G2 A2 ((4, 0), true) := UPForces.hyp ⟨((4, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_f : UPForces G2 A2 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_2_0_f : UPForces G2 A2 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_3_0_f : UPForces G2 A2 ((3, 0), false) := by
    refine UPForces.unit (D := ({((3, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_0_1_f : UPForces G2 A2 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((1, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((1, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_1_t
  have f_2_1_f : UPForces G2 A2 ((2, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((2, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((2, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_1_t
    · exact absurd rfl hne
  have f_3_1_f : UPForces G2 A2 ((3, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_1_t
    · exact absurd rfl hne
  have f_3_2_f : UPForces G2 A2 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 0), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_3_3_t : UPForces G2 A2 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  have f_0_3_f : UPForces G2 A2 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((3, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((3, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_3_t
  have f_0_2_t : UPForces G2 A2 ((0, 2), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 2), true) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact absurd rfl hne
    · exact f_0_3_f
  have f_2_2_f : UPForces G2 A2 ((2, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((2, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((2, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_2_t
    · exact absurd rfl hne
  have f_2_3_t : UPForces G2 A2 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G2 A2 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  refine ⟨({((2, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_2_3_t
  · exact f_3_3_t

def G3 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p2})

def A3 : Set (Literal VV) := negLit '' (↑c3 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r3 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p2}) c3 := by
  show ∃ D ∈ G3, ∀ l ∈ D, UPForces G3 A3 (negLit l)
  have f_1_2_f : UPForces G3 A3 ((1, 2), false) := UPForces.hyp ⟨((1, 2), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_0_t : UPForces G3 A3 ((4, 0), true) := UPForces.hyp ⟨((4, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_f : UPForces G3 A3 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_1_0_f : UPForces G3 A3 ((1, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_2_0_f : UPForces G3 A3 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_3_0_f : UPForces G3 A3 ((3, 0), false) := by
    refine UPForces.unit (D := ({((3, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_3_2_f : UPForces G3 A3 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.head _))) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 0), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_1_1_f : UPForces G3 A3 ((1, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((4, 0), false)} : Clause VV), l ≠ ((1, 1), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_1_3_t : UPForces G3 A3 ((1, 3), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 3), true) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact f_1_1_f
    · exact f_1_2_f
    · exact absurd rfl hne
  have f_0_3_f : UPForces G3 A3 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((1, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((1, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_3_t
  have f_2_3_f : UPForces G3 A3 ((2, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_3_t
    · exact absurd rfl hne
  have f_3_3_f : UPForces G3 A3 ((3, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((3, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((3, 3), false)} : Clause VV), l ≠ ((3, 3), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_3_t
    · exact absurd rfl hne
  have f_3_1_t : UPForces G3 A3 ((3, 1), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 1), true) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact absurd rfl hne
    · exact f_3_2_f
    · exact f_3_3_f
  have f_0_1_f : UPForces G3 A3 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_0_2_t : UPForces G3 A3 ((0, 2), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 2), true) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact absurd rfl hne
    · exact f_0_3_f
  have f_2_1_f : UPForces G3 A3 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_2_2_t : UPForces G3 A3 ((2, 2), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 2), true) → UPForces G3 A3 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact absurd rfl hne
    · exact f_2_3_f
  refine ⟨({((0, 2), false), ((2, 2), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_2_t
  · exact f_2_2_t

def G4 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p3})

def A4 : Set (Literal VV) := negLit '' (↑c4 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r4 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p3}) c4 := by
  show ∃ D ∈ G4, ∀ l ∈ D, UPForces G4 A4 (negLit l)
  have f_4_0_t : UPForces G4 A4 ((4, 0), true) := UPForces.hyp ⟨((4, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_f : UPForces G4 A4 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_2_0_f : UPForces G4 A4 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_3_0_f : UPForces G4 A4 ((3, 0), false) := by
    refine UPForces.unit (D := ({((3, 0), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), false), ((4, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_3_2_f : UPForces G4 A4 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 0), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_1_2_t : UPForces G4 A4 ((1, 2), true) := by
    refine UPForces.unit (D := ({((1, 2), true), ((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), true), ((4, 0), false)} : Clause VV), l ≠ ((1, 2), true) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_0_t
  have f_0_2_f : UPForces G4 A4 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((1, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((1, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_2_t
  have f_2_2_f : UPForces G4 A4 ((2, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((2, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((2, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_2_t
    · exact absurd rfl hne
  have f_0_1_f : UPForces G4 A4 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((2, 2), true), ((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((2, 2), true), ((4, 0), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_2_f
    · exact f_4_0_t
  have f_0_3_t : UPForces G4 A4 ((0, 3), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 3), true) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact f_0_2_f
    · exact absurd rfl hne
  have f_2_3_f : UPForces G4 A4 ((2, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_3_t
    · exact absurd rfl hne
  have f_2_1_t : UPForces G4 A4 ((2, 1), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 1), true) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact absurd rfl hne
    · exact f_2_2_f
    · exact f_2_3_f
  have f_3_1_f : UPForces G4 A4 ((3, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_2_1_t
    · exact absurd rfl hne
  have f_3_3_t : UPForces G4 A4 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G4 A4 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  refine ⟨({((0, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_3_t
  · exact f_3_3_t

def G5 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p4})

def A5 : Set (Literal VV) := negLit '' (↑c5 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r5 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p4}) c5 := by
  show ∃ D ∈ G5, ∀ l ∈ D, UPForces G5 A5 (negLit l)
  have f_4_1_t : UPForces G5 A5 ((4, 1), true) := UPForces.hyp ⟨((4, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_2_2_f : UPForces G5 A5 ((2, 2), false) := UPForces.hyp ⟨((2, 2), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_t : UPForces G5 A5 ((0, 0), true) := UPForces.hyp ⟨((0, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_1_0_f : UPForces G5 A5 ((1, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((1, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((1, 0), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_2_0_f : UPForces G5 A5 ((2, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_3_0_f : UPForces G5 A5 ((3, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_1_1_f : UPForces G5 A5 ((1, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((1, 1), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_2_1_f : UPForces G5 A5 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_2_3_t : UPForces G5 A5 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  have f_3_1_f : UPForces G5 A5 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_1_3_f : UPForces G5 A5 ((1, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_2_3_t
  have f_1_2_t : UPForces G5 A5 ((1, 2), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 2), true) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact f_1_1_f
    · exact absurd rfl hne
    · exact f_1_3_f
  have f_3_2_f : UPForces G5 A5 ((3, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_2_t
    · exact absurd rfl hne
  have f_3_3_t : UPForces G5 A5 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G5 A5 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  refine ⟨({((2, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_2_3_t
  · exact f_3_3_t

def G6 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p5})

def A6 : Set (Literal VV) := negLit '' (↑c6 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r6 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p5}) c6 := by
  show ∃ D ∈ G6, ∀ l ∈ D, UPForces G6 A6 (negLit l)
  have f_4_1_t : UPForces G6 A6 ((4, 1), true) := UPForces.hyp ⟨((4, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_3_2_t : UPForces G6 A6 ((3, 2), true) := UPForces.hyp ⟨((3, 2), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_1_f : UPForces G6 A6 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_1_1_f : UPForces G6 A6 ((1, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((1, 1), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_2_1_f : UPForces G6 A6 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_0_2_f : UPForces G6 A6 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_2_t
  have f_1_2_f : UPForces G6 A6 ((1, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((1, 2), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_2_t
  have f_2_2_f : UPForces G6 A6 ((2, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_2_t
  have f_0_0_f : UPForces G6 A6 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 2), true), ((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 2), true), ((4, 1), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_2_f
    · exact f_4_1_t
  have f_0_3_t : UPForces G6 A6 ((0, 3), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 3), true) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact f_0_2_f
    · exact absurd rfl hne
  have f_1_3_f : UPForces G6 A6 ((1, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((1, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((1, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_3_t
    · exact absurd rfl hne
  have f_1_0_t : UPForces G6 A6 ((1, 0), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 0), true) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_1_1_f
    · exact f_1_2_f
    · exact f_1_3_f
  have f_2_0_f : UPForces G6 A6 ((2, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_2_3_t : UPForces G6 A6 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G6 A6 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  refine ⟨({((0, 3), false), ((2, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_3_t
  · exact f_2_3_t

def G7 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p6})

def A7 : Set (Literal VV) := negLit '' (↑c7 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r7 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p6}) c7 := by
  show ∃ D ∈ G7, ∀ l ∈ D, UPForces G7 A7 (negLit l)
  have f_4_1_t : UPForces G7 A7 ((4, 1), true) := UPForces.hyp ⟨((4, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_1_0_t : UPForces G7 A7 ((1, 0), true) := UPForces.hyp ⟨((1, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_f : UPForces G7 A7 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((1, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((1, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_0_t
  have f_2_0_f : UPForces G7 A7 ((2, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_3_0_f : UPForces G7 A7 ((3, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_0_1_f : UPForces G7 A7 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_2_1_f : UPForces G7 A7 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_3_1_f : UPForces G7 A7 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_3_2_f : UPForces G7 A7 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 1), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_3_3_t : UPForces G7 A7 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  have f_0_3_f : UPForces G7 A7 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((3, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((3, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_3_t
  have f_0_2_t : UPForces G7 A7 ((0, 2), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 2), true) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact absurd rfl hne
    · exact f_0_3_f
  have f_2_2_f : UPForces G7 A7 ((2, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((2, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((2, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_2_t
    · exact absurd rfl hne
  have f_2_3_t : UPForces G7 A7 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G7 A7 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  refine ⟨({((2, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_2_3_t
  · exact f_3_3_t

def G8 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p7})

def A8 : Set (Literal VV) := negLit '' (↑c8 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r8 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p7}) c8 := by
  show ∃ D ∈ G8, ∀ l ∈ D, UPForces G8 A8 (negLit l)
  have f_1_2_f : UPForces G8 A8 ((1, 2), false) := UPForces.hyp ⟨((1, 2), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_1_t : UPForces G8 A8 ((4, 1), true) := UPForces.hyp ⟨((4, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_1_f : UPForces G8 A8 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_1_1_f : UPForces G8 A8 ((1, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((1, 1), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_2_1_f : UPForces G8 A8 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_3_1_f : UPForces G8 A8 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_3_2_f : UPForces G8 A8 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.head _))) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 1), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_1_0_f : UPForces G8 A8 ((1, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((4, 1), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_1_3_t : UPForces G8 A8 ((1, 3), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 3), true) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact f_1_1_f
    · exact f_1_2_f
    · exact absurd rfl hne
  have f_0_3_f : UPForces G8 A8 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((1, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((1, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_3_t
  have f_2_3_f : UPForces G8 A8 ((2, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_3_t
    · exact absurd rfl hne
  have f_3_3_f : UPForces G8 A8 ((3, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((3, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((3, 3), false)} : Clause VV), l ≠ ((3, 3), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_3_t
    · exact absurd rfl hne
  have f_3_0_t : UPForces G8 A8 ((3, 0), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 0), true) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_f
    · exact f_3_2_f
    · exact f_3_3_f
  have f_0_0_f : UPForces G8 A8 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_0_t
  have f_0_2_t : UPForces G8 A8 ((0, 2), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 2), true) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact absurd rfl hne
    · exact f_0_3_f
  have f_2_0_f : UPForces G8 A8 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_0_t
  have f_2_2_t : UPForces G8 A8 ((2, 2), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 2), true) → UPForces G8 A8 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact absurd rfl hne
    · exact f_2_3_f
  refine ⟨({((0, 2), false), ((2, 2), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_2_t
  · exact f_2_2_t

def G9 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p8})

def A9 : Set (Literal VV) := negLit '' (↑c9 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r9 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p8}) c9 := by
  show ∃ D ∈ G9, ∀ l ∈ D, UPForces G9 A9 (negLit l)
  have f_4_1_t : UPForces G9 A9 ((4, 1), true) := UPForces.hyp ⟨((4, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_1_f : UPForces G9 A9 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_2_1_f : UPForces G9 A9 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_3_1_f : UPForces G9 A9 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_3_2_f : UPForces G9 A9 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 1), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_1_2_t : UPForces G9 A9 ((1, 2), true) := by
    refine UPForces.unit (D := ({((1, 2), true), ((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), true), ((4, 1), false)} : Clause VV), l ≠ ((1, 2), true) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_1_t
  have f_0_2_f : UPForces G9 A9 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((1, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((1, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_2_t
  have f_2_2_f : UPForces G9 A9 ((2, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((2, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((2, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_2_t
    · exact absurd rfl hne
  have f_0_0_f : UPForces G9 A9 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 2), true), ((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 2), true), ((4, 1), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_2_f
    · exact f_4_1_t
  have f_0_3_t : UPForces G9 A9 ((0, 3), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 3), true) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact f_0_2_f
    · exact absurd rfl hne
  have f_2_3_f : UPForces G9 A9 ((2, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_3_t
    · exact absurd rfl hne
  have f_2_0_t : UPForces G9 A9 ((2, 0), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 0), true) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_1_f
    · exact f_2_2_f
    · exact f_2_3_f
  have f_3_0_f : UPForces G9 A9 ((3, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_2_0_t
    · exact absurd rfl hne
  have f_3_3_t : UPForces G9 A9 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G9 A9 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  refine ⟨({((0, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_3_t
  · exact f_3_3_t

def G10 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p9})

def A10 : Set (Literal VV) := negLit '' (↑c10 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r10 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p9}) c10 := by
  show ∃ D ∈ G10, ∀ l ∈ D, UPForces G10 A10 (negLit l)
  have f_4_2_t : UPForces G10 A10 ((4, 2), true) := UPForces.hyp ⟨((4, 2), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_2_1_f : UPForces G10 A10 ((2, 1), false) := UPForces.hyp ⟨((2, 1), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_t : UPForces G10 A10 ((0, 0), true) := UPForces.hyp ⟨((0, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_1_0_f : UPForces G10 A10 ((1, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((1, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((1, 0), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_2_0_f : UPForces G10 A10 ((2, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_3_0_f : UPForces G10 A10 ((3, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_1_2_f : UPForces G10 A10 ((1, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((1, 2), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_2_2_f : UPForces G10 A10 ((2, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_2_3_t : UPForces G10 A10 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  have f_3_2_f : UPForces G10 A10 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_1_3_f : UPForces G10 A10 ((1, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_2_3_t
  have f_1_1_t : UPForces G10 A10 ((1, 1), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 1), true) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact absurd rfl hne
    · exact f_1_2_f
    · exact f_1_3_f
  have f_3_1_f : UPForces G10 A10 ((3, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_1_t
    · exact absurd rfl hne
  have f_3_3_t : UPForces G10 A10 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G10 A10 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  refine ⟨({((2, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_2_3_t
  · exact f_3_3_t

def G11 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p10})

def A11 : Set (Literal VV) := negLit '' (↑c11 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r11 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p10}) c11 := by
  show ∃ D ∈ G11, ∀ l ∈ D, UPForces G11 A11 (negLit l)
  have f_4_2_t : UPForces G11 A11 ((4, 2), true) := UPForces.hyp ⟨((4, 2), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_3_1_t : UPForces G11 A11 ((3, 1), true) := UPForces.hyp ⟨((3, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_1_f : UPForces G11 A11 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_1_1_f : UPForces G11 A11 ((1, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((1, 1), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_2_1_f : UPForces G11 A11 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_0_2_f : UPForces G11 A11 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_1_2_f : UPForces G11 A11 ((1, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((1, 2), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_2_2_f : UPForces G11 A11 ((2, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_0_0_f : UPForces G11 A11 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 1), true), ((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 1), true), ((4, 2), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_1_f
    · exact f_4_2_t
  have f_0_3_t : UPForces G11 A11 ((0, 3), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 3), true) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact f_0_2_f
    · exact absurd rfl hne
  have f_1_3_f : UPForces G11 A11 ((1, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((1, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((1, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_3_t
    · exact absurd rfl hne
  have f_1_0_t : UPForces G11 A11 ((1, 0), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 0), true) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_1_1_f
    · exact f_1_2_f
    · exact f_1_3_f
  have f_2_0_f : UPForces G11 A11 ((2, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_2_3_t : UPForces G11 A11 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G11 A11 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  refine ⟨({((0, 3), false), ((2, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_3_t
  · exact f_2_3_t

def G12 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p11})

def A12 : Set (Literal VV) := negLit '' (↑c12 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r12 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p11}) c12 := by
  show ∃ D ∈ G12, ∀ l ∈ D, UPForces G12 A12 (negLit l)
  have f_4_2_t : UPForces G12 A12 ((4, 2), true) := UPForces.hyp ⟨((4, 2), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_1_0_t : UPForces G12 A12 ((1, 0), true) := UPForces.hyp ⟨((1, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_f : UPForces G12 A12 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((1, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((1, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_0_t
  have f_2_0_f : UPForces G12 A12 ((2, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_3_0_f : UPForces G12 A12 ((3, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_0_2_f : UPForces G12 A12 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_2_2_f : UPForces G12 A12 ((2, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_3_2_f : UPForces G12 A12 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_3_1_f : UPForces G12 A12 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 2), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_3_3_t : UPForces G12 A12 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  have f_0_3_f : UPForces G12 A12 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((3, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((3, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_3_t
  have f_0_1_t : UPForces G12 A12 ((0, 1), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 1), true) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact absurd rfl hne
    · exact f_0_2_f
    · exact f_0_3_f
  have f_2_1_f : UPForces G12 A12 ((2, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((2, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((2, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_1_t
    · exact absurd rfl hne
  have f_2_3_t : UPForces G12 A12 ((2, 3), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 3), true) → UPForces G12 A12 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact f_2_2_f
    · exact absurd rfl hne
  refine ⟨({((2, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_2_3_t
  · exact f_3_3_t

def G13 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p12})

def A13 : Set (Literal VV) := negLit '' (↑c13 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r13 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p12}) c13 := by
  show ∃ D ∈ G13, ∀ l ∈ D, UPForces G13 A13 (negLit l)
  have f_4_2_t : UPForces G13 A13 ((4, 2), true) := UPForces.hyp ⟨((4, 2), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_1_1_f : UPForces G13 A13 ((1, 1), false) := UPForces.hyp ⟨((1, 1), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_2_f : UPForces G13 A13 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_1_2_f : UPForces G13 A13 ((1, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((1, 2), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_2_2_f : UPForces G13 A13 ((2, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_3_2_f : UPForces G13 A13 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_3_1_f : UPForces G13 A13 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.head _))) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 2), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_1_0_f : UPForces G13 A13 ((1, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((4, 2), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_1_3_t : UPForces G13 A13 ((1, 3), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 3), true) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact f_1_1_f
    · exact f_1_2_f
    · exact absurd rfl hne
  have f_0_3_f : UPForces G13 A13 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((1, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((1, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_3_t
  have f_2_3_f : UPForces G13 A13 ((2, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_3_t
    · exact absurd rfl hne
  have f_3_3_f : UPForces G13 A13 ((3, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((3, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((3, 3), false)} : Clause VV), l ≠ ((3, 3), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_3_t
    · exact absurd rfl hne
  have f_3_0_t : UPForces G13 A13 ((3, 0), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 0), true) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_f
    · exact f_3_2_f
    · exact f_3_3_f
  have f_0_0_f : UPForces G13 A13 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_0_t
  have f_0_1_t : UPForces G13 A13 ((0, 1), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 1), true) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact absurd rfl hne
    · exact f_0_2_f
    · exact f_0_3_f
  have f_2_0_f : UPForces G13 A13 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_0_t
  have f_2_1_t : UPForces G13 A13 ((2, 1), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 1), true) → UPForces G13 A13 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact absurd rfl hne
    · exact f_2_2_f
    · exact f_2_3_f
  refine ⟨({((0, 1), false), ((2, 1), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_1_t
  · exact f_2_1_t

def G14 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p13})

def A14 : Set (Literal VV) := negLit '' (↑c14 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r14 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p13}) c14 := by
  show ∃ D ∈ G14, ∀ l ∈ D, UPForces G14 A14 (negLit l)
  have f_4_2_t : UPForces G14 A14 ((4, 2), true) := UPForces.hyp ⟨((4, 2), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_2_f : UPForces G14 A14 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_2_2_f : UPForces G14 A14 ((2, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_3_2_f : UPForces G14 A14 ((3, 2), false) := by
    refine UPForces.unit (D := ({((3, 2), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 2), false), ((4, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_3_1_f : UPForces G14 A14 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 2), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_1_1_t : UPForces G14 A14 ((1, 1), true) := by
    refine UPForces.unit (D := ({((1, 1), true), ((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), true), ((4, 2), false)} : Clause VV), l ≠ ((1, 1), true) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_2_t
  have f_0_1_f : UPForces G14 A14 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((1, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((1, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_1_t
  have f_2_1_f : UPForces G14 A14 ((2, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((2, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((2, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_1_t
    · exact absurd rfl hne
  have f_0_0_f : UPForces G14 A14 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 1), true), ((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 1), true), ((4, 2), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_1_f
    · exact f_4_2_t
  have f_0_3_t : UPForces G14 A14 ((0, 3), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 3), true) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact f_0_2_f
    · exact absurd rfl hne
  have f_2_3_f : UPForces G14 A14 ((2, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((2, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((2, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_3_t
    · exact absurd rfl hne
  have f_2_0_t : UPForces G14 A14 ((2, 0), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 0), true) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_1_f
    · exact f_2_2_f
    · exact f_2_3_f
  have f_3_0_f : UPForces G14 A14 ((3, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_2_0_t
    · exact absurd rfl hne
  have f_3_3_t : UPForces G14 A14 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G14 A14 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  refine ⟨({((0, 3), false), ((3, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_3_t
  · exact f_3_3_t

def G15 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p14})

def A15 : Set (Literal VV) := negLit '' (↑c15 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r15 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p14}) c15 := by
  show ∃ D ∈ G15, ∀ l ∈ D, UPForces G15 A15 (negLit l)
  have f_2_1_f : UPForces G15 A15 ((2, 1), false) := UPForces.hyp ⟨((2, 1), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_t : UPForces G15 A15 ((0, 0), true) := UPForces.hyp ⟨((0, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_3_t : UPForces G15 A15 ((4, 3), true) := UPForces.hyp ⟨((4, 3), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_1_0_f : UPForces G15 A15 ((1, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((1, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((1, 0), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_2_0_f : UPForces G15 A15 ((2, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_3_0_f : UPForces G15 A15 ((3, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_0_t
    · exact absurd rfl hne
  have f_1_3_f : UPForces G15 A15 ((1, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_2_3_f : UPForces G15 A15 ((2, 3), false) := by
    refine UPForces.unit (D := ({((2, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_2_2_t : UPForces G15 A15 ((2, 2), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 2), true) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact absurd rfl hne
    · exact f_2_3_f
  have f_1_2_f : UPForces G15 A15 ((1, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((2, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((2, 2), false)} : Clause VV), l ≠ ((1, 2), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_2_2_t
  have f_1_1_t : UPForces G15 A15 ((1, 1), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 1), true) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact absurd rfl hne
    · exact f_1_2_f
    · exact f_1_3_f
  have f_3_1_f : UPForces G15 A15 ((3, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_1_t
    · exact absurd rfl hne
  have f_3_2_f : UPForces G15 A15 ((3, 2), false) := by
    refine UPForces.unit (D := ({((2, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_2_2_t
    · exact absurd rfl hne
  have f_3_3_t : UPForces G15 A15 ((3, 3), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 3), true) → UPForces G15 A15 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact f_3_2_f
    · exact absurd rfl hne
  refine ⟨({((3, 3), false), ((4, 3), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 3, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_3_3_t
  · exact f_4_3_t

def G16 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p15})

def A16 : Set (Literal VV) := negLit '' (↑c16 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r16 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p15}) c16 := by
  show ∃ D ∈ G16, ∀ l ∈ D, UPForces G16 A16 (negLit l)
  have f_3_1_t : UPForces G16 A16 ((3, 1), true) := UPForces.hyp ⟨((3, 1), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_3_t : UPForces G16 A16 ((4, 3), true) := UPForces.hyp ⟨((4, 3), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_1_f : UPForces G16 A16 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_1_1_f : UPForces G16 A16 ((1, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((1, 1), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_2_1_f : UPForces G16 A16 ((2, 1), false) := by
    refine UPForces.unit (D := ({((2, 1), false), ((3, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 1), false), ((3, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_t
  have f_0_3_f : UPForces G16 A16 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_1_3_f : UPForces G16 A16 ((1, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_2_3_f : UPForces G16 A16 ((2, 3), false) := by
    refine UPForces.unit (D := ({((2, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_0_0_f : UPForces G16 A16 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 1), true), ((4, 3), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 1), true), ((4, 3), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_1_f
    · exact f_4_3_t
  have f_0_2_t : UPForces G16 A16 ((0, 2), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 2), true) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact absurd rfl hne
    · exact f_0_3_f
  have f_1_2_f : UPForces G16 A16 ((1, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((1, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((1, 2), false)} : Clause VV), l ≠ ((1, 2), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_2_t
    · exact absurd rfl hne
  have f_1_0_t : UPForces G16 A16 ((1, 0), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 0), true) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_1_1_f
    · exact f_1_2_f
    · exact f_1_3_f
  have f_2_0_f : UPForces G16 A16 ((2, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_2_2_t : UPForces G16 A16 ((2, 2), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 2), true) → UPForces G16 A16 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact absurd rfl hne
    · exact f_2_3_f
  refine ⟨({((0, 2), false), ((2, 2), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_2_t
  · exact f_2_2_t

def G17 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p16})

def A17 : Set (Literal VV) := negLit '' (↑c17 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r17 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p16}) c17 := by
  show ∃ D ∈ G17, ∀ l ∈ D, UPForces G17 A17 (negLit l)
  have f_1_0_t : UPForces G17 A17 ((1, 0), true) := UPForces.hyp ⟨((1, 0), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_3_t : UPForces G17 A17 ((4, 3), true) := UPForces.hyp ⟨((4, 3), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_0_f : UPForces G17 A17 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((1, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((1, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_0_t
  have f_2_0_f : UPForces G17 A17 ((2, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((2, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((2, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_3_0_f : UPForces G17 A17 ((3, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_0_t
    · exact absurd rfl hne
  have f_0_3_f : UPForces G17 A17 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_2_3_f : UPForces G17 A17 ((2, 3), false) := by
    refine UPForces.unit (D := ({((2, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_3_3_f : UPForces G17 A17 ((3, 3), false) := by
    refine UPForces.unit (D := ({((3, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((3, 3), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_3_1_f : UPForces G17 A17 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 3), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_3_2_t : UPForces G17 A17 ((3, 2), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 2), true) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact absurd rfl hne
    · exact f_3_3_f
  have f_0_2_f : UPForces G17 A17 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_2_t
  have f_0_1_t : UPForces G17 A17 ((0, 1), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 1), true) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact absurd rfl hne
    · exact f_0_2_f
    · exact f_0_3_f
  have f_2_1_f : UPForces G17 A17 ((2, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((2, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((2, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_1_t
    · exact absurd rfl hne
  have f_2_2_t : UPForces G17 A17 ((2, 2), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 2), true) → UPForces G17 A17 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact f_2_1_f
    · exact absurd rfl hne
    · exact f_2_3_f
  refine ⟨({((2, 2), false), ((3, 2), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_2_2_t
  · exact f_3_2_t

def G18 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p17})

def A18 : Set (Literal VV) := negLit '' (↑c18 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r18 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p17}) c18 := by
  show ∃ D ∈ G18, ∀ l ∈ D, UPForces G18 A18 (negLit l)
  have f_1_1_f : UPForces G18 A18 ((1, 1), false) := UPForces.hyp ⟨((1, 1), true), Finset.mem_coe.2 (by decide), rfl⟩
  have f_4_3_t : UPForces G18 A18 ((4, 3), true) := UPForces.hyp ⟨((4, 3), false), Finset.mem_coe.2 (by decide), rfl⟩
  have f_0_3_f : UPForces G18 A18 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_1_3_f : UPForces G18 A18 ((1, 3), false) := by
    refine UPForces.unit (D := ({((1, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((1, 3), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_2_3_f : UPForces G18 A18 ((2, 3), false) := by
    refine UPForces.unit (D := ({((2, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_3_3_f : UPForces G18 A18 ((3, 3), false) := by
    refine UPForces.unit (D := ({((3, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((3, 3), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_3_1_f : UPForces G18 A18 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.head _))) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 3), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_1_0_f : UPForces G18 A18 ((1, 0), false) := by
    refine UPForces.unit (D := ({((1, 0), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), false), ((4, 3), false)} : Clause VV), l ≠ ((1, 0), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_1_2_t : UPForces G18 A18 ((1, 2), true) := by
    refine UPForces.unit (D := ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨1, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 0), true), ((1, 1), true), ((1, 2), true), ((1, 3), true)} : Clause VV), l ≠ ((1, 2), true) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_1_0_f
    · exact f_1_1_f
    · exact absurd rfl hne
    · exact f_1_3_f
  have f_0_2_f : UPForces G18 A18 ((0, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((1, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((1, 2), false)} : Clause VV), l ≠ ((0, 2), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_2_t
  have f_2_2_f : UPForces G18 A18 ((2, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((2, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((2, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_2_t
    · exact absurd rfl hne
  have f_3_2_f : UPForces G18 A18 ((3, 2), false) := by
    refine UPForces.unit (D := ({((1, 2), false), ((3, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 2), false), ((3, 2), false)} : Clause VV), l ≠ ((3, 2), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_2_t
    · exact absurd rfl hne
  have f_3_0_t : UPForces G18 A18 ((3, 0), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 0), true) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_3_1_f
    · exact f_3_2_f
    · exact f_3_3_f
  have f_0_0_f : UPForces G18 A18 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_0_t
  have f_0_1_t : UPForces G18 A18 ((0, 1), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 1), true) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact absurd rfl hne
    · exact f_0_2_f
    · exact f_0_3_f
  have f_2_0_f : UPForces G18 A18 ((2, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((2, 0), false) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_3_0_t
  have f_2_1_t : UPForces G18 A18 ((2, 1), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 1), true) → UPForces G18 A18 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_2_0_f
    · exact absurd rfl hne
    · exact f_2_2_f
    · exact f_2_3_f
  refine ⟨({((0, 1), false), ((2, 1), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_1_t
  · exact f_2_1_t

def G19 : Set (Clause VV) := (PHP (4 + 1) 4 ∪ {D | D ∈ p18})

def A19 : Set (Literal VV) := negLit '' (↑c19 : Set (Literal VV))

set_option maxRecDepth 10000 in
theorem r19 : IsRUP (PHP (4 + 1) 4 ∪ {D | D ∈ p18}) c19 := by
  show ∃ D ∈ G19, ∀ l ∈ D, UPForces G19 A19 (negLit l)
  have f_4_0_f : UPForces G19 A19 ((4, 0), false) := by
    refine UPForces.unit (D := ({((4, 0), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) (by decide) ?_
    show ∀ l ∈ ({((4, 0), false)} : Clause VV), l ≠ ((4, 0), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl
    · exact absurd rfl hne
  have f_4_1_f : UPForces G19 A19 ((4, 1), false) := by
    refine UPForces.unit (D := ({((4, 1), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) (by decide) ?_
    show ∀ l ∈ ({((4, 1), false)} : Clause VV), l ≠ ((4, 1), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl
    · exact absurd rfl hne
  have f_4_2_f : UPForces G19 A19 ((4, 2), false) := by
    refine UPForces.unit (D := ({((4, 2), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) (by decide) ?_
    show ∀ l ∈ ({((4, 2), false)} : Clause VV), l ≠ ((4, 2), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl
    · exact absurd rfl hne
  have f_4_3_t : UPForces G19 A19 ((4, 3), true) := by
    refine UPForces.unit (D := ({((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨4, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((4, 0), true), ((4, 1), true), ((4, 2), true), ((4, 3), true)} : Clause VV), l ≠ ((4, 3), true) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_4_0_f
    · exact f_4_1_f
    · exact f_4_2_f
    · exact absurd rfl hne
  have f_0_3_f : UPForces G19 A19 ((0, 3), false) := by
    refine UPForces.unit (D := ({((0, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((0, 3), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_2_3_f : UPForces G19 A19 ((2, 3), false) := by
    refine UPForces.unit (D := ({((2, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((2, 3), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_3_3_f : UPForces G19 A19 ((3, 3), false) := by
    refine UPForces.unit (D := ({((3, 3), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨3, 4, 3, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 3), false), ((4, 3), false)} : Clause VV), l ≠ ((3, 3), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_3_1_f : UPForces G19 A19 ((3, 1), false) := by
    refine UPForces.unit (D := ({((3, 1), false), ((4, 3), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (by decide) ?_
    show ∀ l ∈ ({((3, 1), false), ((4, 3), false)} : Clause VV), l ≠ ((3, 1), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_1_1_t : UPForces G19 A19 ((1, 1), true) := by
    refine UPForces.unit (D := ({((1, 1), true), ((4, 3), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.head _)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), true), ((4, 3), false)} : Clause VV), l ≠ ((1, 1), true) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_4_3_t
  have f_0_1_f : UPForces G19 A19 ((0, 1), false) := by
    refine UPForces.unit (D := ({((0, 1), false), ((1, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 1), false), ((1, 1), false)} : Clause VV), l ≠ ((0, 1), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hne
    · exact f_1_1_t
  have f_2_1_f : UPForces G19 A19 ((2, 1), false) := by
    refine UPForces.unit (D := ({((1, 1), false), ((2, 1), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((1, 1), false), ((2, 1), false)} : Clause VV), l ≠ ((2, 1), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_1_1_t
    · exact absurd rfl hne
  have f_0_0_f : UPForces G19 A19 ((0, 0), false) := by
    refine UPForces.unit (D := ({((0, 0), false), ((2, 1), true), ((4, 3), false)} : Clause VV)) (Set.mem_union_right _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (by decide) ?_
    show ∀ l ∈ ({((0, 0), false), ((2, 1), true), ((4, 3), false)} : Clause VV), l ≠ ((0, 0), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_1_f
    · exact f_4_3_t
  have f_0_2_t : UPForces G19 A19 ((0, 2), true) := by
    refine UPForces.unit (D := ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨0, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 0), true), ((0, 1), true), ((0, 2), true), ((0, 3), true)} : Clause VV), l ≠ ((0, 2), true) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_0_0_f
    · exact f_0_1_f
    · exact absurd rfl hne
    · exact f_0_3_f
  have f_2_2_f : UPForces G19 A19 ((2, 2), false) := by
    refine UPForces.unit (D := ({((0, 2), false), ((2, 2), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((0, 2), false), ((2, 2), false)} : Clause VV), l ≠ ((2, 2), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_0_2_t
    · exact absurd rfl hne
  have f_2_0_t : UPForces G19 A19 ((2, 0), true) := by
    refine UPForces.unit (D := ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨2, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), true), ((2, 1), true), ((2, 2), true), ((2, 3), true)} : Clause VV), l ≠ ((2, 0), true) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact f_2_1_f
    · exact f_2_2_f
    · exact f_2_3_f
  have f_3_0_f : UPForces G19 A19 ((3, 0), false) := by
    refine UPForces.unit (D := ({((2, 0), false), ((3, 0), false)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((2, 0), false), ((3, 0), false)} : Clause VV), l ≠ ((3, 0), false) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact f_2_0_t
    · exact absurd rfl hne
  have f_3_2_t : UPForces G19 A19 ((3, 2), true) := by
    refine UPForces.unit (D := ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV)) (Set.mem_union_left _ (Set.mem_union_left _ ⟨3, by decide⟩)) (by decide) ?_
    show ∀ l ∈ ({((3, 0), true), ((3, 1), true), ((3, 2), true), ((3, 3), true)} : Clause VV), l ≠ ((3, 2), true) → UPForces G19 A19 (negLit l)
    intro l hl hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact f_3_0_f
    · exact f_3_1_f
    · exact absurd rfl hne
    · exact f_3_3_f
  refine ⟨({((0, 2), false), ((3, 2), false)} : Clause VV), Set.mem_union_left _ (Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact f_0_2_t
  · exact f_3_2_t

theorem d0 : IsRUPRun (PHP (4 + 1) 4) p0 := IsRUPRun.learn IsRUPRun.nil r0

theorem d1 : IsRUPRun (PHP (4 + 1) 4) p1 := IsRUPRun.learn d0 r1

theorem d2 : IsRUPRun (PHP (4 + 1) 4) p2 := IsRUPRun.learn d1 r2

theorem d3 : IsRUPRun (PHP (4 + 1) 4) p3 := IsRUPRun.learn d2 r3

theorem d4 : IsRUPRun (PHP (4 + 1) 4) p4 := IsRUPRun.learn d3 r4

theorem d5 : IsRUPRun (PHP (4 + 1) 4) p5 := IsRUPRun.learn d4 r5

theorem d6 : IsRUPRun (PHP (4 + 1) 4) p6 := IsRUPRun.learn d5 r6

theorem d7 : IsRUPRun (PHP (4 + 1) 4) p7 := IsRUPRun.learn d6 r7

theorem d8 : IsRUPRun (PHP (4 + 1) 4) p8 := IsRUPRun.learn d7 r8

theorem d9 : IsRUPRun (PHP (4 + 1) 4) p9 := IsRUPRun.learn d8 r9

theorem d10 : IsRUPRun (PHP (4 + 1) 4) p10 := IsRUPRun.learn d9 r10

theorem d11 : IsRUPRun (PHP (4 + 1) 4) p11 := IsRUPRun.learn d10 r11

theorem d12 : IsRUPRun (PHP (4 + 1) 4) p12 := IsRUPRun.learn d11 r12

theorem d13 : IsRUPRun (PHP (4 + 1) 4) p13 := IsRUPRun.learn d12 r13

theorem d14 : IsRUPRun (PHP (4 + 1) 4) p14 := IsRUPRun.learn d13 r14

theorem d15 : IsRUPRun (PHP (4 + 1) 4) p15 := IsRUPRun.learn d14 r15

theorem d16 : IsRUPRun (PHP (4 + 1) 4) p16 := IsRUPRun.learn d15 r16

theorem d17 : IsRUPRun (PHP (4 + 1) 4) p17 := IsRUPRun.learn d16 r17

theorem d18 : IsRUPRun (PHP (4 + 1) 4) p18 := IsRUPRun.learn d17 r18

theorem d19 : IsRUPRun (PHP (4 + 1) 4) p19 := IsRUPRun.learn d18 r19

theorem main_aux : ∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (4 + 1) 4) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)) ∈ ρ ∧ ρ.length ≤ 24 :=
  ⟨p19, d19, List.Mem.head _, by decide⟩

end PEqualNP.Outside.L_meta_9250

theorem PEqualNP.Outside.L_meta_9250 : ∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (4 + 1) 4) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)) ∈ ρ ∧ ρ.length ≤ 24 :=
  PEqualNP.Outside.L_meta_9250.main_aux
