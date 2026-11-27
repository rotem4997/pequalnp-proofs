import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9561

open PEqualNP.ProofComplexity

abbrev asg (b0 b1 b2 b3 : Bool) : Fin 4 → Bool :=
  fun i => if i = 0 then b0 else if i = 1 then b1 else if i = 2 then b2 else b3

def csat (a : Fin 4 → Bool) (C : PEqualNP.ProofComplexity.Clause (Fin 4)) : Bool := decide (∃ l ∈ C, a l.1 = l.2)

def fsat (a : Fin 4 → Bool) (S : Finset (PEqualNP.ProofComplexity.Clause (Fin 4))) : Bool := decide (∀ C ∈ S, csat a C = true)

def satb (S : Finset (PEqualNP.ProofComplexity.Clause (Fin 4))) : Bool :=
  [false, true].any (fun b0 => [false, true].any (fun b1 => [false, true].any (fun b2 => [false, true].any (fun b3 => fsat (asg b0 b1 b2 b3) S))))

def mub (S : Finset (PEqualNP.ProofComplexity.Clause (Fin 4))) : Bool :=
  (!satb S) && decide (∀ C ∈ S, satb (S.erase C) = true)

theorem bany (f : Bool → Bool) : [false, true].any f = true ↔ ∃ b, f b = true := by
  simp [Bool.exists_bool]

theorem fsat_iff (a : Fin 4 → Bool) (S : Finset (PEqualNP.ProofComplexity.Clause (Fin 4))) :
    fsat a S = true ↔ ∀ C ∈ S, ∃ l ∈ C, a l.1 = l.2 := by
  simp [fsat, csat]

theorem asg_eq (a : Fin 4 → Bool) : asg (a 0) (a 1) (a 2) (a 3) = a := by
  funext i
  fin_cases i <;> rfl

theorem sat_iff (S : Finset (PEqualNP.ProofComplexity.Clause (Fin 4))) : Satisfiable (↑S : Set (PEqualNP.ProofComplexity.Clause (Fin 4))) ↔ satb S = true := by
  simp only [satb, bany, fsat_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a 0, a 1, a 2, a 3, fun C hC => ?_⟩
    obtain ⟨l, hl, e⟩ := ha C (Finset.mem_coe.mpr hC)
    exact ⟨l, hl, by rw [asg_eq]; exact e⟩
  · rintro ⟨b0, b1, b2, b3, h⟩
    exact ⟨asg b0 b1 b2 b3, fun C hC => h C (Finset.mem_coe.mp hC)⟩

theorem mu_iff (S : Finset (PEqualNP.ProofComplexity.Clause (Fin 4))) :
    (¬ Satisfiable (↑S : Set (PEqualNP.ProofComplexity.Clause (Fin 4))) ∧ ∀ C ∈ (↑S : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), Satisfiable ((↑S : Set (PEqualNP.ProofComplexity.Clause (Fin 4))) \ {C})) ↔ mub S = true := by
  have h1 : (¬ Satisfiable (↑S : Set (PEqualNP.ProofComplexity.Clause (Fin 4)))) ↔ satb S = false := by
    rw [sat_iff]
    simp
  have h2 : (∀ C ∈ (↑S : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), Satisfiable ((↑S : Set (PEqualNP.ProofComplexity.Clause (Fin 4))) \ {C})) ↔ ∀ C ∈ S, satb (S.erase C) = true := by
    constructor
    · intro h C hC
      rw [← sat_iff, Finset.coe_erase]
      exact h C (Finset.mem_coe.mpr hC)
    · intro h C hC
      rw [← Finset.coe_erase, sat_iff]
      exact h C (Finset.mem_coe.mp hC)
  rw [h1, h2]
  simp [mub]

def F0 : Finset (PEqualNP.ProofComplexity.Clause (Fin 4)) :=
  {({((0 : Fin 4), false), ((1 : Fin 4), false), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), true), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), true), ((2 : Fin 4), true), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((2 : Fin 4), true), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4))}

theorem restr_eq (x : Fin 4) (b : Bool) :
    (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.filter (fun l => l.1 ≠ x)) '' {C | C ∈ (↑F0 : Set (PEqualNP.ProofComplexity.Clause (Fin 4))) ∧ (x, b) ∉ C} = ↑((F0.filter (fun C => (x, b) ∉ C)).image (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.filter (fun l => l.1 ≠ x))) := by
  ext D
  simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Finset.mem_coe]

theorem merge_eq (x y : Fin 4) (p : Bool) :
    {D | (∃ C ∈ (↑F0 : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), D = C.image (fun m => if m.1 = x then (y, if p then m.2 else !m.2) else m)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} = ↑((F0.image (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.image (fun m => if m.1 = x then (y, if p then m.2 else !m.2) else m))).filter (fun D => ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D)) := by
  ext D
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, h⟩
    exact ⟨⟨C, hC, rfl⟩, h⟩
  · rintro ⟨⟨C, hC, rfl⟩, h⟩
    exact ⟨⟨C, hC, rfl⟩, h⟩

theorem elim_eq (x : Fin 4) :
    {D | ((D ∈ (↑F0 : Set (PEqualNP.ProofComplexity.Clause (Fin 4))) ∧ (x, true) ∉ D ∧ (x, false) ∉ D) ∨ ∃ C ∈ (↑F0 : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), ∃ E ∈ (↑F0 : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), (x, true) ∈ C ∧ (x, false) ∈ E ∧ D = C.erase (x, true) ∪ E.erase (x, false)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} = ↑(((F0.filter (fun D => (x, true) ∉ D ∧ (x, false) ∉ D)) ∪ ((F0.filter (fun C => (x, true) ∈ C)) ×ˢ (F0.filter (fun E => (x, false) ∈ E))).image (fun q : PEqualNP.ProofComplexity.Clause (Fin 4) × PEqualNP.ProofComplexity.Clause (Fin 4) => q.1.erase (x, true) ∪ q.2.erase (x, false))).filter (fun D => ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D)) := by
  ext D
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨h1 | ⟨C, hC, E, hE, h1, h2, rfl⟩, h⟩
    · exact ⟨Or.inl h1, h⟩
    · exact ⟨Or.inr ⟨C, E, ⟨⟨hC, h1⟩, hE, h2⟩, rfl⟩, h⟩
  · rintro ⟨h1 | ⟨C, E, ⟨⟨hC, h1⟩, hE, h2⟩, rfl⟩, h⟩
    · exact ⟨Or.inl h1, h⟩
    · exact ⟨Or.inr ⟨C, hC, E, hE, h1, h2, rfl⟩, h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part1 : mub F0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part2 (x : Fin 4) (b : Bool) : mub ((F0.filter (fun C => (x, b) ∉ C)).image (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.filter (fun l => l.1 ≠ x))) = false := by
  fin_cases x <;> cases b <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part3 (x y : Fin 4) (p : Bool) (hxy : x ≠ y) : mub ((F0.image (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.image (fun m => if m.1 = x then (y, if p then m.2 else !m.2) else m))).filter (fun D => ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D)) = false := by
  fin_cases x <;> fin_cases y <;> cases p <;> first | (exfalso; exact hxy rfl) | decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part4 (x : Fin 4) : mub (((F0.filter (fun D => (x, true) ∉ D ∧ (x, false) ∉ D)) ∪ ((F0.filter (fun C => (x, true) ∈ C)) ×ˢ (F0.filter (fun E => (x, false) ∈ E))).image (fun q : PEqualNP.ProofComplexity.Clause (Fin 4) × PEqualNP.ProofComplexity.Clause (Fin 4) => q.1.erase (x, true) ∪ q.2.erase (x, false))).filter (fun D => ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D)) = false := by
  fin_cases x <;> decide +kernel

theorem main_aux : ∀ F : Set (PEqualNP.ProofComplexity.Clause (Fin 4)), F = {({((0 : Fin 4), false), ((1 : Fin 4), false), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), true), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), true), ((2 : Fin 4), true), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((2 : Fin 4), true), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4))} → (¬ PEqualNP.ProofComplexity.Satisfiable F ∧ ∀ C ∈ F, PEqualNP.ProofComplexity.Satisfiable (F \ {C})) ∧ (∀ (x : Fin 4) (b : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), G = (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.filter (fun l => l.1 ≠ x)) '' {C | C ∈ F ∧ (x, b) ∉ C} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) ∧ (∀ (x y : Fin 4) (p : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), x ≠ y → G = {D | (∃ C ∈ F, D = C.image (fun m => if m.1 = x then (y, if p then m.2 else !m.2) else m)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) ∧ (∀ (x : Fin 4) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), G = {D | ((D ∈ F ∧ (x, true) ∉ D ∧ (x, false) ∉ D) ∨ ∃ C ∈ F, ∃ E ∈ F, (x, true) ∈ C ∧ (x, false) ∈ E ∧ D = C.erase (x, true) ∪ E.erase (x, false)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) := by
  intro F hF
  have hF0 : F = ↑F0 := by
    rw [hF]
    simp only [F0, Finset.coe_insert, Finset.coe_singleton]
  subst hF0
  clear hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mu_iff]
    exact part1
  · intro x b G hG
    rw [hG, restr_eq, mu_iff]
    rw [part2 x b]
    decide
  · intro x y p G hxy hG
    rw [hG, merge_eq, mu_iff]
    rw [part3 x y p hxy]
    decide
  · intro x G hG
    rw [hG, elim_eq, mu_iff]
    rw [part4 x]
    decide

end PEqualNP.Outside.L_meta_9561

theorem PEqualNP.Outside.L_meta_9561 : ∀ F : Set (PEqualNP.ProofComplexity.Clause (Fin 4)), F = {({((0 : Fin 4), false), ((1 : Fin 4), false), ((2 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((1 : Fin 4), true), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), false), ((2 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((1 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((0 : Fin 4), true), ((2 : Fin 4), false), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), false), ((2 : Fin 4), false), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((1 : Fin 4), true), ((2 : Fin 4), true), ((3 : Fin 4), false)} : PEqualNP.ProofComplexity.Clause (Fin 4)), ({((2 : Fin 4), true), ((3 : Fin 4), true)} : PEqualNP.ProofComplexity.Clause (Fin 4))} → (¬ PEqualNP.ProofComplexity.Satisfiable F ∧ ∀ C ∈ F, PEqualNP.ProofComplexity.Satisfiable (F \ {C})) ∧ (∀ (x : Fin 4) (b : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), G = (fun C : PEqualNP.ProofComplexity.Clause (Fin 4) => C.filter (fun l => l.1 ≠ x)) '' {C | C ∈ F ∧ (x, b) ∉ C} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) ∧ (∀ (x y : Fin 4) (p : Bool) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), x ≠ y → G = {D | (∃ C ∈ F, D = C.image (fun m => if m.1 = x then (y, if p then m.2 else !m.2) else m)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) ∧ (∀ (x : Fin 4) (G : Set (PEqualNP.ProofComplexity.Clause (Fin 4))), G = {D | ((D ∈ F ∧ (x, true) ∉ D ∧ (x, false) ∉ D) ∨ ∃ C ∈ F, ∃ E ∈ F, (x, true) ∈ C ∧ (x, false) ∈ E ∧ D = C.erase (x, true) ∪ E.erase (x, false)) ∧ ¬ ∃ v, (v, true) ∈ D ∧ (v, false) ∈ D} → ¬ (¬ PEqualNP.ProofComplexity.Satisfiable G ∧ ∀ C ∈ G, PEqualNP.ProofComplexity.Satisfiable (G \ {C}))) :=
  PEqualNP.Outside.L_meta_9561.main_aux
