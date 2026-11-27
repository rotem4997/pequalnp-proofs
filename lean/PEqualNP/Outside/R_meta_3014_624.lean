import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 18000 in
theorem PEqualNP.Outside.R_meta_3014_624
    (core : ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 13 D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.output < 13 + D.size ∧ D.size ≤ 14 ∧
      ∀ x : Fin 14 → Bool, (((x 0 && ((x 8 || x 10) || x 7)) || (x 1 && ((x 9 || x 13) || x 7))) || (x 3 && ((x 11 || x 12) || x 7))) = false →
        (D.eval ([x 2, x 4, x 5, x 6, x 8, x 9, x 10, x 11, x 12, x 13, x 8 || x 10, x 9 || x 13, x 11 || x 12]) = true ↔
          ∃ u v : Fin 14, (u.val,v.val) ∈ ([(2,8), (2,12), (2,13), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))
    (extend : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 13 D →
      (∀ g ∈ D.gates, g.inputs.Nodup) → D.output < 13 + D.size →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      2 ≤ C.size ∧ C.size ≤ D.size+12 ∧
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = ((((x 0 && ((x 8 || x 10) || x 7)) || (x 1 && ((x 9 || x 13) || x 7))) || (x 3 && ((x 11 || x 12) || x 7))) || D.eval ([x 2, x 4, x 5, x 6, x 8, x 9, x 10, x 11, x 12, x 13, x 8 || x 10, x 9 || x 13, x 11 || x 12])))
    : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6 = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  obtain ⟨D, dShape, dDistinct, dOut, dSize, dEval⟩ := core
  obtain ⟨C, cShape, cDistinct, cMin, cSize, cEval⟩ := extend D dShape dDistinct dOut
  let pencil (x : Fin 14 → Bool) : Bool := (((x 0 && ((x 8 || x 10) || x 7)) || (x 1 && ((x 9 || x 13) || x 7))) || (x 3 && ((x 11 || x 12) || x 7)))
  let lifted (x : Fin 14 → Bool) : List Bool := ([x 2, x 4, x 5, x 6, x 8, x 9, x 10, x 11, x 12, x 13, x 8 || x 10, x 9 || x 13, x 11 || x 12])
  let P : List (ℕ × ℕ) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (3,7), (3,11), (3,12)]
  let R : List (ℕ × ℕ) := [(2,8), (2,12), (2,13), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
  let E : List (ℕ × ℕ) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
  let hit (S : List (ℕ × ℕ)) (x : Fin 14 → Bool) : Prop :=
    ∃ u v : Fin 14, (u.val,v.val) ∈ S ∧ x u = true ∧ x v = true
  have partition : ∀ u v : Fin 14, (u.val,v.val) ∈ E ↔ ((u.val,v.val) ∈ P ∨ (u.val,v.val) ∈ R) := by
    decide +kernel
  have active (x : Fin 14 → Bool) : pencil x = true ↔ hit P x := by
    simp only [pencil,hit,Bool.or_eq_true,Bool.and_eq_true]
    constructor
    · rintro ((⟨h0,(h8 | h10) | h7⟩ | ⟨h1,(h9 | h13) | h17⟩) | ⟨h3,(h11 | h12) | h37⟩)
      · exact ⟨0,8,by decide,h0,h8⟩
      · exact ⟨0,10,by decide,h0,h10⟩
      · exact ⟨0,7,by decide,h0,h7⟩
      · exact ⟨1,9,by decide,h1,h9⟩
      · exact ⟨1,13,by decide,h1,h13⟩
      · exact ⟨1,7,by decide,h1,h17⟩
      · exact ⟨3,11,by decide,h3,h11⟩
      · exact ⟨3,12,by decide,h3,h12⟩
      · exact ⟨3,7,by decide,h3,h37⟩
    · rintro ⟨u,v,member,hu,hv⟩
      simp only [P,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
      rcases member with eq | eq | eq | eq | eq | eq | eq | eq | eq
      · have eu : u = 0 := Fin.ext eq.1
        have ev : v = 7 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 0 := Fin.ext eq.1
        have ev : v = 8 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 0 := Fin.ext eq.1
        have ev : v = 10 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 1 := Fin.ext eq.1
        have ev : v = 7 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 1 := Fin.ext eq.1
        have ev : v = 9 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 1 := Fin.ext eq.1
        have ev : v = 13 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 3 := Fin.ext eq.1
        have ev : v = 7 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 3 := Fin.ext eq.1
        have ev : v = 11 := Fin.ext eq.2
        subst u
        subst v
        tauto
      · have eu : u = 3 := Fin.ext eq.1
        have ev : v = 12 := Fin.ext eq.2
        subst u
        subst v
        tauto
  have split (x : Fin 14 → Bool) : hit E x ↔ hit P x ∨ hit R x := by
    constructor
    · rintro ⟨u,v,edge,hu,hv⟩
      rcases (partition u v).mp edge with left | right
      · exact Or.inl ⟨u,v,left,hu,hv⟩
      · exact Or.inr ⟨u,v,right,hu,hv⟩
    · rintro (⟨u,v,e,hu,hv⟩ | ⟨u,v,e,hu,hv⟩)
      · exact ⟨u,v,(partition u v).mpr (Or.inl e),hu,hv⟩
      · exact ⟨u,v,(partition u v).mpr (Or.inr e),hu,hv⟩
  have correct (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔ hit E x := by
    have same : C.eval (List.ofFn x) = (pencil x || D.eval (lifted x)) := cEval x
    rw [same,Bool.or_eq_true,split x]
    by_cases h : pencil x = true
    · have k := (active x).mp h
      simp [h,k]
    · have h0 := Bool.eq_false_iff.mpr h
      have k : ¬ hit P x := fun a => h ((active x).mpr a)
      have eq : D.eval (lifted x) = true ↔ hit R x := dEval x h0
      simp [h,k,eq]
  refine ⟨C,cShape,cDistinct,cMin,by omega,?_,?_⟩
  · intro x yes _
    exact (correct x).mpr (of_decide_eq_true yes)
  · intro x no _
    exact Bool.eq_false_iff.mpr (fun h => of_decide_eq_false no ((correct x).mp h))
