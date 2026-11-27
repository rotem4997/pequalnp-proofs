import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7081_aux

open PEqualNP.AndCount Classical

variable {n k : ℕ}

noncomputable def vs (S : Finset (Finset (Fin n))) (v : Fin n) : Finset (Finset (Fin n)) :=
  S.filter (fun U => v ∈ U)

noncomputable def circ (S : Finset (Finset (Fin n))) (bare : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (Y : Finset (Finset (Fin n))) : AndCountCircuit n where
  size := k
  leftVars j := (bare j).filter (fun v => vs S v ⊆ L j)
  leftGates j := Finset.univ.filter (fun i => i < j ∧ L i ∩ R i ⊆ L j)
  rightVars j := (bare j).filter (fun v => vs S v ⊆ R j)
  rightGates j := Finset.univ.filter (fun i => i < j ∧ L i ∩ R i ⊆ R j)
  outVars := ∅
  outGates := Finset.univ.filter (fun j => L j ∩ R j ⊆ Y)

def Cl (S : Finset (Finset (Fin n))) (bare : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (j : Fin k) (T : Finset (Finset (Fin n))) : Prop :=
  ∀ U ∈ T, (∃ v ∈ bare j, U ∈ vs S v ∧ vs S v ⊆ T) ∨ ∃ i < j, U ∈ L i ∩ R i ∧ L i ∩ R i ⊆ T

theorem side_iff (S : Finset (Finset (Fin n))) (bare : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (j : Fin k) (T : Finset (Finset (Fin n)))
    (hT : Cl S bare L R j T) (U : Finset (Fin n)) (hU : U ∈ S) (val : Fin k → Bool)
    (hval : ∀ i < j, (val i = true ↔ U ∈ L i ∩ R i)) :
    AndCountCircuit.sideTrue U ((bare j).filter (fun v => vs S v ⊆ T))
      (Finset.univ.filter (fun i => i < j ∧ L i ∩ R i ⊆ T)) j val = true ↔ U ∈ T := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_true_iff]
  constructor
  · rintro (⟨v, hv, hvU⟩ | ⟨i, hi, _, hvi⟩)
    · rw [Finset.mem_filter] at hv
      exact hv.2 (by simp [vs, hU, hvU])
    · rw [Finset.mem_filter] at hi
      exact hi.2.2 ((hval i hi.2.1).1 hvi)
  · intro hUT
    rcases hT U hUT with ⟨v, hvb, hUv, hsub⟩ | ⟨i, hij, hUi, hsub⟩
    · left
      exact ⟨v, Finset.mem_filter.2 ⟨hvb, hsub⟩, (Finset.mem_filter.1 hUv).2⟩
    · right
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hij, hsub⟩, hij, (hval i hij).2 hUi⟩

theorem fuel_iff (S : Finset (Finset (Fin n))) (bare : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (Y : Finset (Finset (Fin n)))
    (hcl : ∀ j, Cl S bare L R j (L j) ∧ Cl S bare L R j (R j))
    (U : Finset (Fin n)) (hU : U ∈ S) :
    ∀ d (i : Fin k), i.val < d →
      ((circ S bare L R Y).gateValFuel U d i = true ↔ U ∈ L i ∩ R i) := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    have hval : ∀ i' < i, ((circ S bare L R Y).gateValFuel U d i' = true ↔ U ∈ L i' ∩ R i') :=
      fun i' hi' => ih i' (by have := Fin.lt_def.1 hi'; omega)
    show (AndCountCircuit.sideTrue U ((bare i).filter (fun v => vs S v ⊆ L i))
        (Finset.univ.filter (fun i' => i' < i ∧ L i' ∩ R i' ⊆ L i)) i
          ((circ S bare L R Y).gateValFuel U d) &&
        AndCountCircuit.sideTrue U ((bare i).filter (fun v => vs S v ⊆ R i))
        (Finset.univ.filter (fun i' => i' < i ∧ L i' ∩ R i' ⊆ R i)) i
          ((circ S bare L R Y).gateValFuel U d)) = true ↔ U ∈ L i ∩ R i
    rw [Bool.and_eq_true, side_iff S bare L R i (L i) (hcl i).1 U hU _ hval,
      side_iff S bare L R i (R i) (hcl i).2 U hU _ hval, Finset.mem_inter]

theorem build (S : Finset (Finset (Fin n))) (bare : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (Y : Finset (Finset (Fin n)))
    (hcl : ∀ j, Cl S bare L R j (L j) ∧ Cl S bare L R j (R j))
    (hY : ∀ U ∈ Y, ∃ j, U ∈ L j ∩ R j ∧ L j ∩ R j ⊆ Y) :
    ∃ C : AndCountCircuit n, C.WellFormed ∧ C.size = k ∧
      (∀ v : Fin n, (Finset.univ.filter (fun g : Fin C.size => v ∈ C.leftVars g ∨ v ∈ C.rightVars g)).card ≤
        (Finset.univ.filter (fun j : Fin k => v ∈ bare j)).card) ∧
      ∀ U ∈ S, C.eval U = true ↔ U ∈ Y := by
  refine ⟨circ S bare L R Y, ?_, rfl, ?_, ?_⟩
  · intro i
    constructor
    · intro j hj; exact (Finset.mem_filter.1 hj).2.1
    · intro j hj; exact (Finset.mem_filter.1 hj).2.1
  · intro v
    refine Finset.card_le_card_of_injOn (fun g => (g : Fin k)) ?_ ?_
    · intro g hg
      have hg' := (Finset.mem_filter.1 (Finset.mem_coe.1 hg)).2
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      rcases hg' with h | h
      · exact (Finset.mem_filter.1 h).1
      · exact (Finset.mem_filter.1 h).1
    · intro a _ b _ h
      exact h
  · intro U hU
    unfold AndCountCircuit.eval
    rw [decide_eq_true_iff]
    have hg : ∀ j : Fin k, ((circ S bare L R Y).gateVal U j = true ↔ U ∈ L j ∩ R j) :=
      fun j => fuel_iff S bare L R Y hcl U hU k j j.2
    constructor
    · rintro (⟨v, hv, _⟩ | ⟨j, hj, hjv⟩)
      · simp [circ] at hv
      · exact (Finset.mem_filter.1 hj).2 ((hg j).1 hjv)
    · intro hUY
      obtain ⟨j, hUj, hsub⟩ := hY U hUY
      exact Or.inr ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hsub⟩, (hg j).2 hUj⟩

end PEqualNP.Outside.L_meta_7081_aux

theorem PEqualNP.Outside.L_meta_7081 : ∀ (x1 x2 : ℕ),   let x3 : Type := Finset (Finset (Fin x1));   have x4 : Finset (Fin x2) := Finset.univ;   ∀ (x5 : x3) (x6 : Fin x2 → Finset (Fin x1)) (x7 x8 : Fin x2 → x3) (x9 : x3),     have x10 : Fin x1 → Finset (Finset (Fin x1)) := fun (x10 : Fin x1) => {x11 ∈ x5 | x10 ∈ x11};     have x11 : Fin x2 → x3 := fun (x11 : Fin x2) => x7 x11 ∩ x8 x11;     have x12 : Fin x2 → x3 → Prop := fun (x12 : Fin x2) (x13 : x3) => ∀ x14 ∈ x13, (∃ x16 ∈ x6 x12, x14 ∈ x10 x16 ∧ x10 x16 ⊆ x13) ∨ ∃ x16 < x12, x14 ∈ x11 x16 ∧ x11 x16 ⊆ x13;     (∀ (x13 : Fin x2), x12 x13 (x7 x13) ∧ x12 x13 (x8 x13)) →       (∀ x14 ∈ x9, ∃ (x16 : Fin x2), x14 ∈ x11 x16 ∧ x11 x16 ⊆ x9) →         ∃ (x15 : PEqualNP.AndCount.AndCountCircuit x1),           x15.WellFormed ∧             x15.size = x2 ∧               (have x16 : Finset (Fin x15.size) := Finset.univ;                 ∀ (x17 : Fin x1), {x18 ∈ x16 | x17 ∈ x15.leftVars x18 ∨ x17 ∈ x15.rightVars x18}.card ≤ {x18 ∈ x4 | x17 ∈ x6 x18}.card) ∧                 ∀ x16 ∈ x5, x15.eval x16 = Bool.true ↔ x16 ∈ x9 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 h1 h2
  exact PEqualNP.Outside.L_meta_7081_aux.build x5 x6 x7 x8 x9 h1 h2
