import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_704

open PEqualNP.AndCount AndCountCircuit

theorem star_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T U : Finset (Fin n)) (cov : ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) :
    (starCircuit G T).eval U = true ↔ ∃ a ∈ U, ∃ b ∈ U, G.Adj a b := by
  classical
  have gate (i : Fin T.card) : (starCircuit G T).gateVal U i = true ↔
      T.orderEmbOfFin rfl i ∈ U ∧ ∃ b ∈ U, G.Adj (T.orderEmbOfFin rfl i) b := by
    obtain ⟨k,h⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
    unfold gateVal
    change gateValFuel (starCircuit G T) U T.card i = true ↔ _
    rw [congrArg (fun d => (starCircuit G T).gateValFuel U d i) h]
    simp [gateValFuel, sideTrue, starCircuit, and_comm]
    constructor
    · rintro ⟨ha | ⟨j,hj,_⟩, hb | ⟨l,hl,_⟩⟩
      · exact ⟨ha,hb⟩
      · exact (Finset.notMem_empty l hl).elim
      · exact (Finset.notMem_empty j hj).elim
      · exact (Finset.notMem_empty j hj).elim
    · exact fun ⟨ha,hb⟩ => ⟨Or.inl ha, Or.inl hb⟩
  change decide (_ ∨ _) = true ↔ _
  simp only [decide_eq_true_eq, starCircuit, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨ha,b,hb,h⟩ := (gate i).mp hi.2
    exact ⟨_,ha,b,hb,h⟩
  · rintro ⟨a,ha,b,hb,h⟩
    have from_center (v w : Fin n) (hv : v ∈ T) (hvU : v ∈ U) (hw : w ∈ U) (edge : G.Adj v w) :
        ∃ i : Fin T.card, i ∈ (Finset.univ : Finset (Fin T.card)) ∧ (starCircuit G T).gateVal U i = true := by
      obtain ⟨i,rfl⟩ := (T.range_orderEmbOfFin rfl).ge hv
      exact ⟨i, Finset.mem_univ _, (gate i).mpr ⟨hvU,w,hw,edge⟩⟩
    rcases cov a b h with ht | ht
    · exact from_center a b ht ha hb h
    · exact from_center b a ht hb ha h.symm

end PEqualNP.Outside.L_meta_704

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem PEqualNP.Outside.L_meta_704 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
    (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) →
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).WellFormed ∧
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size = T.card ∧
      ∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
        (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval I = false ∧
        ∀ x : Fin n, x ∉ I → (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval (insert x I) = true := by
  intro n G _ T cover
  refine ⟨?_, rfl, ?_⟩
  · intro i
    constructor <;> intro j hj <;> exact (Finset.notMem_empty j hj).elim
  · intro I hind hmax
    constructor
    · apply Bool.eq_false_iff.mpr
      rintro h
      obtain ⟨a, ha, b, hb, hab⟩ := (PEqualNP.Outside.L_meta_704.star_eval G T I cover).mp h
      exact hind a ha b hb hab
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := hmax x hx
      exact (PEqualNP.Outside.L_meta_704.star_eval G T (insert x I) cover).mpr
        ⟨x, Finset.mem_insert_self .., v, Finset.mem_insert_of_mem hv, hxv⟩
