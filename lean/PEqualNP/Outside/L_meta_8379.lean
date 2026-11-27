import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8379_aux

theorem ev_nil (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hg : C.gates = [])
    (y : Fin m → Bool) :
    PEqualNP.MetaComplexity.circuitFun m C y = (List.ofFn y).getD C.output false := by
  simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, hg]

theorem natAdd_inj' {m k : ℕ} {a b : Fin k} : Fin.natAdd m a = Fin.natAdd m b ↔ a = b := by
  simp [Fin.ext_iff]

end PEqualNP.Outside.L_meta_8379_aux

theorem PEqualNP.Outside.L_meta_8379 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → ∀ (x13 : Fin (x2 + x2) → Bool), (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.true → x1 < Fintype.card { x16 : Fin x2 // x13 (Fin.natAdd x2 x16) = Bool.true } → (∀ (x17 : Fin x2), x13 (Fin.natAdd x2 x17) = Bool.true → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (Function.update x13 (Fin.natAdd x2 x17) Bool.false) = Bool.false) → x5.gates = [] → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N R _ C hq hN hdeg huniq hmono hinc hfalse x hnot htrue hcard hmin hg
  exfalso
  rw [L_meta_8379_aux.ev_nil _ _ hg] at htrue
  have hout : C.output < N + N := by
    by_contra h
    rw [List.getD_eq_default _ _ (by simp; omega)] at htrue
    exact Bool.false_ne_true htrue
  have hxo : x ⟨C.output, hout⟩ = true := by
    rw [List.getD_eq_getElem _ _ (by simpa using hout), List.getElem_ofFn] at htrue
    exact htrue
  have h2 : 1 < Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } := by omega
  obtain ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩, hne⟩ := Fintype.one_lt_card_iff.mp h2
  have hne' : l1 ≠ l2 := fun h => hne (Subtype.ext h)
  have key : ∀ l : Fin N, x (Fin.natAdd N l) = true →
      (Fin.natAdd N l : Fin (N + N)) ≠ ⟨C.output, hout⟩ → False := by
    intro l hl hlo
    have hm := hmin l hl
    rw [L_meta_8379_aux.ev_nil _ _ hg, List.getD_eq_getElem _ _ (by simpa using hout),
      List.getElem_ofFn, Function.update_of_ne (Ne.symm hlo), hxo] at hm
    exact absurd hm (by decide)
  by_cases h1 : (Fin.natAdd N l1 : Fin (N + N)) = ⟨C.output, hout⟩
  · apply key l2 hl2
    intro h2'
    exact hne' (L_meta_8379_aux.natAdd_inj'.mp (h1.trans h2'.symm))
  · exact key l1 hl1 h1
