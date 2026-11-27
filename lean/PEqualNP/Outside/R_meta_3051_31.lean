import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_3051_31
    (chart : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      0 < q → n = q^2 + q + 1 →
      (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∃ (P : Fin (q*q) ↪ Fin n) (L : (Fin (q+1) × Fin q) ↪ Fin n)
        (b : Fin (q+1) → Fin (q*q) → Fin q),
        (∀ i j, i ≠ j → Function.Bijective (fun p => (b i p, b j p))) ∧
        ∀ p i t, I (P p) (L (i,t)) ↔ b i p = t)
    (codeBound : ∀ (q n : ℕ) (P : Fin (q*q) ↪ Fin n) (L : (Fin (q+1) × Fin q) ↪ Fin n)
      (b : Fin (q+1) → Fin (q*q) → Fin q) (C : Circuit),
      300 ≤ q → (∀ i j, i ≠ j → Function.Bijective (fun p => (b i p, b j p))) → Monotone2 C →
      (∀ p i, C.eval (incidenceInput {P p} {L (i,b i p)}) = true) →
      (∀ (X : Finset (Fin (q*q))) (Y : Finset (Fin (q+1) × Fin q)), Y.card ≤ q →
        (∀ p ∈ X, ∀ i, (i,b i p) ∉ Y) → C.eval (incidenceInput (X.map P) (Y.map L)) = false) →
      q^2 * (q+1) ≤ 99 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n I inst C big order degrees unique mono pos neg
  obtain ⟨P,L,b,orth,inc⟩ := chart q n I (by omega) order degrees unique
  classical
  let bits (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have evalBits (X Y : Finset (Fin n)) : C.eval (incidenceInput X Y) = circuitFun (n+n) C (bits X Y) := by
    exact congrArg C.eval (List.ofFn_fin_append _ _).symm
  have pair (p : Fin (q*q)) (i : Fin (q+1)) : C.eval (incidenceInput {P p} {L (i,b i p)}) = true := by
    rw [evalBits]
    convert pos (P p) (L (i,b i p)) ((inc p i _).mpr rfl) using 2
    funext w
    have sep (a z : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n z := by
      intro e
      have v := congrArg Fin.val e
      change a.val = n + z.val at v
      omega
    refine Fin.addCases (fun a => ?_) (fun a => ?_) w
    · simp only [bits,Fin.addCases_left,Finset.mem_singleton,Fin.castAdd_inj,sep,or_false]
    · simp only [bits,Fin.addCases_right,Finset.mem_singleton,Fin.natAdd_inj,
        Ne.symm (sep _ _),false_or]
  have reject (X : Finset (Fin (q*q))) (Y : Finset (Fin (q+1) × Fin q)) (small : Y.card ≤ q)
      (miss : ∀ p ∈ X, ∀ i, (i,b i p) ∉ Y) : C.eval (incidenceInput (X.map P) (Y.map L)) = false := by
    rw [evalBits]
    apply neg
    · simpa only [bits,Fin.addCases_right,decide_eq_true_eq,Fintype.card_coe,Finset.card_map] using small
    · rintro ⟨p,l,hit,onP,onL⟩
      have pMem : p ∈ X.map P := by simpa [bits] using onP
      have lMem : l ∈ Y.map L := of_decide_eq_true (by simpa only [bits,Fin.addCases_right] using onL)
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp pMem
      obtain ⟨⟨i,t⟩,ht,rfl⟩ := Finset.mem_map.mp lMem
      exact miss a ha i ((inc a i t).mp hit ▸ ht)
  have bound := codeBound q n P L b C big orth mono pair reject
  rw [order]
  have scale : 99 * q ≤ q^2 * (q+1) := by nlinarith [Nat.mul_self_le_mul_self big]
  have enough : q ≤ C.size := by omega
  nlinarith
