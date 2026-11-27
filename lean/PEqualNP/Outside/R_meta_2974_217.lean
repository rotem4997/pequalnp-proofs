import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_2974_217
  (peel : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 1≤q →
    let H := fun C : Circuit => Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) = true ∧
      lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧
      lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val)=false)
    let S := fun C : Circuit => ∀ x : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      circuitFun (N+N) C x=false
    let K := fun C : Circuit => ∀ v : Fin (N+N),
      let d := ((H C).filter fun e => v=Fin.castAdd N e.1 ∨ v=Fin.natAdd N e.2).card
      0<d → 24*max 1 (Fintype.card {j : Fin C.size // v.val∈(C.gates.get j).inputs}) < d
    ∀ C : Circuit, IsAO2 (N+N) C → S C → 24*C.size<(H C).card →
    ∃ D : Circuit, IsAO2 (N+N) D ∧ S D ∧ 24*D.size<(H D).card ∧ K D)
  (small : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 1≤q →
    (∀ p t, p≠t → ∃! l, I p l ∧ I t l) →
    let H := fun C : Circuit => Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) = true)
    let S := fun C : Circuit => ∀ x : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      circuitFun (N+N) C x=false
    ∀ C : Circuit, (∀ g∈C.gates, g.inputs.length≤2) → S C → C.size≤4512 → (H C).card≤24*C.size)
  (core : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 87≤q → N=q^2+q+1 →
    (∀ l, Fintype.card {p : Fin N // I p l}=q+1) →
    (∀ p t, p≠t → ∃! l, I p l ∧ I t l) →
    let H := fun C : Circuit => Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) = true ∧
      lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧
      lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val)=false)
    let S := fun C : Circuit => ∀ x : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) →
      circuitFun (N+N) C x=false
    let K := fun C : Circuit => ∀ v : Fin (N+N),
      let d := ((H C).filter fun e => v=Fin.castAdd N e.1 ∨ v=Fin.natAdd N e.2).card
      0<d → 24*max 1 (Fintype.card {j : Fin C.size // v.val∈(C.gates.get j).inputs}) < d
    ∀ C : Circuit, IsAO2 (N+N) C → S C → 4513≤C.size → K C → (H C).card≤24*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hn reg uniq ao safe
  let H := fun C : Circuit => Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) = true ∧
      lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧
      lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val)=false)
  let A := fun C : Circuit => Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) = true)
  have sub (D : Circuit) : (H D).card ≤ (A D).card := by
    apply Finset.card_le_card
    intro e he
    obtain ⟨hI,hC,_⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hI,hC⟩
  rw [Fintype.card_subtype]
  change (H C).card ≤ 24*C.size
  by_contra! fail
  obtain ⟨D,dao,ds,excess,heavy⟩ := peel q N I (by omega) C ao safe fail
  by_cases little : D.size≤4512
  · exact (Nat.not_le_of_gt excess) ((sub D).trans (small q N I (by omega) uniq D (fun g hg => (dao.2.2 g hg).le) ds little))
  · exact (Nat.not_le_of_gt excess) (core q N I hq hn reg uniq D dao ds (by omega) heavy)
