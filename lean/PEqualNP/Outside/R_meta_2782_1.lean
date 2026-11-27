import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_2782_1
  (column : ∀ (n : ℕ) (C : Circuit) (s : Finset (Fin n)) (l : Fin n),
    IsAO2 (n+n) C → C.output < n+n+C.size →
    (∀ p ∈ s, C.eval (incidenceInput {p} {l}) = true) →
    C.eval (incidenceInput sᶜ {l}) = false →
    ∃ J : Finset ℕ, s.card ≤ J.card + 1 ∧ ∀ j ∈ J, j < C.size ∧ (gateAt C j).op = .or ∧
      let v := fun X : Finset (Fin n) => wireValue C (incidenceInput X {l}) (n+n+j)
      v sᶜ = false ∧ (∃ a b : Fin n, a ≠ b ∧ v {a} = true ∧ v {b} = true) ∧
      ∀ p : Fin n, v {p} = true → p ∈ s)
  (sharing : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
        100 < q → n = q^2+q+1 →
        (∀ l, (S l).card = q+1) →
        (∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l) →
        IsAO2 (n+n) C → C.output < n+n+C.size →
        RightOnIncidentPairs S C →
        (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
        (∃ j < C.size, (gateAt C j).op = .or ∧ ∃ K : Finset (Fin n), 100 < K.card ∧
          let A := fun l : Fin n => Finset.univ.filter (fun p : Fin n =>
            wireValue C (incidenceInput {p} {l}) (n+n+j))
          Set.InjOn A (K : Set (Fin n)) ∧ ∀ l ∈ K, 1 < (A l).card ∧ A l ⊆ S l ∧
            wireValue C (incidenceInput (S l)ᶜ {l}) (n+n+j) = false) →
        n*q ≤ 100*C.size) :
  ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (U : Finset ℕ),
        100 < q → n = q^2+q+1 →
        (∀ l, (S l).card = q+1) →
        (∀ p p' : Fin n, p ≠ p' → ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l) →
        IsAO2 (n+n) C → C.output < n+n+C.size →
        RightOnIncidentPairs S C →
        (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
        (∀ j < C.size, j ∉ U → (gateAt C j).op = GateOp.and →
          ∃ P L : Finset (Fin n) → Bool, ∀ X Y : Finset (Fin n),
            wireValue C (incidenceInput X Y) (n+n+j) = (P X && L Y)) →
        100 * U.card < n * q → n * q ≤ 100 * C.size := by
  classical
  intro q n S C U hq shape lineSize through basis output accept reject _ _
  have each (l : Fin n) := column n C (S l) l basis output (accept l) (reject _ _ (by simp; omega) (by
    intro k hk; simp only [Finset.mem_singleton] at hk; subst k; exact disjoint_compl_right))
  choose J count gates using each
  let K (j : ℕ) := Finset.univ.filter (fun l : Fin n => j ∈ J l)
  by_cases heavy : ∃ j < C.size, 100 < (K j).card
  · obtain ⟨j,hj,many⟩ := heavy
    obtain ⟨l₀,hl₀⟩ := Finset.card_pos.mp (show 0 < (K j).card by omega)
    have ok (l : Fin n) (hl : l ∈ K j) := gates l j (Finset.mem_filter.mp hl).2
    refine sharing q n S C hq shape lineSize through basis output accept reject
      ⟨j,hj,(ok l₀ hl₀).2.1,K j,many,?_,?_⟩
    · intro l hl k hk eqA
      obtain ⟨_,_,_,rich,sub⟩ := ok l hl
      obtain ⟨a,b,ne,yesA,yesB⟩ := rich
      have other := (ok k hk).2.2.2.2
      let A (t : Fin n) := Finset.univ.filter (fun p : Fin n => wireValue C (incidenceInput {p} {t}) (n+n+j))
      change A l = A k at eqA
      have ha : a ∈ A l := Finset.mem_filter.mpr ⟨Finset.mem_univ _,yesA⟩
      have hb : b ∈ A l := Finset.mem_filter.mpr ⟨Finset.mem_univ _,yesB⟩
      have ak : a ∈ A k := eqA ▸ ha
      have bk : b ∈ A k := eqA ▸ hb
      exact (through a b ne).unique ⟨sub a (Finset.mem_filter.mp ha).2, sub b (Finset.mem_filter.mp hb).2⟩
        ⟨other a (Finset.mem_filter.mp ak).2,other b (Finset.mem_filter.mp bk).2⟩
    · intro l hl
      obtain ⟨_,_,off,rich,sub⟩ := ok l hl
      obtain ⟨a,b,ne,ya,yb⟩ := rich
      exact ⟨Finset.one_lt_card.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ya⟩,b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,yb⟩,ne⟩,fun p hp => sub p (Finset.mem_filter.mp hp).2,off⟩
  · have small (j : ℕ) (hj : j ∈ Finset.range C.size) : (K j).card ≤ 100 :=
      Nat.le_of_not_gt (fun e => heavy ⟨j,Finset.mem_range.mp hj,e⟩)
    have cardJ (l : Fin n) : (J l).card = ∑ j ∈ Finset.range C.size, (if j ∈ J l then 1 else 0) := by
      rw [← Finset.sum_filter]
      have eq : (Finset.range C.size).filter (fun j => j ∈ J l) = J l :=
        Finset.ext (fun j => by simp only [Finset.mem_filter,Finset.mem_range]; exact ⟨And.right,fun h => ⟨(gates l j h).1,h⟩⟩)
      simp [eq]
    calc n*q = ∑ _ : Fin n, q := by simp
         _ ≤ ∑ l : Fin n, (J l).card := Finset.sum_le_sum (fun l _ => by have h := count l; rw [lineSize] at h; omega)
         _ = ∑ j ∈ Finset.range C.size, (K j).card := by
           simp_rw [cardJ]
           rw [Finset.sum_comm]
           apply Finset.sum_congr rfl
           intro j _
           rw [show (K j).card = _ from Finset.card_filter _ _]
         _ ≤ ∑ _j ∈ Finset.range C.size, 100 := Finset.sum_le_sum small
         _ = 100*C.size := by simp [Nat.mul_comm]
