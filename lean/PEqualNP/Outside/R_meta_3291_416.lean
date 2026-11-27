import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Delete an active point or line of degree at most 44 by setting its bit to false.
-- At most 44 accepted pairs disappear and at least one gate is saved.
-- It suffices to bound circuits in which every active point and line has degree at least 45.
theorem PEqualNP.Outside.R_meta_3291_416
    (erase : ∀ (n : ℕ) (C : Circuit) (a b : Fin n), IsAO2 n C → a ≠ b →
      circuitFun n C (fun i => decide (i = a)) = false →
      circuitFun n C (fun i => decide (i = b)) = false →
      circuitFun n C (fun i => decide (i = a ∨ i = b)) = true →
      ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
        (∀ x, circuitFun n D x = true → circuitFun n C x = true) ∧
        ∀ x : Fin n → Bool, x a = false → circuitFun n D x = circuitFun n C x)
    (dense : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      131 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N+N) C →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N+N) C x = false) →
      let E := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧
        circuitFun (N+N) C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true
      (∀ v : Fin (N+N), let d := (E.filter fun e => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2).card
         d = 0 ∨ 44 < d) → E.card ≤ 44*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq order degree unique legal sound
  let pt : Fin N → Fin (N+N) := Fin.castAdd N
  let ln : Fin N → Fin (N+N) := Fin.natAdd N
  let owns (v : Fin (N+N)) (e : Fin N × Fin N) := v = pt e.1 ∨ v = ln e.2
  let pair (e : Fin N × Fin N) (v : Fin (N+N)) := decide (owns v e)
  let E (D : Circuit) := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ circuitFun (N+N) D (pair e) = true
  let incident (D : Circuit) (v : Fin (N+N)) := (E D).filter (owns v)
  let Sound (D : Circuit) := ∀ x : Fin (N+N) → Bool,
    Fintype.card {l : Fin N // x (ln l) = true} ≤ q →
    (¬ ∃ p l, I p l ∧ x (pt p) = true ∧ x (ln l) = true) →
    circuitFun (N+N) D x = false
  have apart (p l : Fin N) : pt p ≠ ln l := by
    intro equal
    have h := congrArg Fin.val equal
    change p.val = N+l.val at h
    omega
  have inj (k l : Fin N) (e : ln k = ln l) : k = l := by
    apply Fin.ext
    have h := congrArg Fin.val e
    change N+k.val = N+l.val at h
    omega
  have memE (D : Circuit) (e : Fin N × Fin N) :
      e ∈ E D ↔ I e.1 e.2 ∧ circuitFun (N+N) D (pair e) = true := by simp [E]
  have offPoint (D : Circuit) (neg : Sound D) (p : Fin N) :
      circuitFun (N+N) D (fun i => decide (i = pt p)) = false := by
    apply neg
    · simp [fun l => (apart p l).symm]
    · rintro ⟨r,l,_,_,bad⟩
      exact (apart p l) (of_decide_eq_true bad).symm
  have offLine (D : Circuit) (neg : Sound D) (l : Fin N) :
      circuitFun (N+N) D (fun i => decide (i = ln l)) = false := by
    apply neg
    · rw [Fintype.card_subtype]
      have sub : (Finset.univ.filter fun k : Fin N => decide (ln k = ln l) = true) ⊆ {l} := by
        intro k hk
        exact Finset.mem_singleton.mpr (inj k l (of_decide_eq_true (Finset.mem_filter.mp hk).2))
      have h := Finset.card_le_card sub
      simp only [Finset.card_singleton] at h
      exact h.trans (by omega)
    · rintro ⟨p,k,_,bad,_⟩
      exact apart p l (of_decide_eq_true bad)
  have bound (k : ℕ) : ∀ D : Circuit, D.size = k → IsAO2 (N+N) D → Sound D →
      (E D).card ≤ 44 * D.size := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D hk ao neg
      by_cases core : ∀ v, (incident D v).card = 0 ∨ 44 < (incident D v).card
      · exact dense q N I D hq order degree unique ao neg core
      push Not at core
      obtain ⟨v, present, cheap⟩ := core
      obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero present)
      obtain ⟨member, endpoint⟩ := Finset.mem_filter.mp he
      have accepted := ((memE D e).mp member).2
      have smaller : ∃ D' : Circuit, IsAO2 (N+N) D' ∧ D'.size < D.size ∧
          (∀ x, circuitFun (N+N) D' x = true → circuitFun (N+N) D x = true) ∧
          ∀ x : Fin (N+N) → Bool, x v = false → circuitFun (N+N) D' x = circuitFun (N+N) D x := by
        change v = pt e.1 ∨ v = ln e.2 at endpoint
        rcases endpoint with rfl | rfl
        · exact erase (N+N) D (pt e.1) (ln e.2) ao (apart _ _)
            (offPoint D neg _) (offLine D neg _) accepted
        · apply erase (N+N) D (ln e.2) (pt e.1) ao (apart _ _).symm
            (offLine D neg _) (offPoint D neg _)
          simpa only [pair,owns,or_comm] using accepted
      obtain ⟨D',valid,save,below,same⟩ := smaller
      have keepsSound : Sound D' := by
        intro x hx noEdges
        cases e : circuitFun (N+N) D' x with
        | false => rfl
        | true => exact False.elim (Bool.noConfusion ((below x e).symm.trans (neg x hx noEdges)))
      have sub : E D ⊆ E D' ∪ incident D v := by
        intro a ha
        by_cases hv : owns v a
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha,hv⟩)
        · obtain ⟨flag,hit⟩ := (memE D a).mp ha
          have noBit : pair a v = false := by simp [pair,hv]
          exact Finset.mem_union_left _ ((memE D' a).mpr ⟨flag,(same (pair a) noBit).trans hit⟩)
      have count := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
      have prev := ih D'.size (by omega) D' rfl valid keepsSound
      omega
  have h := bound C.size C rfl legal sound
  simpa only [Fintype.card_subtype] using h
