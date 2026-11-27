import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Separate gate elimination for nested ANDs from the lower bound without nesting.
theorem PEqualNP.Outside.R_meta_2389_1 :
  (let diff : Finset (Fin 13) := {0, 1, 3, 9}
    let correct := fun C : Circuit =>
      (∀ p l : Fin 13, p - l ∈ diff → C.eval
        (List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
          List.ofFn (fun l' : Fin 13 => decide (l' = l))) = true) ∧
      (∀ Q : Finset (Fin 13), Q.card = 4 →
        (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) → C.eval
          (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff))) = false)
    let nested := fun C : Circuit => ∃ i j : ℕ,
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → C.size < 64 → nested C →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ correct D ∧ D.size < C.size) →
  (let diff : Finset (Fin 13) := {0, 1, 3, 9}
    let correct := fun C : Circuit =>
      (∀ p l : Fin 13, p - l ∈ diff → C.eval
        (List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
          List.ofFn (fun l' : Fin 13 => decide (l' = l))) = true) ∧
      (∀ Q : Finset (Fin 13), Q.card = 4 →
        (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) → C.eval
          (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff))) = false)
    let nested := fun C : Circuit => ∃ i j : ℕ,
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → ¬ nested C → 64 ≤ C.size) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  intro shrink flat C hForm hFun
  let diff : Finset (Fin 13) := {0, 1, 3, 9}
  let correct := fun C : Circuit =>
    (∀ p l : Fin 13, p - l ∈ diff → C.eval
      (List.ofFn (fun p' : Fin 13 => decide (p' = p)) ++
        List.ofFn (fun l' : Fin 13 => decide (l' = l))) = true) ∧
    (∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ l : Fin 13, (Q.filter (fun p => p - l ∈ diff)).card ≤ 2) → C.eval
        (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff))) = false)
  let nested := fun C : Circuit => ∃ i j : ℕ,
    (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
  change (∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → C.size < 64 → nested C →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ correct D ∧ D.size < C.size) at shrink
  change (∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C → ¬ nested C → 64 ≤ C.size) at flat
  have lower : ∀ n : ℕ, ∀ C : Circuit, C.size = n → Monotone2 C → ReadsBack 26 C →
      correct C → 64 ≤ C.size := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n smaller =>
      intro C hsize hmon hback hcorrect
      by_cases hnested : nested C
      · by_contra hbound
        have hbudget : C.size < 64 := by omega
        obtain ⟨D, hdmon, hdback, hdcorrect, hdsmall⟩ :=
          shrink C hmon hback hcorrect hbudget hnested
        have hdsize : D.size < n := hsize ▸ hdsmall
        have hdlower := smaller D.size hdsize D rfl hdmon hdback hdcorrect
        omega
      · exact flat C hmon hback hcorrect hnested
  have hmon : Monotone2 C :=
    fun g hg => ⟨hForm.1 g hg, (hForm.2.2 g hg).le⟩
  have hdiff : ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔ p - l ∈ diff := by decide
  have hcorrect : correct C := by
    constructor
    · intro p l hpl
      let z : Fin (13 + 13) → Bool := Fin.append (fun u => decide (u = p)) (fun v => decide (v = l))
      have hz : C.eval (List.ofFn z) = true := by
        apply (hFun z).2
        exact ⟨p, l, (hdiff p l).mpr hpl, by simp only [z, Fin.append_left, Fin.append_right, decide_eq_true_eq, eq_self_iff_true], by simp only [z, Fin.append_left, Fin.append_right, decide_eq_true_eq, eq_self_iff_true]⟩
      rwa [List.ofFn_fin_append] at hz
    · intro Q hQ hLines
      let z : Fin (13 + 13) → Bool := Fin.append (fun p => decide (p ∈ Q))
        (fun l => decide (∀ p ∈ Q, p - l ∉ diff))
      have hlist : List.ofFn z =
          List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
            List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ diff)) :=
        List.ofFn_fin_append _ _
      rw [← hlist]
      cases hz : C.eval (List.ofFn z) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨p, l, hpl, hp, hl⟩ := (hFun z).1 hz
        have hpQ : p ∈ Q := by simpa only [z, Fin.append_left, Fin.append_right, decide_eq_true_eq] using hp
        have hnone : ∀ r ∈ Q, r - l ∉ diff := by simpa only [z, Fin.append_left, Fin.append_right, decide_eq_true_eq] using hl
        exact hnone p hpQ ((hdiff p l).mp hpl)
  exact lower C.size C rfl hmon hForm.2.1 hcorrect
