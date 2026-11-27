import Mathlib.Combinatorics.SimpleGraph.Finite
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4191_121
    (repair : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∀ S : Finset (Fin n), IsPrimeImplicant n C S → S.card = 2) →
      ∃ R : Circuit, Monotone2 R ∧ IsReadK n R 1 ∧
        R.size + 1 ≤ 3 * (C.size +
          ((List.finRange n).toFinset.powerset.filter
            fun S => IsPrimeImplicant n C S ∧ readsAtMost C n (setList S) 1 = false).card + 1) ∧
        ∀ x : Fin n → Bool, R.eval (List.ofFn x) = C.eval (List.ofFn x))
    (count : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) →
      (∀ D : Circuit, Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size) →
      ((List.finRange n).toFinset.powerset.filter
        fun S => IsPrimeImplicant n C S ∧ readsAtMost C n (setList S) 1 = false).card
        ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.ReadK.IsReadK x2 x10 (1 : ℕ) ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 : Fin x2 → Bool), x10.eval (List.ofFn x11) = x7.eval (List.ofFn x11) := by
  obtain ⟨k, hk⟩ := count
  refine ⟨3 * (k + 1), ?_⟩
  intro n G inst hdegree hgirth C hmono hC
  let good (D : Circuit) : Prop :=
    Monotone2 D ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)
  have hex : ∃ m : ℕ, ∃ D : Circuit, good D ∧ D.size = m :=
    ⟨C.size, C, ⟨hmono, fun _ => rfl⟩, rfl⟩
  classical
  obtain ⟨D, ⟨hD, heq⟩, hsize⟩ := Nat.find_spec hex
  have hmin (E : Circuit) (hE : good E) : D.size ≤ E.size := by
    rw [hsize]
    exact Nat.find_min' hex ⟨E, hE, rfl⟩
  have hDG (x : Fin n → Bool) :
      D.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :=
    (heq x).trans (hC x)
  have hpair (S : Finset (Fin n)) (hS : IsPrimeImplicant n D S) : S.card = 2 := by
    have htrue := hS.1
    change D.eval (List.ofFn (setInput S)) = true at htrue
    rw [hDG] at htrue
    obtain ⟨u, v, huv, hu, hv⟩ := of_decide_eq_true htrue
    have huS : u ∈ S := of_decide_eq_true hu
    have hvS : v ∈ S := of_decide_eq_true hv
    let T : Finset (Fin n) := {u, v}
    have hsub : T ⊆ S := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact huS
      · exact hvS
    have hTS : T = S := by
      by_contra hne
      have hfalse := hS.2 T (Finset.mem_ssubsets.mpr (ssubset_of_subset_of_ne hsub hne))
      change D.eval (List.ofFn (setInput T)) = false at hfalse
      rw [hDG] at hfalse
      exact (of_decide_eq_false hfalse)
        ⟨u, v, huv, decide_eq_true (by simp [T]), decide_eq_true (by simp [T])⟩
    simpa [T, G.ne_of_adj huv] using congrArg Finset.card hTS.symm
  have hcount := hk n G hdegree hgirth D hD hDG
    (fun E hE hED => hmin E ⟨hE, fun x => (hED x).trans (heq x)⟩)
  obtain ⟨R, hR, hread, hbound, hRD⟩ := repair n D hD hpair
  refine ⟨R, hR, hread, ?_, fun x => (hRD x).trans (heq x)⟩
  calc
    _ ≤ 3 * (D.size + _ + 1) := hbound
    _ ≤ 3 * (D.size + k * (D.size + 1) + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_left hcount _) _)
    _ = (3 * (k + 1)) * (D.size + 1) := by ring
    _ ≤ (3 * (k + 1)) * (C.size + 1) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_succ (hmin C ⟨hmono, fun _ => rfl⟩))
