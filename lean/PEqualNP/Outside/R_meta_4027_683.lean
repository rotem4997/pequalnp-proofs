import PEqualNP.Defs
import Mathlib.Tactic.FinCases

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4027_683
    (mono : ∀ (C : Circuit),
      (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ w, Monotone (fun x : Fin 26 → Bool => (C.wires (List.ofFn x)).getD w false))
    (certificate :
      let E := fun (p l : Fin 13) => l ≠ 1 ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)
      ∃ (C : Circuit) (w : ℕ), C.size ≤ 59 ∧ 26 ≤ C.output ∧ C.output < 26+C.size ∧
        26 ≤ w ∧ w < 26+C.size ∧
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ,
            g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) ∧
        (∀ i ∈ ([1,2] : List (Fin 26)),
          (C.wires (List.ofFn (fun j => decide (j=i)))).getD w false = true) ∧
        (C.wires (List.ofFn (fun j : Fin 26 => decide (j ≠ 1 ∧ j ≠ 2)))).getD w false = false ∧
        (∀ p l : Fin 13, E p l →
          C.eval (List.ofFn (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) ∧
        ∀ a : Fin 13 → Bool,
          C.eval (List.ofFn (Fin.addCases a (fun l => decide (∀ p, a p = true → ¬ E p l)))) = false) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (59 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size ∧ (26 : ℕ) ≤ x2 ∧ x2 < (26 : ℕ) + x1.size ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ (∀ (x3 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ)))) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x5 ≠ (1 : Fin (13 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true := by
  classical
  let E := fun (p l : Fin 13) => l ≠ 1 ∧ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)
  obtain ⟨C,w,hs,ho,hob,hw,hwb,hlegal,hseed,hzero,hpos,hneg⟩ := certificate
  have hm := mono C (by
    intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    exact (hlegal j g hj).1)
  have fall (i : ℕ) (x y : Fin 26 → Bool) (hxy : x ≤ y)
      (hy : (C.wires (List.ofFn y)).getD i false = false) :
      (C.wires (List.ofFn x)).getD i false = false :=
    by
      have hle := hm i hxy
      dsimp only at hle
      rw [hy] at hle
      exact le_antisymm hle (Bool.false_le _)
  refine ⟨C,w,hs,ho,hob,hw,hwb,hlegal,?_,?_⟩
  · intro x
    by_cases h : x 1 = true ∨ x 2 = true
    · have rise (i : Fin 26) (hi : i ∈ ([1,2] : List (Fin 26))) (hx : x i = true) :
          (C.wires (List.ofFn x)).getD w false = true := by
        have hle : (fun j : Fin 26 => decide (j=i)) ≤ x := by
          intro j
          by_cases hji : j=i
          · subst j; simp [hx]
          · simp [hji]
        exact Bool.eq_true_of_true_le ((hseed i hi) ▸ hm w hle)
      have out : (C.wires (List.ofFn x)).getD w false = true := by
        rcases h with h | h
        · exact rise 1 (by simp) h
        · exact rise 2 (by simp) h
      rw [out]
      symm
      simpa only [Bool.or_eq_true] using h
    · have hx1 : x 1 = false := Bool.eq_false_iff.mpr (fun h1 => h (Or.inl h1))
      have hx2 : x 2 = false := Bool.eq_false_iff.mpr (fun h2 => h (Or.inr h2))
      have hle : x ≤ (fun j : Fin 26 => decide (j ≠ 1 ∧ j ≠ 2)) := by
        intro j
        by_cases h1 : j=1
        · subst j; simp [hx1]
        by_cases h2 : j=2
        · subst j; simp [hx2]
        simp [h1,h2]
      rw [fall w _ _ hle hzero, hx1, hx2]
      rfl
  · intro x
    constructor
    · intro hout
      by_contra hn
      let a : Fin 13 → Bool := fun p => x (Fin.castAdd 13 p)
      let b : Fin 13 → Bool := fun l => decide (∀ p, a p = true → ¬ E p l)
      have hle : x ≤ (fun i : Fin 26 => Fin.addCases a b i) := by
        intro i
        refine Fin.addCases (n := 13) (m := 13) (fun p => ?_) (fun l => ?_) i
        · simp [a]
        · simp only [Fin.addCases_right]
          change x (Fin.natAdd 13 l) ≤ b l
          cases hl : x (Fin.natAdd 13 l)
          · exact Bool.false_le _
          · have hb : b l = true := by
              apply decide_eq_true
              intro p hp he
              exact hn ⟨p,l,he.1,he.2,hp,hl⟩
            simp [hb]
      have hz := fall C.output x (fun i : Fin 26 => Fin.addCases a b i) hle (show (C.wires (List.ofFn (fun i : Fin 26 => Fin.addCases a b i))).getD C.output false = false from hneg a)
      change C.eval (List.ofFn x) = false at hz
      rw [hz] at hout
      contradiction
    · rintro ⟨p,l,hl,he,hp,hy⟩
      let z : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      have hle : z ≤ x := by
        intro i
        by_cases h : i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l
        · rcases h with rfl | rfl
          · change decide (_ ∨ _) ≤ _
            rw [show decide (Fin.castAdd 13 p = Fin.castAdd 13 p ∨ Fin.castAdd 13 p = Fin.natAdd 13 l) = true from decide_eq_true (Or.inl rfl), hp]
          · change decide (_ ∨ _) ≤ _
            rw [show decide (Fin.natAdd 13 l = Fin.castAdd 13 p ∨ Fin.natAdd 13 l = Fin.natAdd 13 l) = true from decide_eq_true (Or.inr rfl), hy]
        · change decide (_ ∨ _) ≤ _
          rw [decide_eq_false h]
          exact Bool.false_le _
      exact Bool.eq_true_of_true_le ((hpos p l ⟨hl,he⟩) ▸ hm C.output hle)
