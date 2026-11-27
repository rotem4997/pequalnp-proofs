import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1965_5 :
    (∀ C : Circuit,
      let V (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
      let Birth (w a : ℕ) :=
        (14 + a = w ∨ InCone 14 C a (w - 14)) ∧ (gateAt C a).op = .and ∧
        V (14 + a) 0 0 = false ∧ V (14 + a) 7 7 = false ∧
        ∃ b : Fin 2, V (opnd C a b) 0 0 = true ∧ V (opnd C a (1-b)) 7 7 = true
      IsAO2 14 C →
      ∀ g : ℕ, (gateAt C g).op = .and → V (14 + g) 0 7 = true →
      (∀ b : Fin 2, V (opnd C g b) 0 0 = false ∧ V (opnd C g b) 7 7 = false) →
      ∀ b : Fin 2, ∃ a, Birth (opnd C g b) a) →
    (∀ C : Circuit,
      let V (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
      let Birth (w a : ℕ) :=
        (14 + a = w ∨ InCone 14 C a (w - 14)) ∧ (gateAt C a).op = .and ∧
        V (14 + a) 0 0 = false ∧ V (14 + a) 7 7 = false ∧
        ∃ b : Fin 2, V (opnd C a b) 0 0 = true ∧ V (opnd C a (1-b)) 7 7 = true
      C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) →
      circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ∀ g : ℕ, (gateAt C g).op = .and →
      (14 + g = C.output ∨ InCone 14 C g (C.output-14)) →
      V (14 + g) 0 7 = true →
      (∀ b : Fin 2, V (opnd C g b) 0 0 = false ∧ V (opnd C g b) 7 7 = false) →
      ¬ ∃ a, Birth (opnd C g 0) a ∧ Birth (opnd C g 1) a) →
    (∀ C : Circuit,
      let V (w : ℕ) (p q : Fin 14) := wireVal 14 C w (pairInput p q)
      let Birth (w a : ℕ) :=
        (14 + a = w ∨ InCone 14 C a (w - 14)) ∧ (gateAt C a).op = .and ∧
        V (14 + a) 0 0 = false ∧ V (14 + a) 7 7 = false ∧
        ∃ b : Fin 2, V (opnd C a b) 0 0 = true ∧ V (opnd C a (1-b)) 7 7 = true
      C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) →
      circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ∀ g : ℕ, (gateAt C g).op = .and →
      (14 + g = C.output ∨ InCone 14 C g (C.output-14)) →
      V (14 + g) 0 7 = true →
      (∀ b : Fin 2, V (opnd C g b) 0 0 = false ∧ V (opnd C g b) 7 7 = false) →
      (¬ ∃ a, Birth (opnd C g 0) a ∧ Birth (opnd C g 1) a) →
      ¬ ∃ a b, Birth (opnd C g 0) a ∧ Birth (opnd C g 1) b) →
¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  intro trace shared separate h
  obtain ⟨C,hSize,hGate,hEval,g,hAnd,hOut,hPair,hSingles⟩ := h
  have get (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or,[]⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj
  have facts (j : ℕ) (hj : j < C.gates.length) :=
    hGate j (C.gates[j]'hj) (List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩)
  have hAO : IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g' hg'
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg'
      exact (facts j hj).1
    · intro j hj w hw
      obtain ⟨a,b,he,_,ha,hb⟩ := (facts j hj).2
      rw [get j hj,he] at hw
      rcases (show w = a ∨ w = b by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
    · intro g' hg'
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg'
      obtain ⟨a,b,he,_,_,_⟩ := (facts j hj).2
      simp [he]
  have hDistinct (j : ℕ) (hj : j < C.gates.length) : (gateAt C j).inputs.Nodup := by
    obtain ⟨a,b,he,hn,_,_⟩ := (facts j hj).2
    rw [get j hj,he]
    simpa using hn
  have geometry : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l+1 ∨ p = l+3 := by
    decide +kernel
  have hTarget : circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
      p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) := by
    funext x
    exact Bool.eq_iff_iff.mpr ((hEval x).trans (by simp only [decide_eq_true_eq,geometry]))
  have noShared := shared C hSize hAO hDistinct hTarget g hAnd hOut hPair hSingles
  obtain ⟨a,ha⟩ := trace C hAO g hAnd hPair hSingles 0
  obtain ⟨b,hb⟩ := trace C hAO g hAnd hPair hSingles 1
  exact separate C hSize hAO hDistinct hTarget g hAnd hOut hPair hSingles noShared ⟨a,b,ha,hb⟩
