import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- A nonstar gate in either permitted ownership shape contains an induced path on four vertices.
-- Gates already owning a star can be passed without changing the circuit.
theorem PEqualNP.Outside.R_meta_5377_1
    (classify : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (O : Fin n → Fin n → Prop),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      (∀ a b, O a b → G.Adj a b) →
      ((∃ a b, O a b ∧ ∀ u v, O u v → u = a ∨ v = a ∨ u = b ∨ v = b) ∨
        ∃ a b c d e, O a b ∧ O b c ∧ O c d ∧ O d e ∧ O e a) →
      (∃ a, ∀ u v, O u v → u = a ∨ v = a) ∨
        ∃ p a b q, (O p a ∨ O a p) ∧ O a b ∧ (O b q ∨ O q b) ∧
          ¬ G.Adj p b ∧ ¬ G.Adj a q ∧ ¬ G.Adj p q)
    (advance :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      let O := fun (C : Circuit) (j : ℕ) (u v : Fin n) => G.Adj u v ∧ Owns n C j u v
      let good := fun C : Circuit =>
        IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
          ∀ j : ℕ, (∀ u v, ¬ O C j u v) ∨
            (∃ a b, O C j a b ∧ ∀ u v, O C j u v → u = a ∨ v = a ∨ u = b ∨ v = b) ∨
            ∃ a b c d e, O C j a b ∧ O C j b c ∧ O C j c d ∧ O C j d e ∧ O C j e a ∧
              (∀ u v, O C j u v → u = a ∨ u = b ∨ u = c ∨ u = d ∨ u = e) ∧
              gateVal n C j (pairInput a a) = true
      let earlier := fun (C : Circuit) (k : ℕ) =>
        ∀ j < k, (∀ u v, ¬ O C j u v) ∨ ∃ a, ∀ u v, O C j u v → u = a ∨ v = a
      ∀ (C : Circuit) (k : ℕ), good C → k < C.size → earlier C k →
        (∃ p a b q, (O C k p a ∨ O C k a p) ∧ O C k a b ∧ (O C k b q ∨ O C k q b) ∧
          ¬ G.Adj p b ∧ ¬ G.Adj a q ∧ ¬ G.Adj p q) →
        ∃ D : Circuit, good D ∧ earlier D (k+1)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],
      (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →
      PEqualNP.TopForm.NoFourCycle x2 →
      have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;
      have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ), (∀ (x9 x10 : Fin x1), ¬x6 x7 x8 x9 x10) ∨ (∃ (x9 : Fin x1) (x10 : Fin x1), x6 x7 x8 x9 x10 ∧ ∀ (x11 x12 : Fin x1), x6 x7 x8 x11 x12 → x11 = x9 ∨ x12 = x9 ∨ x11 = x10 ∨ x12 = x10) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1), x6 x7 x8 x9 x10 ∧ x6 x7 x8 x10 x11 ∧ x6 x7 x8 x11 x12 ∧ x6 x7 x8 x12 x13 ∧ x6 x7 x8 x13 x9 ∧ (∀ (x14 x15 : Fin x1), x6 x7 x8 x14 x15 → x14 = x9 ∨ x14 = x10 ∨ x14 = x11 ∨ x14 = x12 ∨ x14 = x13) ∧ PEqualNP.EdgeOwnership.gateVal x1 x7 x8 (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.true;
      have x8 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) => ∀ x10 < x9, (∀ (x12 x13 : Fin x1), ¬x6 x8 x10 x12 x13) ∨ ∃ (x12 : Fin x1), ∀ (x13 x14 : Fin x1), x6 x8 x10 x13 x14 → x13 = x12 ∨ x14 = x12;
      ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x7 x9 → x10 < x9.size → x8 x9 x10 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), x7 x14 ∧ x8 x14 (x10 + (1 : ℕ)) := by
  intro n G inst triangle square
  dsimp only
  intro C k good bound earlier
  let O (u v : Fin n) := G.Adj u v ∧ Owns n C k u v
  have current :
      ((∀ u v, ¬ O u v) ∨ ∃ a, ∀ u v, O u v → u = a ∨ v = a) ∨
      ∃ p a b q, (O p a ∨ O a p) ∧ O a b ∧ (O b q ∨ O q b) ∧
        ¬ G.Adj p b ∧ ¬ G.Adj a q ∧ ¬ G.Adj p q := by
    rcases good.2.2 k with empty | shapes
    · exact Or.inl (Or.inl empty)
    have skeleton :
        (∃ a b, O a b ∧ ∀ u v, O u v → u = a ∨ v = a ∨ u = b ∨ v = b) ∨
        ∃ a b c d e, O a b ∧ O b c ∧ O c d ∧ O d e ∧ O e a := by
      rcases shapes with pair | ⟨a,b,c,d,e,ab,bc,cd,de,ea,_,_⟩
      · exact Or.inl pair
      · exact Or.inr ⟨a,b,c,d,e,ab,bc,cd,de,ea⟩
    rcases classify n G O triangle square (fun a b h => h.1) skeleton with star | obstruction
    · exact Or.inl (Or.inr star)
    · exact Or.inr obstruction
  rcases current with star | obstruction
  · refine ⟨C, good, ?_⟩
    intro j hj
    by_cases before : j < k
    · exact earlier j before
    · have eq : j = k := by omega
      subst j
      exact star
  · exact advance n G triangle square C k good bound earlier obstruction
