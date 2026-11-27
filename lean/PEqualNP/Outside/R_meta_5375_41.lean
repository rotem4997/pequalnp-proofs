import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The cover construction already wins if its budget is optimal.
-- For strict savings, a failed gate supplies an explicit false pair.
-- Repair just that gate while keeping the gates already repaired.
theorem PEqualNP.Outside.R_meta_5375_41
    (cover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧
        HasStarProfile n G C ∧ C.size ≤ G.edgeFinset.card + G.vertexCoverNum.toNat - 1)
    (localPair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G → Monotone2 C →
      ∀ j a b c d, G.Adj a b → Owns n C j a b → G.Adj c d → Owns n C j c d →
        a ≠ c → a ≠ d → b ≠ c → b ≠ d →
        ∃ u v, (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧ ¬ G.Adj u v ∧
          gateVal n C j (pairInput u v) = true)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      let O := fun (D : Circuit) j u v => G.Adj u v ∧ Owns n D j u v
      let linked := fun (D : Circuit) j => ∀ a b c d, O D j a b → O D j c d →
        O D j a c ∨ O D j a d ∨ O D j b c ∨ O D j b d
      ∀ (C : Circuit), IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        C.size < G.edgeFinset.card + G.vertexCoverNum.toNat - 1 →
        ∀ j < C.size, (∀ i < j, linked C i) →
        (∃ a b c d u v, O C j a b ∧ O C j c d ∧
          ¬ (O C j a c ∨ O C j a d ∨ O C j b c ∨ O C j b d) ∧
          (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧
          ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧
          D.size ≤ C.size ∧ ∀ i ≤ j, linked D i) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ) (x9 x10 x11 x12 : Fin x1), x6 x7 x8 x9 x10 → x6 x7 x8 x11 x12 → x6 x7 x8 x9 x11 ∨ x6 x7 x8 x9 x12 ∨ x6 x7 x8 x10 x11 ∨ x6 x7 x8 x10 x12 := by
  classical
  intro n G inst tri square
  let O (C : Circuit) (j : ℕ) (a b : Fin n) := G.Adj a b ∧ Owns n C j a b
  let linked (C : Circuit) (j : ℕ) := ∀ a b c d, O C j a b → O C j c d →
    O C j a c ∨ O C j a d ∨ O C j b c ∨ O C j b d
  change ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧ ∀ j, linked C j
  have flip (C : Circuit) (j : ℕ) (a b : Fin n) (h : O C j a b) : O C j b a := by
    have same : pairInput b a = pairInput a b := by
      funext w
      change decide (w = b ∨ w = a) = decide (w = a ∨ w = b)
      simp only [Bool.decide_or, Bool.or_comm]
    obtain ⟨edge,jh,op,yes,no⟩ := h
    exact ⟨edge.symm,jh,op,by rw [same]; exact yes,
      fun i hi below andOp => by rw [same]; exact no i hi below andOp⟩
  have meet (C : Circuit) (j : ℕ) (a b c d : Fin n) (ab : O C j a b) (cd : O C j c d)
      (common : a = c ∨ a = d ∨ b = c ∨ b = d) :
      O C j a c ∨ O C j a d ∨ O C j b c ∨ O C j b d := by
    rcases common with h|h|h|h
    · subst c; exact Or.inr (Or.inl cd)
    · subst d; exact Or.inl (flip _ _ _ _ cd)
    · subst c; exact Or.inl ab
    · subst d; exact Or.inr (Or.inl ab)
  obtain ⟨S,ms,fs,star,bound⟩ := cover n G
  let P (k : ℕ) := ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ C.size = k
  have existsSize : ∃ k, P k := ⟨S.size,S,ms,fs,rfl⟩
  let opt := Nat.find existsSize
  obtain ⟨B,mb,fb,sb⟩ := Nat.find_spec existsSize
  have floor (C : Circuit) (mc : Monotone2 C) (fc : circuitFun n C = graphFun G ∅) :
      opt ≤ C.size := Nat.find_min' existsSize ⟨C,mc,fc,rfl⟩
  have minimal (C : Circuit) (mc : Monotone2 C) (fc : circuitFun n C = graphFun G ∅)
      (sc : C.size = opt) : IsMinimalMonoCircuit n C :=
    ⟨mc, fun D md fd => sc ▸ floor D md (fd.trans fc)⟩
  by_cases equalSize : S.size = opt
  · refine ⟨S, minimal S ms fs equalSize, fs, ?_⟩
    intro j a b c d ab cd
    rcases star j ab.2.1 ab.2.2.1 with none | ⟨v,all⟩
    · exact (none a b ab.1 ab.2).elim
    · apply meet S j a b c d ab cd
      rcases all a b ab.1 ab.2 with h|h <;> rcases all c d cd.1 cd.2 with g|g
      · exact Or.inl (h.trans g.symm)
      · exact Or.inr (Or.inl (h.trans g.symm))
      · exact Or.inr (Or.inr (Or.inl (h.trans g.symm)))
      · exact Or.inr (Or.inr (Or.inr (h.trans g.symm)))
  have cheaper : opt < G.edgeFinset.card + G.vertexCoverNum.toNat - 1 := by
    have h := floor S ms fs
    omega
  have advance (k : ℕ) : ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      circuitFun n C = graphFun G ∅ ∧ C.size = opt ∧ ∀ j < k, linked C j := by
    induction k with
    | zero => exact ⟨B, minimal B mb fb sb, fb, sb, by simp⟩
    | succ k ih =>
      obtain ⟨C,mc,fc,sc,earlier⟩ := ih
      by_cases good : linked C k
      · exact ⟨C,mc,fc,sc,fun i hi => (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)).elim
            (earlier i) (fun e => e ▸ good)⟩
      change ¬ (∀ a b c d, O C k a b → O C k c d →
        O C k a c ∨ O C k a d ∨ O C k b c ∨ O C k b d) at good
      have counter : ∃ a b c d, O C k a b ∧ O C k c d ∧
          ¬ (O C k a c ∨ O C k a d ∨ O C k b c ∨ O C k b d) := by
        simp only [not_forall] at good
        obtain ⟨a,b,c,d,ab,cd,no⟩ := good
        exact ⟨a,b,c,d,ab,cd,no⟩
      obtain ⟨a,b,c,d,ab,cd,no⟩ := counter
      have noMeet : ¬ (a = c ∨ a = d ∨ b = c ∨ b = d) := fun h => no (meet C k a b c d ab cd h)
      obtain ⟨u,v,hu,hv,bad,fires⟩ := localPair n G C tri square mc.1 k a b c d
        ab.1 ab.2 cd.1 cd.2 (fun h => noMeet (.inl h)) (fun h => noMeet (.inr (.inl h)))
        (fun h => noMeet (.inr (.inr (.inl h)))) (fun h => noMeet (.inr (.inr (.inr h))))
      obtain ⟨D,md,fd,sd,fixed⟩ := repair n G tri square C mc fc (sc ▸ cheaper)
        k ab.2.1 earlier ⟨a,b,c,d,u,v,ab,cd,no,hu,hv,bad,fires⟩
      have full := fd.trans fc
      have eq : D.size = opt := le_antisymm (sd.trans sc.le) (floor D md full)
      exact ⟨D,minimal D md full eq,full,eq,fun i hi => fixed i (Nat.le_of_lt_succ hi)⟩
  obtain ⟨D,md,fd,sd,earlier⟩ := advance opt
  refine ⟨D,md,fd,fun j => ?_⟩
  by_cases hj : j < opt
  · exact earlier j hj
  · intro a b c d ab
    exact (hj (ab.2.1.trans_le sd.le)).elim
