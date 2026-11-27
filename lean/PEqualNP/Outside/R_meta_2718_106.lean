import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2718_106
    (bypass : ∀ (C : Circuit) (i a b w : ℕ),
      C.gates[i]? = some ⟨.and,[a,b]⟩ → (w=a ∨ w=b) →
      let D : Circuit := ⟨C.gates.set i ⟨.and,[w]⟩, C.output⟩
      Monotone2 C → Monotone2 D ∧ D.size = C.size ∧
      (D.gates.countP (fun g => g.inputs.length == 2)) < (C.gates.countP (fun g => g.inputs.length == 2)) ∧
      ∀ x : List Bool, C.eval x = true → D.eval x = true)
    (safeFork : let neg := (fun (C : Circuit) => ∀ X : Finset (Fin 13),
      (∀ p ∉ X, ∃ l ∈ missLines singerLines3 X, p ∈ singerLines3 l) →
      (¬InNoLine singerLines3 X ∨ ¬InNoPencil singerLines3 (missLines singerLines3 X)) →
      C.eval (incidenceInput X (missLines singerLines3 X)) = false);
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 → RightOnIncidentPairs singerLines3 C → neg C →
      2 < C.lineDeg 26 (Finset.Ico 13 26) → 2 < C.lineDeg 26 (Finset.range 13) →
      ∃ i a b w : ℕ, C.gates[i]? = some ⟨.and,[a,b]⟩ ∧ (w=a ∨ w=b) ∧
        neg ⟨C.gates.set i ⟨.and,[w]⟩, C.output⟩)
    (thinSound : let neg := (fun (C : Circuit) => ∀ X : Finset (Fin 13),
      (∀ p ∉ X, ∃ l ∈ missLines singerLines3 X, p ∈ singerLines3 l) →
      (¬InNoLine singerLines3 X ∨ ¬InNoPencil singerLines3 (missLines singerLines3 X)) →
      C.eval (incidenceInput X (missLines singerLines3 X)) = false);
      ∀ C : Circuit, Monotone2 C → RightOnIncidentPairs singerLines3 C → neg C →
      (HasLineDegree 26 (Finset.Ico 13 26) C 2 ∨ HasLineDegree 26 (Finset.range 13) C 2) →
      ComputesIncidence singerLines3 C)
    (exactTwo : ∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C →
      (HasLineDegree 26 (Finset.Ico 13 26) C 2 ∨ HasLineDegree 26 (Finset.range 13) C 2) →
      64 ≤ C.size) : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (1 : ℕ)) := by
  intro D good C hc
  classical
  exfalso
  let neg := fun (C : Circuit) => ∀ X : Finset (Fin 13),
      (∀ p ∉ X, ∃ l ∈ missLines singerLines3 X, p ∈ singerLines3 l) →
      (¬InNoLine singerLines3 X ∨ ¬InNoPencil singerLines3 (missLines singerLines3 X)) →
      C.eval (incidenceInput X (missLines singerLines3 X)) = false
  have eqI : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ ∃ d ∈ D, p = l+d := by decide
  have eqL (S : Finset (Fin 13)) (l : Fin 13) :
      l ∈ missLines singerLines3 S ↔ ∀ p ∈ S, ¬∃ d ∈ D, p = l+d := by
    change l ∈ Finset.univ.filter (fun k => Disjoint (singerLines3 k) S) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right,eqI]
  have input (P L : Finset (Fin 13)) : incidenceInput P L = List.ofFn (fun i : Fin (13+13) =>
      decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, i = Fin.natAdd 13 l)) := by
    rw [List.ofFn_add]
    unfold incidenceInput
    have cross : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide
    have rev : ∀ p l : Fin 13, Fin.natAdd 13 l ≠ Fin.castAdd 13 p := fun p l => (cross p l).symm
    have inj : ∀ k l : Fin 13, Fin.natAdd 13 k = Fin.natAdd 13 l ↔ k=l := by decide
    congr 1 <;> apply congrArg List.ofFn <;> funext i <;> apply decide_eq_decide.mpr
    · change i ∈ P ↔ (∃ p ∈ P, Fin.castAdd 13 i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, Fin.castAdd 13 i = Fin.natAdd 13 l
      simp only [cross,Fin.castAdd_inj]; simp
    · change i ∈ L ↔ (∃ p ∈ P, Fin.natAdd 13 i = Fin.castAdd 13 p) ∨ ∃ l ∈ L, Fin.natAdd 13 i = Fin.natAdd 13 l
      simp only [rev,inj]; simp
  have pos : RightOnIncidentPairs singerLines3 C := by
    intro l p pl
    rw [input]
    have h := hc.2.2.1 p l ((eqI p l).mp pl)
    change C.eval (List.ofFn _) = true at h
    simpa only [Finset.mem_singleton, exists_eq_left] using h
  have ns : neg C := by
    intro S maxS deg
    have m : ∀ p ∉ S, ∃ l : Fin 13, (∀ q ∈ S, ¬∃ d ∈ D, q=l+d) ∧ (∃ d ∈ D, p=l+d) := by
      intro p hp
      obtain ⟨l,hl,hp'⟩ := maxS p hp
      exact ⟨l,(eqL S l).mp hl,(eqI p l).mp hp'⟩
    have d : (∃ l : Fin 13, ∀ p ∈ S, ∃ t ∈ D, p=l+t) ∨
        ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ S, ¬∃ t ∈ D, q=l+t) → ∃ t ∈ D, p=l+t := by
      rcases deg with hn|hn
      · unfold InNoLine at hn
        push Not at hn
        obtain ⟨l,h⟩ := hn
        exact Or.inl ⟨l,fun p hp => (eqI p l).mp (h hp)⟩
      · unfold InNoPencil at hn
        push Not at hn
        obtain ⟨p,h⟩ := hn
        exact Or.inr ⟨p,fun l hl => (eqI p l).mp (h l ((eqL S l).mpr hl))⟩
    have h := hc.2.2.2 S m d
    rw [input]
    change C.eval (List.ofFn _) = false at h
    convert h using 2
    apply congrArg List.ofFn
    funext i
    apply decide_eq_decide.mpr
    simp only [eqL,and_comm]
  let score := fun (A : Circuit) => A.gates.countP (fun g => g.inputs.length == 2)
  let ok := fun (A : Circuit) => Monotone2 A ∧ A.size ≤ 63 ∧ RightOnIncidentPairs singerLines3 A ∧ neg A
  have start : ∃ k, ∃ A : Circuit, ok A ∧ score A = k := ⟨_,C,⟨hc.1,hc.2.1,pos,ns⟩,rfl⟩
  obtain ⟨A,ha,haEq⟩ := Nat.find_spec start
  by_cases thin : HasLineDegree 26 (Finset.Ico 13 26) A 2 ∨ HasLineDegree 26 (Finset.range 13) A 2
  · have low := exactTwo A ha.1 (thinSound A ha.1 ha.2.2.1 ha.2.2.2 thin) thin
    have high := ha.2.1
    omega
  · change ¬(A.lineDeg 26 (Finset.Ico 13 26) ≤ 2 ∨ A.lineDeg 26 (Finset.range 13) ≤ 2) at thin
    simp only [not_or,not_le] at thin
    obtain ⟨i,a,b,w,g,side,nw⟩ := safeFork A ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 thin.1 thin.2
    let B : Circuit := ⟨A.gates.set i ⟨.and,[w]⟩, A.output⟩
    obtain ⟨bm,be,bl,bp⟩ := bypass A i a b w g side ha.1
    have bpos : RightOnIncidentPairs singerLines3 B := fun l p hp => bp _ (ha.2.2.1 l p hp)
    have bok : ok B := ⟨bm,be.le.trans ha.2.1,bpos,nw⟩
    have hk := Nat.find_min' start (show ∃ A, ok A ∧ score A = score B from ⟨B,bok,rfl⟩)
    change score B < score A at bl
    omega
