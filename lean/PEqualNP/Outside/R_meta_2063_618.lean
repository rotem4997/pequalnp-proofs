import Mathlib
import PEqualNP.Defs

-- The equivalence of the raw Singer coordinates with the library presentation
-- follows the argument of WH3EL5 in R_meta_2063_42.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2063_618
    (extension : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
  ((PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 C ∧
    ∀ Q, PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
      C.eval (PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)) = false) ↔
    ∀ P T : Finset (Fin 13), (∀ l, (P ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2) →
      T.card ≤ 3 → (∀ p : Fin 13, (T.filter fun l => p ∈ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2) →
      C.eval (PEqualNP.GenericRejection.incidenceInput P T) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 P T))
    (gateFloor : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
  (∀ P T : Finset (Fin 13), (∀ l, (P ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2) →
    T.card ≤ 3 → (∀ p : Fin 13, (T.filter fun l => p ∈ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2) →
    C.eval (PEqualNP.GenericRejection.incidenceInput P T) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 P T) →
  39 ≤ C.size)
    (selection :
    let S := singerLines3
    let allowed := fun (P T : Finset (Fin 13)) => (∀ l, (P ∩ S l).card ≤ 2) ∧
      T.card ≤ 3 ∧ ∀ p : Fin 13, (T.filter fun l => p ∈ S l).card ≤ 2
    let valid := fun D : Circuit => Monotone2 D ∧ ReadsBack 26 D ∧
      ∀ P T, allowed P T → D.eval (incidenceInput P T) = incidenceFun S P T
    let inner := fun (D : Circuit) (i : ℕ) => (gateAt D i).op = .and ∧
      ∃ j, (gateAt D j).op = .and ∧ InCone 26 D i j
    ∀ C, valid C → 39 ≤ C.size → C.size < 64 → (∀ D, valid D → C.size ≤ D.size) → (∃ i, inner C i) →
      ∃ i, inner C i ∧ ∀ P T, allowed P T → incidenceFun S P T = false →
        (C.wires (incidenceInput P T)).getD (26+i) false = false) :
  have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → x5.size < (64 : ℕ) → (∀ (x10 x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size := by
  intro x1 x2 x3 x4 C mono back ok small dirty nested
  have geom : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ x1 (p-l) = true := by decide +kernel
  have isQ (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔ x2 Q := by
    have eq (l : Fin 13) : Q ∩ singerLines3 l = {p ∈ Q | x1 (p-l) = true} := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter]
      exact and_congr_right fun _ => geom p l
    change (_ ∧ ∀ l, (Q ∩ singerLines3 l).card ≤ 2) ↔
      (_ ∧ ∀ l, (Q.filter fun p => x1 (p-l) = true).card ≤ 2)
    simp only [eq]
  have rows (Q : Finset (Fin 13)) : incidenceInput Q (missLines singerLines3 Q) = x3 Q := by
    change List.ofFn _ ++ List.ofFn _ = List.ofFn _ ++ List.ofFn _
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p ∈ Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l ∈ (Finset.univ.filter fun w : Fin 13 => Disjoint (singerLines3 w) Q)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right]
    exact forall₂_congr fun p _ => by rw [geom]; simp
  let S := singerLines3
  let allowed := fun (P T : Finset (Fin 13)) => (∀ l, (P ∩ S l).card ≤ 2) ∧
      T.card ≤ 3 ∧ ∀ p : Fin 13, (T.filter fun l => p ∈ S l).card ≤ 2
  let valid := fun D : Circuit => Monotone2 D ∧ ReadsBack 26 D ∧
      ∀ P T, allowed P T → D.eval (incidenceInput P T) = incidenceFun S P T
  let inner := fun (D : Circuit) (i : ℕ) => (gateAt D i).op = .and ∧
      ∃ j, (gateAt D j).op = .and ∧ InCone 26 D i j
  have bridge (D : Circuit) (hm : Monotone2 D) : x4 D ↔
      ∀ P T, allowed P T → D.eval (incidenceInput P T) = incidenceFun S P T := by
    constructor
    · intro test P T good
      apply ((extension D hm).mp ?_) P T good.1 good.2.1 good.2.2
      constructor
      · intro l p hp
        change D.eval ((List.ofFn fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
          List.ofFn fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) = true
        simpa only [Finset.mem_singleton] using test.1 p l ((geom p l).mp hp)
      · intro Q hQ
        rw [rows]
        exact test.2 Q ((isQ Q).mp hQ)
    · intro table
      obtain ⟨on,off⟩ := (extension D hm).mpr (fun P T a b c => table P T ⟨a,b,c⟩)
      constructor
      · intro p l hp
        have hit := on l p ((geom p l).mpr hp)
        change D.eval ((List.ofFn fun a : Fin 13 => decide (a ∈ ({p} : Finset (Fin 13)))) ++
          List.ofFn fun b : Fin 13 => decide (b ∈ ({l} : Finset (Fin 13)))) = true at hit
        simpa only [Finset.mem_singleton] using hit
      · intro Q hq
        rw [←rows]
        exact off Q ((isQ Q).mpr hq)
  have original : valid C := ⟨mono,back,(bridge C mono).mp ok⟩
  have counted : 39 ≤ C.size := gateFloor C mono (fun P T a b c => original.2.2 P T ⟨a,b,c⟩)
  by_contra noSmaller
  have least (D : Circuit) (hd : valid D) : C.size ≤ D.size := by
    by_contra! reduced
    exact noSmaller ⟨D,hd.1,hd.2.1,(bridge D hd.1).mpr hd.2.2,reduced⟩
  obtain ⟨a,b,aa,ab,path⟩ := nested
  obtain ⟨i,hi,safe⟩ := selection C original counted small least ⟨a,aa,b,ab,path⟩
  obtain ⟨ai,j,aj,runs⟩ := hi
  obtain ⟨Q,hq,fire⟩ := dirty i j ai aj runs
  have quad := (isQ Q).mpr hq
  have exterior : ∀ A : Finset (Fin 13), IsQuadrangle singerLines3 A →
      (missLines singerLines3 A).card ≤ 3 ∧ ∀ p : Fin 13,
        ((missLines singerLines3 A).filter fun l => p ∈ singerLines3 l).card ≤ 2 := by decide +kernel
  have miss : incidenceFun S Q (missLines S Q) = false := by
    apply decide_eq_false
    rintro ⟨p,hp,l,hl,on⟩
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp hl).2 on hp
  have bad := safe Q (missLines S Q) ⟨quad.2,exterior Q quad⟩ miss
  change (C.wires (incidenceInput Q (missLines singerLines3 Q))).getD (26+i) false = false at bad
  rw [rows] at bad
  exact Bool.noConfusion (fire.symm.trans bad)
