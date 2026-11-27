import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

-- Without nested AND gates, every accepting wire has a witness on at most two inputs.
-- Two such witnesses conflict precisely when their union extends to a quadrangle support.
theorem PEqualNP.Outside.R_meta_5260_3
  (sparse : let V := fun (C : Circuit) (r : ℕ) (U : Finset (Fin 13 ⊕ Fin 13)) =>
      (C.wires (incidenceInput U.toLeft U.toRight)).getD r false
    let flat := fun (C : Circuit) => ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧
      (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
    ∀ C, Monotone2 C → ReadsBack 26 C → flat C → ∀ r X,
    V C r X = true ↔ ∃ U ⊆ X, U.card ≤ 2 ∧ V C r U = true)
  (extension : let P := singerLines3
    let ok := fun (U : Finset (Fin 13 ⊕ Fin 13)) => IsFree (incidences P) U ∧
      U.toRight.card ≤ 3 ∧ (∀ l, (U.toLeft ∩ P l).card ≤ 2) ∧
      ∀ p, (U.toRight.filter fun l => p ∈ P l).card ≤ 2
    ∀ U, U.card ≤ 4 → (ok U ↔ ∃ Q, IsQuadrangle P Q ∧ U ⊆ supp P Q))
  (bound : let P := singerLines3
    let ok := fun (U : Finset (Fin 13 ⊕ Fin 13)) => IsFree (incidences P) U ∧
      U.toRight.card ≤ 3 ∧ (∀ l, (U.toLeft ∩ P l).card ≤ 2) ∧
      ∀ p, (U.toRight.filter fun l => p ∈ P l).card ≤ 2
    let V := fun (C : Circuit) (r : ℕ) (U : Finset (Fin 13 ⊕ Fin 13)) =>
      (C.wires (incidenceInput U.toLeft U.toRight)).getD r false
    let flat := fun (C : Circuit) => ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧
      (gateAt C j).op = GateOp.and ∧ InCone 26 C i j
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C → flat C →
    (∀ p l, p ∈ P l → let U : Finset (Fin 13 ⊕ Fin 13) := {Sum.inl p, Sum.inr l}; (V C a U && V C b U) = true) →
    (∀ U W, U.card ≤ 2 → W.card ≤ 2 → ok (U ∪ W) → (V C a U && V C b W) = false) →
    (∀ r ∈ [a,b], ∃ U, U.card ≤ 2 ∧ ok U ∧ V C r U = true) → 63 ≤ C.size)
  : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   (PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9)) → (¬∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11) → (63 : ℕ) ≤ x5.size := by
  dsimp only at sparse extension bound ⊢
  intro C a b valid flatC
  obtain ⟨mono,back,pos,neg,first,second⟩ := valid
  have mem_inc : ∀ q l : Fin 13, q ∈ PEqualNP.HeptadCover.singerLines3 l ↔ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    intro q l
    delta PEqualNP.HeptadCover.singerLines3
    simp [← Fin.val_eq_val, Fin.val_sub]
    constructor <;> intro h <;> rcases h with (h | h | h | h) <;> omega
  have card_inc : ∀ (S : Finset (Fin 13)) (c : Fin 13),
      (S ∩ PEqualNP.HeptadCover.singerLines3 c).card = {q ∈ S | q - c ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card := by
    intro S c
    congr 1
    ext q
    simp [mem_inc]
  have hI : ∀ p l : Fin 13, ((List.ofFn fun q : Fin 13 => decide (q ∈ (({p} : Finset (Fin 13))))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (({l} : Finset (Fin 13)))))) = ((List.ofFn fun q : Fin 13 => decide (q = p)) ++ (List.ofFn fun q : Fin 13 => decide (q = l))) := by
    intro p l
    simp
  have hM : ∀ S : Finset (Fin 13),
      ((List.ofFn fun q : Fin 13 => decide (q ∈ (S))) ++ (List.ofFn fun q : Fin 13 => decide (q ∈ (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 S)))) = ((List.ofFn fun q : Fin 13 => decide (q ∈ S)) ++
        (List.ofFn fun l : Fin 13 => decide ((∀ q ∈ S, q - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)))))) := by
    intro S
    delta PEqualNP.HeptadCover.missLines
    simp [Finset.disjoint_right, mem_inc]
  have hQ : ∀ S : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 S ↔
      (S.card = 4 ∧ ∀ c : Fin 13, {q ∈ S | q - c ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card ≤ 2) := by
    intro S
    constructor
    · intro h
      obtain ⟨h1, h2⟩ : S.card = 4 ∧ ∀ l : Fin 13, (S ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2 := h
      exact ⟨h1, fun c => by rw [← card_inc]; exact h2 c⟩
    · rintro ⟨h1, h2⟩
      show S.card = 4 ∧ ∀ l : Fin 13, (S ∩ PEqualNP.HeptadCover.singerLines3 l).card ≤ 2
      exact ⟨h1, fun c => by rw [card_inc]; exact h2 c⟩
  let V := fun (r : ℕ) (U : Finset (Fin 13 ⊕ Fin 13)) => (C.wires (incidenceInput U.toLeft U.toRight)).getD r false
  let P := singerLines3
  let ok := fun (U : Finset (Fin 13 ⊕ Fin 13)) => IsFree (incidences P) U ∧
      U.toRight.card ≤ 3 ∧ (∀ l, (U.toLeft ∩ P l).card ≤ 2) ∧
      ∀ p, (U.toRight.filter fun l => p ∈ P l).card ≤ 2
  have onQ (Q) (h : IsQuadrangle P Q) : (V a (supp P Q) && V b (supp P Q)) = false := by
    have n := neg Q ((hQ Q).mp h)
    dsimp only [V, P, supp, incidenceInput]
    simpa only [Finset.toLeft_disjSum, Finset.toRight_disjSum, hM] using n
  have active (r : ℕ) (Q : Finset (Fin 13)) (h : IsQuadrangle P Q) (on : V r (supp P Q) = true) :
      ∃ U, U.card ≤ 2 ∧ ok U ∧ V r U = true := by
    obtain ⟨U,sub,small,yes⟩ := (sparse C mono back flatC r (supp P Q)).mp on
    exact ⟨U,small,(extension U (by omega)).mpr ⟨Q,h,sub⟩,yes⟩
  apply bound C a b mono back flatC
  · intro p l inc
    have answer := pos p l ((mem_inc p l).mp inc)
    have pair : ({Sum.inl p, Sum.inr l} : Finset (Fin 13 ⊕ Fin 13)) = ({p} : Finset (Fin 13)).disjSum {l} := by
      ext u
      cases u <;> simp
    rw [pair]
    dsimp only [incidenceInput]
    simpa only [Finset.toLeft_disjSum, Finset.toRight_disjSum, hI] using answer
  · intro U W hu hw compatible
    have small := Finset.card_union_le U W
    obtain ⟨Q,hQ',inside⟩ := (extension (U ∪ W) (by omega)).mp compatible
    change (V a U && V b W) = false
    cases ha : V a U <;> cases hb : V b W <;> try rfl
    have qa := (sparse C mono back flatC a (supp P Q)).mpr ⟨U,Finset.Subset.trans Finset.subset_union_left inside,hu,ha⟩
    have qb := (sparse C mono back flatC b (supp P Q)).mpr ⟨W,Finset.Subset.trans Finset.subset_union_right inside,hw,hb⟩
    have no := onQ Q hQ'
    change V a (supp P Q) = true at qa
    change V b (supp P Q) = true at qb
    rw [qa,qb] at no
    exact no
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨Q,hQ',ineq⟩ := second
      apply active _ Q ((hQ Q).mpr hQ')
      have yes := (Bool.lt_iff.mp ineq).2
      dsimp only [V, P, supp, incidenceInput]
      simpa only [Finset.toLeft_disjSum, Finset.toRight_disjSum, hM] using yes
    · obtain ⟨Q,hQ',ineq⟩ := first
      apply active _ Q ((hQ Q).mpr hQ')
      have yes := (Bool.lt_iff.mp ineq).2
      dsimp only [V, P, supp, incidenceInput]
      simpa only [Finset.toLeft_disjSum, Finset.toRight_disjSum, hM] using yes
