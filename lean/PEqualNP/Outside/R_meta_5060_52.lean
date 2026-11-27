import PEqualNP.Defs

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- On a rejected input, either operand may be selected at an AND whose operands agree.
-- Distinct independent inputs whose union contains an edge require disjoint sets of selections.
-- The ten-vertex family forces at least 430 inputs on which fifteen gates have unequal operands.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5060_52
    (geometry : let G := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
      ∀ C : AndCountCircuit 42, C.Computes G →
        ∃ F : Finset (Finset (Fin 42)), 16800 ≤ F.card ∧
          (∀ U ∈ F, U.card = 10 ∧ C.eval U = false) ∧
          ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true)
    (remaining : let G := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
      ∀ C : AndCountCircuit 42, C.WellFormed → C.Computes G →
      (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) → C.size = 19 →
      (∀ v, {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ 3) →
      (∀ p l : Fin 42, p.val < 21 → 21 ≤ l.val → ¬G.Adj p l →
        {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
          l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard ≤ 5) →
      (∃ F : Finset (Finset (Fin 42)), 430 ≤ F.card ∧
        (∀ U ∈ F, U.card = 10 ∧ C.eval U = false ∧
          {i : Fin C.size |
            sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) =
            sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)}.ncard ≤ 4) ∧
        ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true) → False) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (19 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (3 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (5 : ℕ)) → False := by
  intro G C wf comp _ _ disjoint size reads nonedge
  have sideEq {n k} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (v : Fin k → Bool) :
      sideTrue U B F i v = decide ((∃ u ∈ B, u ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl

  have outEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) :
      C.eval U = decide ((∃ u ∈ C.outVars, u ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := rfl

  have fuelEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (a : Nat) (i : Fin C.size) :
      C.gateValFuel U (a+1) i =
        (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U a) &&
         sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U a)) := rfl

  let wing {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) (b : Bool) :=
    sideTrue U (if b then C.rightVars i else C.leftVars i)
      (if b then C.rightGates i else C.leftGates i) i (C.gateVal U)

  have stable {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
      (a b : Nat) (ha : i.val < a) (hb : i.val < b) :
      C.gateValFuel U a i = C.gateValFuel U b i := by
    induction a generalizing i b with
    | zero => omega
    | succ a ih =>
      cases b with
      | zero => omega
      | succ b =>
        have eq (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
            sideTrue U B F i (C.gateValFuel U a) = sideTrue U B F i (C.gateValFuel U b) := by
          rw [sideEq,sideEq]
          congr 1
          apply propext
          constructor <;> rintro (raw | ⟨j,hj,lt,val⟩)
          · exact Or.inl raw
          · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
            exact Or.inr ⟨j,hj,lt,h ▸ val⟩
          · exact Or.inl raw
          · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
            exact Or.inr ⟨j,hj,lt,h.symm ▸ val⟩
        rw [fuelEq,fuelEq,eq,eq]

  have value {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
      C.gateVal U i = (wing C U i false && wing C U i true) :=
    stable C U i C.size (C.size+1) i.isLt (by omega)

  have unionChoice {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (q : Fin C.size → Bool)
      (goodU : ∀ i, wing C U i (q i) = C.gateVal U i)
      (goodV : ∀ i, wing C V i (q i) = C.gateVal V i) :
      C.eval (U ∪ V) = true → C.eval U = true ∨ C.eval V = true := by
    have gates (d : Nat) : ∀ i : Fin C.size, C.gateValFuel (U ∪ V) d i = true →
        C.gateVal U i = true ∨ C.gateVal V i = true := by
      induction d with
      | zero => intro i h; cases h
      | succ d ih =>
        intro i h
        have both := Bool.and_eq_true_iff.mp h
        have pick : sideTrue (U ∪ V) (if q i then C.rightVars i else C.leftVars i)
            (if q i then C.rightGates i else C.leftGates i) i (C.gateValFuel (U ∪ V) d) = true := by
          cases q i
          · exact both.1
          · exact both.2
        rw [← goodU i, ← goodV i]
        simp only [wing,sideEq,decide_eq_true_eq] at pick ⊢
        rcases pick with ⟨v,hv,hmem⟩ | ⟨j,hj,hlt,on⟩
        · rcases Finset.mem_union.mp hmem with h | h
          · exact Or.inl (Or.inl ⟨v,hv,h⟩)
          · exact Or.inr (Or.inl ⟨v,hv,h⟩)
        · rcases ih j on with h | h
          · exact Or.inl (Or.inr ⟨j,hj,hlt,h⟩)
          · exact Or.inr (Or.inr ⟨j,hj,hlt,h⟩)
    simp only [outEq,decide_eq_true_eq]
    rintro (⟨v,hv,vhit⟩|⟨i,hi,hit⟩)
    · rcases Finset.mem_union.mp vhit with h | h
      · exact Or.inl (Or.inl ⟨v,hv,h⟩)
      · exact Or.inr (Or.inl ⟨v,hv,h⟩)
    · rcases gates C.size i hit with h | h
      · exact Or.inl (Or.inr ⟨i,hi,h⟩)
      · exact Or.inr (Or.inr ⟨i,hi,h⟩)

  let free {n} (C : AndCountCircuit n) (U : Finset (Fin n)) : Finset (Fin C.size) :=
    Finset.univ.filter fun i => wing C U i false = wing C U i true

  let encode {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size)) :
      Fin C.size → Bool := fun i => if i ∈ free C U then decide (i ∈ s) else wing C U i false

  have good {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size))
      (i : Fin C.size) : wing C U i (encode C U s i) = C.gateVal U i := by
    rw [value]
    simp only [encode,free,Finset.mem_filter,Finset.mem_univ,true_and]
    cases h : wing C U i false <;> cases h' : wing C U i true <;> by_cases hs : i ∈ s <;> simp [h,h',hs]

  have packing {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
      (neg : ∀ U ∈ F, C.eval U = false)
      (pos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true) :
      (∑ U ∈ F, 2 ^ (free C U).card) ≤ 2 ^ C.size := by
    classical
    let cubes := fun U => (free C U).powerset.image (encode C U)
    have card (U : Finset (Fin n)) : (cubes U).card = 2^(free C U).card := by
      unfold cubes
      rw [Finset.card_image_iff.mpr ?_, Finset.card_powerset]
      intro s hs t ht eq
      have ssub := Finset.mem_powerset.mp hs
      have tsub := Finset.mem_powerset.mp ht
      ext i
      by_cases hi : i ∈ free C U
      · have he := congrFun eq i
        simpa only [encode,ite_eq_left hi,decide_eq_decide] using he
      · exact iff_of_false (fun h => hi (ssub h)) (fun h => hi (tsub h))
    have dis : (F : Set (Finset (Fin n))).PairwiseDisjoint cubes := by
      intro U hu V hv ne
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hq
      obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hq'
      have both := unionChoice C U V q (hs ▸ good C U s) (ht ▸ good C V t) (pos U hu V hv ne)
      simp only [neg U hu,neg V hv, Bool.false_eq_true,or_self] at both
    calc
      _ = ∑ U ∈ F, (cubes U).card := by simp_rw [card]
      _ = (F.biUnion cubes).card := (Finset.card_biUnion dis).symm
      _ ≤ Fintype.card (Fin C.size → Bool) := Finset.card_le_univ _
      _ = _ := by simp

  have pressure {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
      (neg : ∀ U ∈ F, C.eval U = false)
      (pos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true)
      (size : C.size = 19) (big : 16800 ≤ F.card) :
      430 ≤ (F.filter fun U => (free C U).card ≤ 4).card := by
    classical
    let K := F.filter fun U => (free C U).card ≤ 4
    let T := F \ K
    let cost := fun U => 2^(free C U).card
    have sub : K ⊆ F := Finset.filter_subset _ _
    have tcard : T.card = F.card - K.card := Finset.card_sdiff_of_subset sub
    have kt : Disjoint K T := Finset.disjoint_sdiff
    have union : K ∪ T = F := Finset.union_sdiff_of_subset sub
    have low : K.card ≤ ∑ U ∈ K, cost U := by
      calc
        _ = ∑ _U ∈ K, (1 : Nat) := by simp
        _ ≤ _ := Finset.sum_le_sum fun U _ => Nat.one_le_pow _ _ (by decide)
    have high : T.card * 32 ≤ ∑ U ∈ T, cost U := by
      calc
        _ = ∑ _U ∈ T, (32 : Nat) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro U hu
          obtain ⟨inF,out⟩ := Finset.mem_sdiff.mp hu
          have gt : 4 < (free C U).card := by
            by_contra! h
            exact out (Finset.mem_filter.mpr ⟨inF,h⟩)
          exact Nat.pow_le_pow_right (by decide : 0 < 2) gt
    have both := Nat.add_le_add low high
    rw [← Finset.sum_union kt,union] at both
    have cap := packing C F neg pos
    change (∑ U ∈ F, cost U) ≤ 2^C.size at cap
    rw [size] at cap
    change (∑ U ∈ F, cost U) ≤ 524288 at cap
    have kc := Finset.card_le_card sub
    change 430 ≤ K.card
    omega
  obtain ⟨F,big,shape,pos⟩ := geometry C comp
  have neg : ∀ U ∈ F, C.eval U = false := fun U hu => (shape U hu).2
  refine remaining C wf comp disjoint size reads nonedge
    ⟨F.filter (fun U => (free C U).card ≤ 4), pressure C F neg pos size big,?_,
      fun U hu V hv => pos U (Finset.mem_filter.mp hu).1 V (Finset.mem_filter.mp hv).1⟩
  intro U hu
  obtain ⟨mem,small⟩ := Finset.mem_filter.mp hu
  refine ⟨(shape U mem).1,neg U mem,?_⟩
  have eq : {i : Fin C.size | wing C U i false = wing C U i true} = (free C U : Set (Fin C.size)) := by
    ext i
    simp only [free,Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
  change {i : Fin C.size | wing C U i false = wing C U i true}.ncard ≤ 4
  rwa [eq,Set.ncard_coe_finset]
