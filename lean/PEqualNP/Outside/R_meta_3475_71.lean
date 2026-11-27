import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3475_71
    (coverBudget : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) (C : Circuit) (E : Finset (Fin n × Fin n)),
      2 ≤ q → (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      PEqualNP.TopForm.IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      E.Nonempty →
      (∀ e ∈ E, circuitFun (n+n) C (fun i => decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2)) = true) →
      (∀ e ∈ E, 1 < (E.filter (fun f => f.1 = e.1)).card ∧ 1 < (E.filter (fun f => f.2 = e.2)).card) →
      ∃ P L : Finset (Fin n), P ⊆ E.image Prod.fst ∧ L ⊆ E.image Prod.snd ∧
        (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) ∧
        P.card + L.card ≤ min (E.image Prod.fst).card (E.image Prod.snd).card ∧
        (E.image Prod.fst).card + (E.image Prod.snd).card + P.card + L.card ≤ C.size + 1)
    (largeBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 → 13538 ≤ x5.size →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →               let x13 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2;               (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) → (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) → (¬ ∃ P L : Finset (Fin x2), P ⊆ x6.image Prod.fst ∧ L ⊆ x6.image Prod.snd ∧ (∀ e ∈ x6, e.1 ∈ P ∨ e.2 ∈ L) ∧ P.card + L.card ≤ 4512) → x6.card ≤ (24 : ℕ) * x5.size) : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →               let x13 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2;               (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) → (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) → x6.card ≤ (24 : ℕ) * x5.size := by
  classical
  have smallDegree (d : ℕ) : 94 * d ≤ 2256 + (d * d - d) := by
    have dd : d ≤ d * d := by
      cases d
      · simp
      · nlinarith
    zify [dd]
    rcases (show (d : ℤ) ≤ 47 ∨ 48 ≤ (d : ℤ) by omega) with hd | hd
    · nlinarith [mul_nonneg (show 0 ≤ (47 : ℤ) - d by omega)
        (show 0 ≤ (48 : ℤ) - d by omega)]
    · nlinarith [mul_nonneg (show 0 ≤ (d : ℤ) - 47 by omega)
        (show 0 ≤ (d : ℤ) - 48 by omega)]

  have weighted (A B : Type) [Fintype A] [Fintype B] (J : A → B → Prop) [DecidableRel J]
      (unique : ∀ (a a' : A) (b b' : B), a ≠ a' →
        J a b → J a' b → J a b' → J a' b' → b = b') :
      94 * Fintype.card {e : A × B // J e.1 e.2} ≤
        2256 * Fintype.card B + Fintype.card A * (Fintype.card A - 1) := by
    classical
    let neighbors (b : B) : Finset A := Finset.univ.filter (fun a => J a b)
    let attach (b : B) : A ↪ A × B := ⟨fun a => (a, b), fun _ _ h => congrArg Prod.fst h⟩
    let tagged (b : B) := (neighbors b).map (attach b)
    have memNeighbors (a : A) (b : B) : a ∈ neighbors b ↔ J a b := by simp [neighbors]
    have memTagged (e : A × B) (b : B) : e ∈ tagged b ↔ J e.1 b ∧ e.2 = b := by
      constructor
      · rintro h
        obtain ⟨a, ha, eqa⟩ := Finset.mem_map.mp h
        change (a, b) = e at eqa
        rw [← eqa]
        exact ⟨(memNeighbors a b).mp ha, rfl⟩
      · rintro ⟨hJ, eqb⟩
        refine Finset.mem_map.mpr ⟨e.1, (memNeighbors e.1 b).mpr hJ, ?_⟩
        change (e.1, b) = e
        rw [← eqb]
    have tagDisjoint : ((Finset.univ : Finset B) : Set B).PairwiseDisjoint tagged := by
      intro b _ b' _ different
      apply Finset.disjoint_left.mpr
      intro e hb hb'
      exact different (((memTagged e b).mp hb).2.symm.trans ((memTagged e b').mp hb').2)
    have allEdges : ((Finset.univ : Finset B).biUnion tagged) =
        (Finset.univ : Finset (A × B)).filter (fun e => J e.1 e.2) := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, memTagged]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact hb
      · intro he
        exact ⟨e.2, he, rfl⟩
    have edgeCount : Fintype.card {e : A × B // J e.1 e.2} = ∑ b : B, (neighbors b).card := by
      rw [Fintype.card_subtype, ← allEdges, Finset.card_biUnion tagDisjoint]
      simp only [tagged, Finset.card_map]
    have pairDisjoint : ((Finset.univ : Finset B) : Set B).PairwiseDisjoint
        (fun b => (neighbors b).offDiag) := by
      intro b _ b' _ different
      apply Finset.disjoint_left.mpr
      intro e he he'
      obtain ⟨ha, ha', hne⟩ := Finset.mem_offDiag.mp he
      obtain ⟨hb, hb', _⟩ := Finset.mem_offDiag.mp he'
      exact different (unique _ _ b b' hne ((memNeighbors _ _).mp ha) ((memNeighbors _ _).mp ha')
        ((memNeighbors _ _).mp hb) ((memNeighbors _ _).mp hb'))
    have pairCount : (∑ b : B, (neighbors b).offDiag.card) ≤
        Fintype.card A * Fintype.card A - Fintype.card A := by
      have contained : (Finset.univ : Finset B).biUnion (fun b => (neighbors b).offDiag) ⊆
          (Finset.univ : Finset A).offDiag := by
        intro e he
        obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
          (Finset.mem_offDiag.mp hb).2.2⟩
      have cardLe := Finset.card_le_card contained
      simpa only [Finset.card_biUnion pairDisjoint, Finset.offDiag_card, Finset.card_univ] using cardLe
    have sumDegree : (∑ b : B, 94 * (neighbors b).card) ≤
        ∑ b : B, (2256 + (neighbors b).offDiag.card) := by
      apply Finset.sum_le_sum
      intro b _
      rw [Finset.offDiag_card]
      exact smallDegree (neighbors b).card
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at sumDegree
    change 94 * (∑ b : B, (neighbors b).card) ≤
      Fintype.card B * 2256 + ∑ b : B, (neighbors b).offDiag.card at sumDegree
    rw [edgeCount]
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega


  have swapUnique {α β : Type} {J : α → β → Prop}
      (unique : ∀ a a' b b', a ≠ a' → J a b → J a' b → J a b' → J a' b' → b = b') :
      ∀ b b' a a', b ≠ b' → J a b → J a b' → J a' b → J a' b' → a = a' := by
    intro b b' a a' hb h₁ h₂ h₃ h₄
    by_contra ha
    exact hb (unique a a' b b' ha h₁ h₃ h₂ h₄)

  have weightedSplit {α β : Type} [DecidableEq α] [DecidableEq β]
      (E : Finset (α × β)) (A P : Finset α) (B L : Finset β)
      (ha : ∀ e ∈ E, e.1 ∈ A) (hb : ∀ e ∈ E, e.2 ∈ B) (subP : P ⊆ A)
      (cover : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L)
      (unique : ∀ (a a' : α) (b b' : β), a ≠ a' →
        (a,b) ∈ E → (a',b) ∈ E → (a,b') ∈ E → (a',b') ∈ E → b = b') :
      94 * E.card ≤ 2256 * (A.card + B.card - P.card) +
        P.card * (P.card - 1) + L.card * (L.card - 1) := by
    let left := E.filter (fun e => e.1 ∈ P)
    let right := E.filter (fun e => e.1 ∉ P)
    let E₁ (a : ↥P) (b : ↥B) := (a.val,b.val) ∈ E
    let E₂ (b : ↥L) (a : ↥(A \ P)) := (a.val,b.val) ∈ E
    have uniqueness1 : ∀ a a' b b', a ≠ a' → E₁ a b → E₁ a' b → E₁ a b' → E₁ a' b' → b = b' := by
      intro a a' b b' ne ea ea' eb eb'
      exact Subtype.ext (unique _ _ _ _ (fun eq => ne (Subtype.ext eq)) ea ea' eb eb')
    have uniqueness2 : ∀ a a' b b', a ≠ a' → E₂ a b → E₂ a' b → E₂ a b' → E₂ a' b' → b = b' := by
      intro a a' b b' ne ea ea' eb eb'
      exact Subtype.ext (swapUnique unique _ _ _ _ (fun eq => ne (Subtype.ext eq)) ea ea' eb eb')
    let pack1 (e : ↥left) : {r : ↥P × ↥B // E₁ r.1 r.2} :=
      ⟨(⟨e.val.1,(Finset.mem_filter.mp e.property).2⟩,
        ⟨e.val.2,hb _ (Finset.mem_filter.mp e.property).1⟩),
        (Finset.mem_filter.mp e.property).1⟩
    let pack2 (e : ↥right) : {r : ↥L × ↥(A \ P) // E₂ r.1 r.2} :=
      ⟨(⟨e.val.2,(cover _ (Finset.mem_filter.mp e.property).1).resolve_left
          (Finset.mem_filter.mp e.property).2⟩,
        ⟨e.val.1,Finset.mem_sdiff.mpr ⟨ha _ (Finset.mem_filter.mp e.property).1,
          (Finset.mem_filter.mp e.property).2⟩⟩),
        (Finset.mem_filter.mp e.property).1⟩
    have bound1 := Fintype.card_le_of_injective pack1 (fun e e' eq => by
      apply Subtype.ext
      exact congrArg (fun x => (x.val.1.val,x.val.2.val)) eq)
    have bound2 := Fintype.card_le_of_injective pack2 (fun e e' eq => by
      apply Subtype.ext
      exact congrArg (fun x => (x.val.2.val,x.val.1.val)) eq)
    have weight1 := weighted ↥P ↥B E₁ uniqueness1
    have weight2 := weighted ↥L ↥(A \ P) E₂ uniqueness2
    simp only [Fintype.card_coe] at bound1 bound2 weight1 weight2
    have split : left.card + right.card = E.card := Finset.card_filter_add_card_filter_not _
    have size : (A \ P).card = A.card - P.card := Finset.card_sdiff_of_subset subP
    have lePA := Finset.card_le_card subP
    omega

  have pairTerm (x y : ℕ) (hyx : y ≤ x) (hcap : x+y ≤ 4512) :
      x*(x-1) + y*(y-1) ≤ 2256*(2*x+y-1) := by
    calc
      _ ≤ (x+y)*(x-1) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      _ ≤ 4512*(x-1) := Nat.mul_le_mul_right _ hcap
      _ ≤ _ := by omega

  have coverCount {α β : Type} [DecidableEq α] [DecidableEq β]
      (E : Finset (α × β)) (A P : Finset α) (B L : Finset β)
      (ha : ∀ e ∈ E, e.1 ∈ A) (hb : ∀ e ∈ E, e.2 ∈ B) (subP : P ⊆ A) (subL : L ⊆ B)
      (cover : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L)
      (unique : ∀ (a a' : α) (b b' : β), a ≠ a' →
        (a,b) ∈ E → (a',b) ∈ E → (a,b') ∈ E → (a',b') ∈ E → b = b')
      (cap : P.card + L.card ≤ 4512) :
      E.card ≤ 24 * (A.card + B.card + P.card + L.card - 1) := by
    by_cases empty : E = ∅
    · simp [empty]
    have coverPos : 0 < P.card + L.card := by
      obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      rcases cover e he with h | h <;>
        have := Finset.card_pos.mpr ⟨_,h⟩ <;> omega
    by_cases order : L.card ≤ P.card
    · have weight := weightedSplit E A P B L ha hb subP cover unique
      have charge := pairTerm P.card L.card order cap
      have sz := Finset.card_le_card subP
      omega
    let E' := E.image Prod.swap
    have edgeSwap (a : α) (b : β) : (b,a) ∈ E' ↔ (a,b) ∈ E := by
      simp [E', Finset.mem_image, Prod.ext_iff]
    have actB (e : β × α) (he : e ∈ E') : e.1 ∈ B := hb _ ((edgeSwap e.2 e.1).mp (by simpa using he))
    have actA (e : β × α) (he : e ∈ E') : e.2 ∈ A := ha _ ((edgeSwap e.2 e.1).mp (by simpa using he))
    have covers' (e : β × α) (he : e ∈ E') : e.1 ∈ L ∨ e.2 ∈ P :=
      (cover _ ((edgeSwap e.2 e.1).mp (by simpa using he))).symm
    have no4 (b b' : β) (a a' : α) (ne : b ≠ b')
        (h₁ : (b,a) ∈ E') (h₂ : (b',a) ∈ E') (h₃ : (b,a') ∈ E') (h₄ : (b',a') ∈ E') : a = a' :=
      swapUnique unique _ _ _ _ ne ((edgeSwap _ _).mp h₁) ((edgeSwap _ _).mp h₂)
        ((edgeSwap _ _).mp h₃) ((edgeSwap _ _).mp h₄)
    have eqSize : E'.card = E.card := Finset.card_image_of_injective E Prod.swap_injective
    have weight := weightedSplit E' B L A P actB actA subL covers' no4
    have charge := pairTerm L.card P.card (by omega) (by omega)
    have sz := Finset.card_le_card subL
    omega

  intro q n I inst C E hq hn lines uniq model sound
  dsimp only
  intro accepts deg
  by_cases none : E = ∅
  · simp [none]
  have nePins (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro eq
    have vals := congrArg Fin.val eq
    change p.val = n + l.val at vals
    have := p.isLt
    omega
  have positive (e : Fin n × Fin n) (he : e ∈ E) :
      circuitFun (n+n) C (fun i => decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2)) =
        true := (accepts e he).2.1
  have degrees (e : Fin n × Fin n) (he : e ∈ E) :
      1 < (E.filter (fun f => f.1 = e.1)).card ∧ 1 < (E.filter (fun f => f.2 = e.2)).card := by
    have points (p : Fin n) :
        E.filter (fun f => Fin.castAdd n p = Fin.castAdd n f.1 ∨
          Fin.castAdd n p = Fin.natAdd n f.2) = E.filter (fun f => f.1 = p) := by
      apply Finset.filter_congr
      intro f _
      constructor
      · intro h
        exact h.elim (fun eq => ((Fin.castAddEmb n).injective eq).symm)
          (fun eq => (nePins p f.2 eq).elim)
      · intro h
        exact Or.inl (congrArg (Fin.castAdd n) h.symm)
    have lines' (l : Fin n) :
        E.filter (fun f => Fin.natAdd n l = Fin.castAdd n f.1 ∨
          Fin.natAdd n l = Fin.natAdd n f.2) = E.filter (fun f => f.2 = l) := by
      apply Finset.filter_congr
      intro f _
      constructor
      · intro h
        exact h.elim (fun eq => (nePins f.1 l eq.symm).elim)
          (fun eq => ((Fin.natAddEmb n).injective eq).symm)
      · intro h
        exact Or.inr (congrArg (Fin.natAdd n) h.symm)
    have pdeg := deg e he (Fin.castAdd n e.1) (Or.inl rfl)
    have ldeg := deg e he (Fin.natAdd n e.2) (Or.inr rfl)
    change 24 < (E.filter (fun f => Fin.castAdd n e.1 = Fin.castAdd n f.1 ∨
      Fin.castAdd n e.1 = Fin.natAdd n f.2)).card at pdeg
    change 24 < (E.filter (fun f => Fin.natAdd n e.2 = Fin.castAdd n f.1 ∨
      Fin.natAdd n e.2 = Fin.natAdd n f.2)).card at ldeg
    rw [points] at pdeg
    rw [lines'] at ldeg
    exact ⟨by omega,by omega⟩
  obtain ⟨P,L,subP,subL,cover,balance,budget⟩ :=
    coverBudget q n I C E (by omega) uniq model sound
      (Finset.nonempty_iff_ne_empty.mpr none) positive degrees
  have minP := (le_min_iff.mp balance).1
  have minL := (le_min_iff.mp balance).2
  have no4 (a a' b b' : Fin n) (ne : a ≠ a')
      (h₁ : (a,b) ∈ E) (h₂ : (a',b) ∈ E) (h₃ : (a,b') ∈ E) (h₄ : (a',b') ∈ E) : b = b' := by
    obtain ⟨c,_,only⟩ := uniq a a' ne
    exact (only b ⟨(accepts (a,b) h₁).1,(accepts (a',b) h₂).1⟩).trans
      (only b' ⟨(accepts (a,b') h₃).1,(accepts (a',b') h₄).1⟩).symm
  have counting (U V : Finset (Fin n)) (hU : U ⊆ E.image Prod.fst)
      (hV : V ⊆ E.image Prod.snd) (hits : ∀ e ∈ E, e.1 ∈ U ∨ e.2 ∈ V)
      (cap : U.card + V.card ≤ 4512)
      (fits : (E.image Prod.fst).card + (E.image Prod.snd).card + U.card + V.card ≤ C.size + 1) :
      E.card ≤ 24 * C.size := by
    have bound := coverCount E (E.image Prod.fst) U (E.image Prod.snd) V
      (fun e he => Finset.mem_image_of_mem _ he) (fun e he => Finset.mem_image_of_mem _ he)
      hU hV hits no4 cap
    omega
  by_cases small : P.card + L.card ≤ 4512
  · exact counting P L subP subL cover small budget
  by_cases other : ∃ U V : Finset (Fin n), U ⊆ E.image Prod.fst ∧ V ⊆ E.image Prod.snd ∧
      (∀ e ∈ E, e.1 ∈ U ∨ e.2 ∈ V) ∧ U.card + V.card ≤ 4512
  · obtain ⟨U,V,hU,hV,hits,cap⟩ := other
    exact counting U V hU hV hits cap (by omega)
  exact largeBound q n I C E hq (by omega) hn lines uniq model sound accepts deg other
