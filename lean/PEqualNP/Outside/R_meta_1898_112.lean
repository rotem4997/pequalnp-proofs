import Mathlib.Combinatorics.Enumerative.DoubleCounting
import PEqualNP.Defs

open Finset PEqualNP.AndCount

-- The normal form, gate-elimination bounds and size-twelve case are adapted from
-- TheWaler's reduction in PR 6133. The operand count below rules out size eleven.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_1898_112
    (hGeom :
      let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let oriented := fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧
        (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let free := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ q ∈ P, ¬ I q l
      let U := fun (P : Finset (Fin 13)) => Finset.univ.filter fun k : Fin 26 =>
        (∃ p ∈ P, k = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ free P l
      ∀ v a b : Fin 26, a ≠ v → b ≠ v → ¬ (oriented a b ∨ oriented b a) →
        ∃ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l, free P l ∧ I p l) ∧
          ((¬∃ l, ∀ p ∈ P, I p l) ∧ ¬∃ p, ∀ l, free P l → I p l) ∧
          a ∈ U P ∧ b ∈ U P ∧ v ∉ U P)
    (hLadder :
      let I (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let pt := (Fin.castAdd 13 : Fin 13 → Fin 26)
      let ln := (Fin.natAdd 13 : Fin 13 → Fin 26)
      let free (P : Finset (Fin 13)) (l : Fin 13) := ∀ p ∈ P, ¬ I p l
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26, D.WellFormed →
        (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l, I p l → D.eval {pt p, ln l} = true) →
        (∀ P, (∀ p ∉ P, ∃ l, free P l ∧ I p l) →
          ((¬ ∃ l, ∀ p ∈ P, I p l) ∧ ¬ ∃ p, ∀ l, free P l → I p l) →
          D.eval (Finset.univ.filter fun k => (∃ p ∈ P, k = pt p) ∨ ∃ l, k = ln l ∧ free P l) = false) →
        let G (v : Fin 26) := Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
        D.outVars = ∅ ∧ 11 ≤ D.size ∧ (∀ v, (G v).card + 9 ≤ D.size) ∧
          (∀ p l, ¬ I p l → (G (pt p) ∪ G (ln l)).card + 7 ≤ D.size) ∧
          (∀ p q, p ≠ q → (G (pt p) ∪ G (pt q)).card + 6 ≤ D.size ∧
            (G (ln p) ∪ G (ln q)).card + 6 ≤ D.size))
    (hSize12 :
      let E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let G (D : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin D.size) :=
        Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.WellFormed → D.size = 12 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l : Fin 13, E p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
        (∀ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ E q l) ∧ E p l) →
          ((¬∃ l : Fin 13, ∀ p ∈ P, E p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ E q l) → E p l) →
          D.eval (Finset.univ.filter fun k : Fin 26 =>
            (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ E q l) = false) →
        (∀ v : Fin 26, (G D v).card ≤ 3) →
        (∀ p l : Fin 13, ¬ E p l → (G D (Fin.castAdd 13 p) ∪ G D (Fin.natAdd 13 l)).card ≤ 5) →
        (∀ p1 p2 : Fin 13, p1 ≠ p2 → (G D (Fin.castAdd 13 p1) ∪ G D (Fin.castAdd 13 p2)).card ≤ 6) →
        (∀ l1 l2 : Fin 13, l1 ≠ l2 → (G D (Fin.natAdd 13 l1) ∪ G D (Fin.natAdd 13 l2)).card ≤ 6) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  have hSize11 :
      let E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let G (D : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin D.size) :=
        Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.WellFormed → D.size = 11 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l : Fin 13, E p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
        (∀ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ E q l) ∧ E p l) →
          ((¬∃ l : Fin 13, ∀ p ∈ P, E p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ E q l) → E p l) →
          D.eval (Finset.univ.filter fun k : Fin 26 =>
            (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ E q l) = false) →
        (∀ v : Fin 26, (G D v).card ≤ 2) →
        (∀ p l : Fin 13, ¬ E p l → (G D (Fin.castAdd 13 p) ∪ G D (Fin.natAdd 13 l)).card ≤ 4) →
        (∀ p1 p2 : Fin 13, p1 ≠ p2 → (G D (Fin.castAdd 13 p1) ∪ G D (Fin.castAdd 13 p2)).card ≤ 5) →
        (∀ l1 l2 : Fin 13, l1 ≠ l2 → (G D (Fin.natAdd 13 l1) ∪ G D (Fin.natAdd 13 l2)).card ≤ 5) →
        False := by
    let V := Fin 26
    let Slot := Fin 11 × Bool
    -- A smallest deficient family has no vertex with a private operand slot.
    have selectCore (occ : V → Finset Slot) :
        ∃ T : Finset V, (T.biUnion occ).card + 4 ≤ T.card ∧
          ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w := by
      classical
      let candidates := (Finset.univ : Finset (Finset V)).filter fun T =>
        (T.biUnion occ).card + 4 ≤ T.card
      have full : Finset.univ ∈ candidates := by
        have h := Finset.card_le_univ ((Finset.univ : Finset V).biUnion occ)
        simpa [candidates, V, Slot] using h
      obtain ⟨T, hm, hmin⟩ := candidates.exists_min_image Finset.card ⟨_, full⟩
      have ht : (T.biUnion occ).card + 4 ≤ T.card := (Finset.mem_filter.mp hm).2
      refine ⟨T, ht, ?_⟩
      intro v hv s hs
      by_contra! h
      have hsub : (T.erase v).biUnion occ ⊆ T.biUnion occ :=
        fun _ hi => by
          obtain ⟨w, hw, hi⟩ := Finset.mem_biUnion.mp hi
          exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_of_mem_erase hw, hi⟩
      have hlt : ((T.erase v).biUnion occ).card < (T.biUnion occ).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨hsub, ?_⟩
        intro he
        have hs' : s ∈ (T.erase v).biUnion occ := he ▸ Finset.mem_biUnion.mpr ⟨v, hv, hs⟩
        obtain ⟨w, hw, hsw⟩ := Finset.mem_biUnion.mp hs'
        exact h w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw) hsw
      have hsize := Finset.card_erase_add_one hv
      have hm' : T.erase v ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have := hmin _ hm'
      omega
    have distinct_other (v : V) : ∃ w : V, w ≠ v := by
      by_cases h : v = 0
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, Ne.symm h⟩
    have occ_not_subset (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) {v w : V} (hne : v ≠ w) : ¬ occ v ⊆ occ w := by
      intro h
      exact irr w (sep v w w hne.symm hne.symm (h.trans subset_union_left))
    have otherSlot (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (s : Slot) (v : V) (hv : v ∈ T) (hs : s ∈ occ v) :
        ∃ k : Slot, k ≠ s ∧ occ v = {s, k} := by
      obtain ⟨a, _, ha, hsa⟩ := core v hv s hs
      have hn := occ_not_subset E occ irr sep ha.symm
      have he := card_erase_add_one hs
      have hne : ((occ v).erase s).Nonempty := by
        by_contra h
        apply hn
        intro i hi
        by_cases eq : i = s
        · simpa [eq] using hsa
        · exact (h ⟨i, mem_erase.mpr ⟨eq, hi⟩⟩).elim
      obtain ⟨k, hk⟩ := hne
      have h1 : ((occ v).erase s).card ≤ 1 := by have := cap v; omega
      have heq : (occ v).erase s = {k} := eq_singleton_iff_unique_mem.mpr
        ⟨hk, fun i hi => card_le_one.mp h1 _ hi _ hk⟩
      exact ⟨k, ne_of_mem_erase hk, by simpa [← heq] using (insert_erase hs).symm⟩
    let users (T : Finset V) (occ : V → Finset Slot) (s : Slot) :=
      T.filter fun v => s ∈ occ v
    -- For a vertex using two slots, other users of opposite slots must be incident.
    have opposite (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (s : Slot) (v : V) (hv : v ∈ users T occ s) :
        ∃ k w, k ≠ s ∧ occ v = {s, k} ∧ w ∈ T ∧ w ≠ v ∧ k ∈ occ w ∧
          ∀ a ∈ users T occ s, a ≠ v → E a w := by
      obtain ⟨hvT, hsv⟩ := mem_filter.mp hv
      obtain ⟨k, hk, eq⟩ := otherSlot E occ irr sep cap T core s v hvT hsv
      obtain ⟨w, hw, hne, hkw⟩ := core v hvT k (by simp [eq])
      refine ⟨k, w, hk, eq, hw, hne, hkw, ?_⟩
      intro a ha hav
      apply sep v a w hav hne
      rw [eq]
      exact insert_subset_iff.mpr ⟨mem_union_left _ (mem_filter.mp ha).2, singleton_subset_iff.mpr (mem_union_right _ hkw)⟩
    have same_neighbor (E : V → V → Prop) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (A : Finset V) (hA : 1 < A.card) (x y : V)
        (hx : ∀ a ∈ A, E a x) (hy : ∀ a ∈ A, E a y) : x = y := by
      obtain ⟨a, ha, b, hb, hn⟩ := one_lt_card.mp hA
      exact common hn (hx a ha) (hx b hb) (hy a ha) (hy b hb)
    -- A common neighbor of three or more users would need a different slot for each user.
    have no_universal (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (s : Slot) (hlarge : 2 < (users T occ s).card) (z : V) :
        ¬ (∀ v ∈ users T occ s, E v z) := by
      intro all_adj
      let A := users T occ s
      have aux (v : V) (hv : v ∈ A) : ∃ k ∈ occ z, occ v = {s, k} := by
        obtain ⟨k,w,_,eq,_,_,hkw,ha⟩ := opposite E occ irr sep cap T core s v hv
        have erase := card_erase_add_one hv
        have hz := same_neighbor E common (A.erase v) (by change 2 < A.card at hlarge; omega) w z
          (fun a h => ha a (mem_of_mem_erase h) (ne_of_mem_erase h))
          (fun a h => all_adj a (mem_of_mem_erase h))
        exact ⟨k, hz ▸ hkw, eq⟩
      choose f hf he using aux
      let g (v : ↥A) : ↥(occ z) := ⟨f v v.2, hf v v.2⟩
      have inj : Function.Injective g := by
        intro a b eq
        have h := congrArg Subtype.val eq
        change f a a.2 = f b b.2 at h
        by_contra hn
        exact occ_not_subset E occ irr sep (fun e => hn (Subtype.ext e))
          (by rw [he a a.2, he b b.2, h])
      have hcard := card_le_card_of_injective inj
      have hz := cap z
      change 2 < A.card at hlarge
      omega
    have users_le_three (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (s : Slot) : (users T occ s).card ≤ 3 := by
      by_contra! h
      let A := users T occ s
      change 3 < A.card at h
      obtain ⟨v, hv, u, hu, hvu⟩ := one_lt_card.mp (by omega : 1 < A.card)
      obtain ⟨_, z, _, _, _, _, _, hz⟩ := opposite E occ irr sep cap T core s v hv
      obtain ⟨_, w, _, _, _, _, _, hw⟩ := opposite E occ irr sep cap T core s u hu
      have hv' := card_erase_add_one hv
      have hu' := card_erase_add_one (mem_erase.mpr ⟨Ne.symm hvu, hu⟩ : u ∈ A.erase v)
      have hzw := same_neighbor E common ((A.erase v).erase u) (by omega) z w
        (fun i hi => hz i (mem_of_mem_erase (mem_of_mem_erase hi)) (ne_of_mem_erase (mem_of_mem_erase hi)))
        (fun i hi => hw i (mem_of_mem_erase (mem_of_mem_erase hi)) (ne_of_mem_erase hi))
      apply no_universal E occ irr sep cap T core common s (by change 2 < A.card; omega) z
      intro i hi
      by_cases he : i = v
      · subst i
        exact hzw ▸ hw v hv hvu
      · exact hz i hi he
    have other_users (E : V → V → Prop) (occ : V → Finset Slot) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (s k : Slot) (hs : 2 < (users T occ s).card) (v : V)
        (hv : v ∈ users T occ s) (eq : occ v = {s,k}) :
        ∃ w ∈ T, w ≠ v ∧ users T occ k = {v,w} ∧
          (∀ a ∈ users T occ s, a ≠ v → E a w) := by
      obtain ⟨hvT, hsv⟩ := mem_filter.mp hv
      obtain ⟨w,hw,hwv,hkw⟩ := core v hvT k (by simp [eq])
      have cross (b : V) (hb : b ∈ users T occ k) (hne : b ≠ v) :
          ∀ a ∈ users T occ s, a ≠ v → E a b := by
        intro a ha hav
        apply sep v a b hav hne
        rw [eq]
        exact insert_subset_iff.mpr ⟨mem_union_left _ (mem_filter.mp ha).2,
          singleton_subset_iff.mpr (mem_union_right _ (mem_filter.mp hb).2)⟩
      have wmem : w ∈ users T occ k := mem_filter.mpr ⟨hw,hkw⟩
      refine ⟨w,hw,hwv,?_,cross w wmem hwv⟩
      ext b
      rw [mem_insert,mem_singleton]
      constructor
      · intro hb
        by_cases h : b = v
        · exact Or.inl h
        · apply Or.inr
          have := card_erase_add_one hv
          apply same_neighbor E common ((users T occ s).erase v) (by omega)
          · exact fun a ha => cross b hb h a (mem_of_mem_erase ha) (ne_of_mem_erase ha)
          · exact fun a ha => cross w wmem hwv a (mem_of_mem_erase ha) (ne_of_mem_erase ha)
      · rintro (rfl | rfl)
        · exact mem_filter.mpr ⟨hvT, by simp [eq]⟩
        · exact wmem
    let branches (T : Finset V) (occ : V → Finset Slot) : Finset Slot :=
      (T.biUnion occ).filter fun s => 2 < (users T occ s).card
    -- Count the uses of slots from both ends. Each retained vertex uses exactly two.
    have many_branches (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (hd : (T.biUnion occ).card + 4 ≤ T.card) :
        8 ≤ (branches T occ).card := by
      classical
      let U := T.biUnion occ
      have occ_two (v : V) (hv : v ∈ T) : (occ v).card = 2 := by
        have nonempty : (occ v).Nonempty := by
          obtain ⟨a, ha⟩ := distinct_other v
          by_contra! he
          exact occ_not_subset E occ irr sep (Ne.symm ha) (by simp [he])
        obtain ⟨s,hs⟩ := nonempty
        obtain ⟨k,hk,eq⟩ := otherSlot E occ irr sep cap T core s v hv hs
        simp [eq, hk.symm]
      have hand : ∑ s ∈ U, (users T occ s).card = 2 * T.card := by
        change ∑ s ∈ U, (T.bipartiteBelow (fun v s => s ∈ occ v) s).card = _
        rw [← sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (fun v s => s ∈ occ v) (s := T) (t := U)]
        calc
          _ = ∑ v ∈ T, 2 := by
            apply sum_congr rfl
            intro v hv
            have he : U.bipartiteAbove (fun v s => s ∈ occ v) v = occ v := by
              ext s
              exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_biUnion.mpr ⟨v,hv,h⟩,h⟩⟩
            rw [he, occ_two v hv]
          _ = _ := by simp [Nat.mul_comm]
      have hcap : ∑ s ∈ U, (users T occ s).card ≤ 2 * U.card + (branches T occ).card := by
        calc
          _ ≤ ∑ s ∈ U, (2 + if 2 < (users T occ s).card then 1 else 0) := by
            apply sum_le_sum
            intro s hs
            have := users_le_three E occ irr sep cap T core common s
            split <;> omega
          _ = _ := by simp [sum_add_distrib, branches, U, Nat.mul_comm]
      change U.card + 4 ≤ T.card at hd
      omega
    have branches_disjoint (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) : (branches T occ : Set Slot).PairwiseDisjoint (users T occ) := by
      intro s hs k hk hne
      apply disjoint_left.mpr
      intro v hv hvk
      obtain ⟨j, hj, eq⟩ := otherSlot E occ irr sep cap T core s v (mem_filter.mp hv).1 (mem_filter.mp hv).2
      have kj : k = j := by
        have mem := (mem_filter.mp hvk).2
        rw [eq, mem_insert,mem_singleton] at mem
        exact mem.resolve_left (Ne.symm hne)
      subst j
      obtain ⟨w,_,_,he,_⟩ := other_users E occ sep T core common s k (mem_filter.mp hs).2 v hv eq
      have large := (mem_filter.mp hk).2
      rw [he] at large
      have hc := card_insert_le v {w}
      simp only [card_singleton] at hc
      omega
    have covered_by_branches (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (hd : (T.biUnion occ).card + 4 ≤ T.card) :
        24 ≤ ((branches T occ).biUnion (users T occ)).card ∧ (branches T occ).card ≤ 8 := by
      have hsum : ((branches T occ).biUnion (users T occ)).card = 3 * (branches T occ).card := by
        rw [card_biUnion (branches_disjoint E occ irr sep cap T core common)]
        calc
          _ = ∑ s ∈ branches T occ, 3 := by
            apply sum_congr rfl
            intro s h
            have := (mem_filter.mp h).2
            have := users_le_three E occ irr sep cap T core common s
            omega
          _ = _ := by simp [Nat.mul_comm]
      have hm := many_branches E occ irr sep cap T core common hd
      have hmax := card_le_univ ((branches T occ).biUnion (users T occ))
      change _ ≤ 26 at hmax
      omega
    let active (T : Finset V) (occ : V → Finset Slot) :=
      (branches T occ).biUnion (users T occ)
    let side (T : Finset V) (occ : V → Finset Slot) (slot : Slot) :=
      (users T occ slot) ∩ active T occ
    have mono_branch (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (col : V → Bool) (colE : ∀ {a b}, E a b → col a ≠ col b) (s : Slot) (h : s ∈ branches T occ) {v w : V}
        (hv : v ∈ users T occ s) (hw : w ∈ users T occ s) : col v = col w := by
      by_cases he : v = w
      · exact congrArg col he
      let A := users T occ s
      have hl := (mem_filter.mp h).2
      change 2 < A.card at hl
      have hsize := card_erase_add_one (show v ∈ A from hv)
      obtain ⟨a,ha,haw⟩ := exists_mem_ne (by omega : 1 < (A.erase v).card) w
      obtain ⟨_, z, _, _, _, _, _, hz⟩ := opposite E occ irr sep cap T core s a (mem_of_mem_erase ha)
      exact (Bool.eq_not_of_ne (colE (hz v hv (Ne.symm (ne_of_mem_erase ha))))).trans
        (Bool.eq_not_of_ne (colE (hz w hw (Ne.symm haw)))).symm
    -- When one of a vertex’s slots contains a triangle, its other slot has one point and one line.
    have mixed_side (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (col : V → Bool) (colE : ∀ {a b}, E a b → col a ≠ col b) (s : Slot) (h : s ∉ branches T occ) {v w : V}
        (hv : v ∈ side T occ s) (hw : w ∈ side T occ s) (hne : v ≠ w) : col v ≠ col w := by
      obtain ⟨hv₁, hv₂⟩ := mem_inter.mp hv
      obtain ⟨t,ht,hvt⟩ := mem_biUnion.mp hv₂
      have hst : s ≠ t := fun he => h (he ▸ ht)
      obtain ⟨k,hk,eq⟩ := otherSlot E occ irr sep cap T core t v (mem_filter.mp hvt).1 (mem_filter.mp hvt).2
      have e : s = k := by
        have mem := (mem_filter.mp hv₁).2
        rw [eq,mem_insert,mem_singleton] at mem
        exact mem.resolve_left hst
      subst k
      have htlarge := (mem_filter.mp ht).2
      obtain ⟨q,_,_,hq,hadj⟩ := other_users E occ sep T core common t s htlarge v hvt eq
      have hw' := (mem_inter.mp hw).1
      rw [hq,mem_insert,mem_singleton] at hw'
      have eqw := hw'.resolve_left (Ne.symm hne)
      subst q
      obtain ⟨a,ha,hav⟩ := exists_mem_ne (by omega : 1 < (users T occ t).card) v
      exact (mono_branch E occ irr sep cap T core col colE t ht hvt ha) ▸ colE (hadj a ha hav)
    have side_degree (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) [DecidableRel E] (s : Slot) (z : V) :
        ((side T occ s).filter fun a => E a z).card ≤ 2 := by
      let A := users T occ s
      have sub : (side T occ s).filter (fun a => E a z) ⊆ A :=
        (filter_subset ..).trans inter_subset_left
      have bound := users_le_three E occ irr sep cap T core common s
      change A.card ≤ 3 at bound
      by_contra! big
      have he : (side T occ s).filter (fun a => E a z) = A :=
        eq_of_subset_of_card_le sub (by omega)
      exact no_universal E occ irr sep cap T core common s
        (by change 2 < A.card; rw [← he]; exact big) z
        (fun a ha => (mem_filter.mp (show a ∈ (side T occ s).filter (fun a => E a z) by rw [he]; exact ha)).2)
    let links (E : V → V → Prop) [DecidableRel E] (A B : Finset V) :=
      (A ×ˢ B).filter fun p => E p.1 p.2
    have links_sum (E : V → V → Prop) [DecidableRel E] (A B : Finset V) :
        (links E A B).card = ∑ a ∈ A, (B.filter (fun b => E a b)).card := by
      simp only [links, card_eq_sum_ones, sum_filter, sum_product]
    have links_swap (E : V → V → Prop) (sym : ∀ {a b}, E a b → E b a) [DecidableRel E] (A B : Finset V) :
        (links E A B).card = (links E B A).card := by
      rw [links_sum, links_sum]
      simp only [card_eq_sum_ones, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      by_cases h : E a b
      · simp [h,sym h]
      · simp [h,mt (sym (a:=b) (b:=a)) h]
    have links_six (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (sym : ∀ {a b}, E a b → E b a) [DecidableRel E] (s k : Slot) :
        (links E (side T occ s) (side T occ k)).card ≤ 6 := by
      rw [links_sum]
      have bound := (side T occ s).sum_le_card_nsmul (fun a =>
        ((side T occ k).filter fun b => E a b).card) 2 (fun a _ => by
          simpa only [show (fun b => E a b) = (fun b => E b a) from
            funext fun b => propext ⟨sym,sym⟩] using side_degree E occ irr sep cap T core common k a)
      have hc := card_le_card (inter_subset_left (s₁ := users T occ s) (s₂ := active T occ))
      have hl := users_le_three E occ irr sep cap T core common s
      change (side T occ s).card ≤ _ at hc
      simpa using (bound.trans (by simp; omega))
    have links_two (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (T : Finset V) (core : ∀ v ∈ T, ∀ s ∈ occ v, ∃ w ∈ T, w ≠ v ∧ s ∈ occ w) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (col : V → Bool) (colE : ∀ {a b}, E a b → col a ≠ col b) (sym : ∀ {a b}, E a b → E b a) [DecidableRel E] (s k : Slot) (hs : s ∉ branches T occ) :
        (links E (side T occ s) (side T occ k)).card ≤ 2 := by
      have hs2 : (side T occ s).card ≤ 2 := by
        have small : (users T occ s).card ≤ 2 := by
          by_contra! h
          obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0 < (users T occ s).card)
          exact hs (mem_filter.mpr ⟨mem_biUnion.mpr ⟨v,(mem_filter.mp hv).1,(mem_filter.mp hv).2⟩,h⟩)
        exact (card_le_card inter_subset_left).trans small
      by_cases hk : k ∈ branches T occ
      · obtain ⟨v,hv⟩ := card_pos.mp (by have := (mem_filter.mp hk).2; omega : 0 < (users T occ k).card)
        let B := (side T occ s).filter fun a => col a ≠ col v
        have hc : B.card ≤ 1 := by
          apply card_le_one.mpr
          intro a ha b hb
          by_contra hn
          have hne := mixed_side E occ irr sep cap T core common col colE s hs
            (mem_filter.mp ha).1 (mem_filter.mp hb).1 hn
          exact hne ((Bool.eq_not_of_ne (mem_filter.mp ha).2).trans
            (Bool.eq_not_of_ne (mem_filter.mp hb).2).symm)
        have restrict : links E (side T occ s) (side T occ k) = links E B (side T occ k) := by
          ext p
          simp only [links, mem_filter, mem_product, B]
          constructor
          · rintro ⟨⟨a,b⟩,e⟩
            have same := mono_branch E occ irr sep cap T core col colE k hk (mem_inter.mp b).1 hv
            exact ⟨⟨⟨a,same ▸ colE e⟩,b⟩,e⟩
          · exact fun h => ⟨⟨h.1.1.1,h.1.2⟩,h.2⟩
        rw [restrict,links_sum]
        have hdeg (a : V) : ((side T occ k).filter fun b => E a b).card ≤ 2 := by
          simpa only [show (fun b => E a b) = (fun b => E b a) from
            funext fun b => propext ⟨sym,sym⟩] using side_degree E occ irr sep cap T core common k a
        exact (B.sum_le_card_nsmul _ 2 (fun a _ => hdeg a)).trans (by simp; omega)
      · rw [links_sum]
        have hdeg (a : V) : ((side T occ k).filter fun b => E a b).card ≤ 1 := by
          apply card_le_one.mpr
          intro x hx y hy
          by_contra hn
          have hne := mixed_side E occ irr sep cap T core common col colE k hk
            (mem_filter.mp hx).1 (mem_filter.mp hy).1 hn
          exact hne ((Bool.eq_not_of_ne (Ne.symm (colE (mem_filter.mp hx).2))).trans
            (Bool.eq_not_of_ne (Ne.symm (colE (mem_filter.mp hy).2))).symm)
        exact ((side T occ s).sum_le_card_nsmul _ 1 (fun a _ => hdeg a)).trans (by simpa using hs2)
    -- Removing two vertices loses at most sixteen ordered incidences.
    have incidentLower (E : V → V → Prop) [DecidableRel E] (W : Finset V) (hw : 24 ≤ W.card)
        (sym : ∀ {a b}, E a b → E b a)
        (full : 104 ≤ (links E univ univ).card)
        (four : ∀ a, ((univ : Finset V).filter (E a)).card ≤ 4) :
        88 ≤ (links E W W).card := by
      classical
      let L := links E
      have sub : L univ univ ⊆ L W W ∪ L Wᶜ univ ∪ L univ Wᶜ := by
        intro p h
        have e := (mem_filter.mp h).2
        simp only [L,links,mem_filter,mem_product,mem_univ,true_and,and_true,mem_union, mem_compl]
        by_cases a : p.1 ∈ W <;> by_cases b : p.2 ∈ W <;> simp [a,b,e]
      have bound : (L Wᶜ univ).card ≤ 8 := by
        have hc := card_compl_add_card W
        change Wᶜ.card + W.card = 26 at hc
        rw [show L = links E from rfl, links_sum]
        exact (Wᶜ.sum_le_card_nsmul _ 4 (fun a _ => four a)).trans (by simp; omega)
      have b := card_union_le (L W W ∪ L Wᶜ univ) (L univ Wᶜ)
      have c := card_union_le (L W W) (L Wᶜ univ)
      have d := card_le_card sub
      have eq : (L univ Wᶜ).card = (L Wᶜ univ).card := links_swap E sym _ _
      change 104 ≤ (L univ univ).card at full
      change 88 ≤ (L W W).card
      omega
    -- Eleven gates can cover at most seventy-six ordered incidences among the twenty-four vertices.
    have impossible_eleven (E : V → V → Prop) (occ : V → Finset Slot) (irr : ∀ a, ¬ E a a) (sep : ∀ v a b, a ≠ v → b ≠ v → occ v ⊆ occ a ∪ occ b → E a b) (cap : ∀ v, (occ v).card ≤ 2) (common : ∀ {a b x y : V}, a ≠ b → E a x → E b x → E a y → E b y → x = y) (col : V → Bool) (colE : ∀ {a b}, E a b → col a ≠ col b) (sym : ∀ {a b}, E a b → E b a) [DecidableRel E]
        (pairs : ∀ x y, E x y → ∃ j : Fin 11,
          ((j,false) ∈ occ x ∧ (j,true) ∈ occ y) ∨ ((j,true) ∈ occ x ∧ (j,false) ∈ occ y))
        (full : 104 ≤ (links E univ univ).card)
        (four : ∀ a, ((univ : Finset V).filter (E a)).card ≤ 4) : False := by
      classical
      obtain ⟨T, hd, core⟩ := selectCore occ
      let W := active T occ
      let S := side T occ
      let B := branches T occ
      obtain ⟨hw,hb⟩ := covered_by_branches E occ irr sep cap T core common hd
      have lower := incidentLower E W hw sym full four
      let hits (j : Fin 11) := links E (S (j,false)) (S (j,true)) ∪ links E (S (j,true)) (S (j,false))
      have sub : links E W W ⊆ univ.biUnion hits := by
        intro p h
        obtain ⟨⟨hx,hy⟩,e⟩ := (show p.1 ∈ W ∧ p.2 ∈ W from mem_product.mp (mem_filter.mp h).1), (mem_filter.mp h).2
        have incl (v : V) (hv : v ∈ W) (s : Slot) (hsv : s ∈ occ v) : v ∈ S s := by
          obtain ⟨t,_,hvt⟩ := mem_biUnion.mp hv
          exact mem_inter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hvt).1,hsv⟩,hv⟩
        obtain ⟨j,hj⟩ := pairs _ _ e
        apply mem_biUnion.mpr
        refine ⟨j,mem_univ _,?_⟩
        cases hj with
        | inl a => exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨incl _ hx _ a.1,incl _ hy _ a.2⟩,e⟩)
        | inr a => exact mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr ⟨incl _ hx _ a.1,incl _ hy _ a.2⟩,e⟩)
      let b (s : Slot) : ℕ := if s ∈ B then 1 else 0
      have hbcount : ∑ j : Fin 11, (b (j,false) + b (j,true)) = B.card := by
        calc
          _ = ∑ s : Slot, b s := by rw [Fintype.sum_prod_type]; simp [add_comm]
          _ = _ := by simp [b]
      have cost (j : Fin 11) : (hits j).card ≤ 4 + 4 * (b (j,false) + b (j,true)) := by
        let s : Slot := (j,false)
        let k : Slot := (j,true)
        have u := card_union_le (links E (S s) (S k)) (links E (S k) (S s))
        have sw := links_swap E sym (S k) (S s)
        change (links E (S s) (S k) ∪ links E (S k) (S s)).card ≤ 4 + 4 * (b s + b k)
        by_cases hs : s ∈ B <;> by_cases hk : k ∈ B
        · have h := links_six E occ irr sep cap T core common sym s k
          change (links E (S s) (S k)).card ≤ 6 at h
          simp only [b,ite_eq_left hs,ite_eq_left hk]
          omega
        · have h := links_two E occ irr sep cap T core common col colE sym k s hk
          change (links E (S k) (S s)).card ≤ 2 at h
          omega
        · have h := links_two E occ irr sep cap T core common col colE sym s k hs
          change (links E (S s) (S k)).card ≤ 2 at h
          omega
        · have h := links_two E occ irr sep cap T core common col colE sym s k hs
          change (links E (S s) (S k)).card ≤ 2 at h
          omega
      have upper := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (fun j _ => cost j)))
      rw [sum_add_distrib, ← mul_sum, hbcount] at upper
      simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at upper
      change B.card ≤ 8 at hb
      omega

    let rawVars {n : ℕ} (D : AndCountCircuit n) (s : Fin D.size × Bool) : Finset (Fin n) :=
      if s.2 then D.rightVars s.1 else D.leftVars s.1

    let rawOcc {n : ℕ} (D : AndCountCircuit n) (v : Fin n) : Finset (Fin D.size × Bool) :=
      univ.filter fun s => v ∈ rawVars D s

    have mem_rawOcc {n : ℕ} (D : AndCountCircuit n) (v : Fin n) (s : Fin D.size × Bool) :
        s ∈ rawOcc D v ↔ v ∈ rawVars D s := by simp [rawOcc]

    have rawEvalEq {n : ℕ} (D : AndCountCircuit n) (U : Finset (Fin n)) :
        D.eval U = decide ((∃ v ∈ D.outVars, v ∈ U) ∨ ∃ j ∈ D.outGates, D.gateVal U j = true) := rfl
    have rawSideEq {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
        (val : Fin k → Bool) :
        AndCountCircuit.sideTrue U B F i val =
          decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := rfl
    have rawNextEq {n : ℕ} (D : AndCountCircuit n) (U : Finset (Fin n)) (d : ℕ) (i : Fin D.size) :
        D.gateValFuel U (d + 1) i =
          (AndCountCircuit.sideTrue U (D.leftVars i) (D.leftGates i) i (D.gateValFuel U d) &&
           AndCountCircuit.sideTrue U (D.rightVars i) (D.rightGates i) i (D.gateValFuel U d)) := rfl

    have rawPair {n : ℕ} (D : AndCountCircuit n) (out : D.outVars = ∅)
        (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i))
        {x y : Fin n} (positive : D.eval {x, y} = true) :
        ∃ i, ((i, false) ∈ rawOcc D x ∧ (i, true) ∈ rawOcc D y) ∨
          ((i, true) ∈ rawOcc D x ∧ (i, false) ∈ rawOcc D y) := by
      simp [rawEvalEq, out] at positive
      obtain ⟨i, _, hi⟩ := positive
      suffices aux : ∀ (d : ℕ) (j : Fin D.size), D.gateValFuel {x,y} d j = true →
          ∃ k, (x ∈ D.leftVars k ∧ y ∈ D.rightVars k) ∨
            (x ∈ D.rightVars k ∧ y ∈ D.leftVars k) by
        simpa only [mem_rawOcc, rawVars, Bool.false_eq_true, ite_false, ite_true] using aux D.size i hi
      intro d
      induction d with
      | zero => intro _ h; exact (Bool.false_ne_true h).elim
      | succ d ih =>
        intro j h
        simp only [rawNextEq, Bool.and_eq_true, rawSideEq,
          decide_eq_true_eq, mem_insert, mem_singleton] at h
        rcases h.1 with ⟨a, ha, rfl | rfl⟩ | ⟨k, _, _, hk⟩
        · rcases h.2 with ⟨b, hb, rfl | rfl⟩ | ⟨k, _, _, hk⟩
          · exact (Finset.disjoint_left.mp (disj j) ha hb).elim
          · exact ⟨j, Or.inl ⟨ha, hb⟩⟩
          · exact ih k hk
        · rcases h.2 with ⟨b, hb, rfl | rfl⟩ | ⟨k, _, _, hk⟩
          · exact ⟨j, Or.inr ⟨hb, ha⟩⟩
          · exact (Finset.disjoint_left.mp (disj j) ha hb).elim
          · exact ih k hk
        · exact ih k hk

    have rawDominates {n : ℕ} (D : AndCountCircuit n) (out : D.outVars = ∅)
        {U Z : Finset (Fin n)}
        (cover : ∀ s : Fin D.size × Bool, (∃ v ∈ U, v ∈ rawVars D s) → ∃ v ∈ Z, v ∈ rawVars D s)
        (accepted : D.eval U = true) : D.eval Z = true := by
      simp [rawEvalEq, out] at accepted ⊢
      obtain ⟨g, hg, h⟩ := accepted
      refine ⟨g, hg, ?_⟩
      suffices mono : ∀ (d : ℕ) (j : Fin D.size), D.gateValFuel U d j = true → D.gateValFuel Z d j = true
        from mono D.size g h
      intro d
      induction d with
      | zero => exact fun _ h => h
      | succ d ih =>
        intro j
        have side (b : Bool) (F : Finset (Fin D.size)) :
            AndCountCircuit.sideTrue U (rawVars D (j,b)) F j (D.gateValFuel U d) = true →
            AndCountCircuit.sideTrue Z (rawVars D (j,b)) F j (D.gateValFuel Z d) = true := by
          simp only [rawSideEq, decide_eq_true_eq]
          rintro (⟨v, hv, hu⟩ | ⟨k, hk, hkj, ht⟩)
          · obtain ⟨w, hw, hz⟩ := cover (j,b) ⟨v, hu, hv⟩
            exact Or.inl ⟨w, hz, hw⟩
          · exact Or.inr ⟨k, hk, hkj, ih k ht⟩
        simp only [rawNextEq, Bool.and_eq_true]
        exact fun h => ⟨side false _ h.1, side true _ h.2⟩

    have rawExcluded {n : ℕ} (D : AndCountCircuit n) (out : D.outVars = ∅)
        {v w : Fin n} {Z : Finset (Fin n)} (accept : D.eval {v,w} = true)
        (hw : w ∈ Z) (reject : D.eval Z = false) :
        ∃ s ∈ rawOcc D v, ∀ a ∈ Z, s ∉ rawOcc D a := by
      by_contra! h
      have covered (s : Fin D.size × Bool) (hs : ∃ z ∈ ({v,w} : Finset _), z ∈ rawVars D s) :
          ∃ z ∈ Z, z ∈ rawVars D s := by
        obtain ⟨z, hz, hzs⟩ := hs
        rcases mem_insert.mp hz with rfl | hz
        · obtain ⟨a, ha, has⟩ := h s ((mem_rawOcc D _ _).mpr hzs)
          exact ⟨a, ha, (mem_rawOcc D _ _).mp has⟩
        · obtain rfl := mem_singleton.mp hz
          exact ⟨z, hw, hzs⟩
      have contra := rawDominates D out covered accept
      simp [reject] at contra

    have rawOcc_card_le {n : ℕ} (D : AndCountCircuit n)
        (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i)) (v : Fin n) :
        (rawOcc D v).card ≤ (univ.filter fun i => v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · rintro ⟨i,b⟩ hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        cases b
        · exact Or.inl ((mem_rawOcc D _ _).mp hi)
        · exact Or.inr ((mem_rawOcc D _ _).mp hi)
      · rintro ⟨i,a⟩ ha ⟨j,b⟩ hb (rfl : i = j)
        have hA := (mem_rawOcc D _ _).mp ha
        have hB := (mem_rawOcc D _ _).mp hb
        cases a <;> cases b
        · rfl
        · exact (Finset.disjoint_left.mp (disj i) hA hB).elim
        · exact (Finset.disjoint_left.mp (disj i) hB hA).elim
        · rfl


    let incidence (a b : V) : Prop :=
      (a.val < 13 ∧ 13 ≤ b.val ∧
        (a.val + 26 - b.val) % 13 ∈ ([0,1,3,9] : List ℕ)) ∨
      (b.val < 13 ∧ 13 ≤ a.val ∧
        (b.val + 26 - a.val) % 13 ∈ ([0,1,3,9] : List ℕ))


    let col (v : V) : Bool := decide (v.val < 13)

    have incidence_symm {x y : V} (h : incidence x y) : incidence y x := h.symm

    let planeInc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

    let row (P : Finset (Fin 13)) : Finset V := Finset.univ.filter fun k : V =>
      (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ planeInc q l

    let Closed (P : Finset (Fin 13)) : Prop :=
      ∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ planeInc q l) ∧ planeInc p l

    let Generic (P : Finset (Fin 13)) : Prop :=
      (¬ ∃ l : Fin 13, ∀ p ∈ P, planeInc p l) ∧
        ¬ ∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ planeInc q l) → planeInc p l

    have codes : ∀ (p l : Fin 13),
        incidence (Fin.castAdd 13 p) (Fin.natAdd 13 l) ↔ planeInc p l := by decide

    have no_points : ∀ (p q : Fin 13), ¬ incidence (Fin.castAdd 13 p) (Fin.castAdd 13 q) :=
      by decide

    have no_lines : ∀ (l k : Fin 13), ¬ incidence (Fin.natAdd 13 l) (Fin.natAdd 13 k) :=
      by decide

    have vertex_positive (D : AndCountCircuit 26)
        (pos : ∀ p l : Fin 13, planeInc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) :
        ∀ a b : V, incidence a b → D.eval {a,b} = true := by
      intro a b
      induction a using (Fin.addCases (m := 13) (n := 13)) <;> induction b using (Fin.addCases (m := 13) (n := 13))
      case left.left p q => exact fun h => (no_points p q h).elim
      case left.right p l => exact fun h => pos p l ((codes p l).mp h)
      case right.left l p =>
        intro h
        simpa only [Finset.pair_comm] using pos p l ((codes p l).mp (incidence_symm h))
      case right.right l k => exact fun h => (no_lines l k h).elim

    have missingNeighbor (P : Finset (Fin 13)) (hc : Closed P) :
        ∀ v : V, v ∉ row P → ∃ w ∈ row P, incidence v w := by
      intro v
      induction v using (Fin.addCases (m := 13) (n := 13))
      case left p =>
        intro hv
        have hp : p ∉ P := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, h, rfl⟩⟩)
        obtain ⟨l, free, incident⟩ := hc p hp
        exact ⟨Fin.natAdd 13 l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨l, rfl, free⟩⟩,
          (codes p l).mpr incident⟩
      case right l =>
        intro hv
        by_contra! h
        apply hv
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨l, rfl, ?_⟩⟩
        intro p hp incident
        exact h (Fin.castAdd 13 p) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, hp, rfl⟩⟩)
          (incidence_symm ((codes p l).mpr incident))

    have rawSeparation (D : AndCountCircuit 26) (out : D.outVars = ∅)
        (pos : ∀ p l : Fin 13, planeInc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true)
        (neg : ∀ P, Closed P → Generic P → D.eval (row P) = false)
        (extension : ∀ v a b : V, a ≠ v → b ≠ v → ¬ incidence a b →
          ∃ P, Closed P ∧ Generic P ∧ a ∈ row P ∧ b ∈ row P ∧ v ∉ row P) :
        ∀ v a b : V, a ≠ v → b ≠ v → rawOcc D v ⊆ rawOcc D a ∪ rawOcc D b → incidence a b := by
      intro v a b hav hbv hsub
      by_contra nonedge
      obtain ⟨P, hc, hg, ha, hb, hv⟩ := extension v a b hav hbv nonedge
      obtain ⟨w, hw, edge⟩ := missingNeighbor P hc v hv
      obtain ⟨s, hs, hn⟩ := rawExcluded D out (vertex_positive D pos v w edge) hw (neg P hc hg)
      exact (Finset.mem_union.mp (hsub hs)).elim (hn a ha) (hn b hb)

    have rawCoverage (D : AndCountCircuit 26) (out : D.outVars = ∅)
        (disj : ∀ i, Disjoint (D.leftVars i) (D.rightVars i))
        (pos : ∀ p l : Fin 13, planeInc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true)
        (x y : V) (edge : incidence x y) :
        ∃ j : Fin D.size, ((j,false) ∈ rawOcc D x ∧ (j,true) ∈ rawOcc D y) ∨
          ((j,true) ∈ rawOcc D x ∧ (j,false) ∈ rawOcc D y) :=
      rawPair D out disj (vertex_positive D pos x y edge)
    have color_edge : ∀ a b : V, incidence a b → col a ≠ col b := by decide
    have no_loop : ∀ a : V, ¬ incidence a a := by decide
    have one_neighbor : ∀ a b : V, a ≠ b →
        ((univ : Finset V).filter fun w => incidence a w ∧ incidence b w).card ≤ 1 := by decide +kernel
    have common_pt {a b x y : V} (hne : a ≠ b) (ax : incidence a x) (bx : incidence b x)
        (ay : incidence a y) (by' : incidence b y) : x = y :=
      Finset.card_le_one.mp (one_neighbor a b hne) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ax, bx⟩)
        _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ay, by'⟩)
    have all_edges : 104 ≤ (links incidence univ univ).card := by decide +kernel
    have four_edges : ∀ a : V, ((univ : Finset V).filter (incidence a)).card ≤ 4 := by decide +kernel
    dsimp only
    intro D _ hs out _ disj pos neg cap _ _ _
    cases D with
    | mk k leftVars leftGates rightVars rightGates outVars outGates =>
      change k = 11 at hs
      subst k
      let D : AndCountCircuit 26 := ⟨11, leftVars, leftGates, rightVars, rightGates, outVars, outGates⟩
      exact impossible_eleven incidence (rawOcc D) no_loop (rawSeparation D out pos neg hGeom)
        (fun v => (rawOcc_card_le D disj v).trans (cap v)) (fun h => common_pt h) col
        (fun {a b} => color_edge a b) (fun h => incidence_symm h)
        (rawCoverage D out disj pos) all_edges four_edges
  classical
  intro C hm hPos hNeg
  have op_and_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have op_or_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have sideTrue_def : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool),
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := fun _ _ _ _ _ => rfl
  have eval_def : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := fun _ _ => rfl
  -- Part 1: Basic AndCountCircuit 26 evaluation helpers
  have sideTrue_congr : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k)
      (val val' : Fin k → Bool), (∀ j : Fin k, j < i → val j = val' j) →
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val' := by
    intro k U B F i val val' h
    rw [sideTrue_def, sideTrue_def, decide_eq_decide]
    constructor
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩
  have fuel_indep : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (d d' : ℕ) (i : Fin E.size), i.val < d → i.val < d' →
      E.gateValFuel U d i = E.gateValFuel U d' i := by
    intro E U d
    induction d with
    | zero =>
      intro d' i h
      exact absurd h (Nat.not_lt_zero _)
    | succ e ih =>
      intro d' i h h'
      cases d' with
      | zero => exact absurd h' (Nat.not_lt_zero _)
      | succ e' =>
        have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateValFuel U e' j := by
          intro j hj
          have hji : j.val < i.val := hj
          exact ih e' j (by omega) (by omega)
        show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) =
             (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e') &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e'))
        rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
            sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateVal_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)) (i : Fin E.size),
      E.gateVal U i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
    intro E U i
    have hi : i.val < E.size := i.2
    obtain ⟨e, he⟩ : ∃ e, E.size = e + 1 := ⟨E.size - 1, by omega⟩
    have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateVal U j := by
      intro j hj
      have hji : j.val < i.val := hj
      exact fuel_indep E U e E.size j (by omega) j.2
    have h1 : E.gateVal U i = E.gateValFuel U (e + 1) i :=
      fuel_indep E U E.size (e + 1) i i.2 (by omega)
    rw [h1]
    show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
          PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) = _
    rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
        sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateValFuel_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ (d : ℕ) (i : Fin E.size), E.gateValFuel U d i = true → E.gateValFuel V d i = true := by
    intro E U V hUV d
    induction d with
    | zero => intro i h; cases h
    | succ d ih =>
      intro i h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) = true at h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.leftVars i) (E.leftGates i) i (E.gateValFuel V d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.rightVars i) (E.rightGates i) i (E.gateValFuel V d)) = true
      rw [Bool.and_eq_true] at h ⊢
      constructor
      · have hL := h.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
      · have hR := h.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
  have gateVal_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ i : Fin E.size, E.gateVal U i = true → E.gateVal V i = true := by
    intro E U V hUV i h
    exact gateValFuel_mono E hUV E.size i h
  have eval_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → E.eval U = true → E.eval V = true := by
    intro E U V hUV h
    rw [eval_def] at h ⊢
    rw [decide_eq_true_eq] at h ⊢
    rcases h with h1 | h2
    · rcases h1 with ⟨v, hv, hu⟩
      exact Or.inl ⟨v, hv, hUV hu⟩
    · rcases h2 with ⟨j, hj, hv⟩
      exact Or.inr ⟨j, hj, gateVal_mono E hUV j hv⟩

  -- Part 2: Collapse Monotone2 C into a well-formed AndCountCircuit 26 D0
  let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  have wiresFrom_append : ∀ (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
    intro gs1 gs2 w; simp [wiresFrom, List.foldl_append]
  have wiresFrom_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
      refine ⟨v :: t, ?_, by simp [hl]⟩
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
      rw [hstep, ht]
      simp
  have length_wiresFrom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
    rw [ht, List.length_append, hl]
  have getD_wiresFrom_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
    intro gs w i h
    obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
    rw [ht, List.getD_append _ _ _ _ h]
  have getD_wiresFrom_take : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k i : ℕ),
      k ≤ gs.length →
      (wiresFrom (gs.take k) w).getD i false =
        if i < w.length + k then (wiresFrom gs w).getD i false else false := by
    intro gs w k i hk
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left hk]
    split_ifs with hi
    · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      conv_rhs => rw [hsplit, wiresFrom_append]
      exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
    · rw [List.getD_eq_default]
      omega
  have getD_wiresFrom_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ)
      (hk : k < gs.length),
      (wiresFrom gs w).getD (w.length + k) false =
        (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
          if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
    intro gs w k hk
    have hsplit : gs = gs.take k ++ gs[k]'hk :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
    have heq : wiresFrom gs w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++
            [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit, wiresFrom_append]
      rfl
    have hsnoc : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := fun l b => by simp
    rw [heq, getD_wiresFrom_lt]
    · conv_lhs => rw [← hlen, hsnoc]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
    · rw [List.length_append, hlen]; simp
  let T_and : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j : Fin C.gates.length => (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  let A_and : Finset ℕ := T_and.image Fin.val
  have hA_card : A_and.card = {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
    have h1 : A_and.card = T_and.card := Finset.card_image_of_injective T_and Fin.val_injective
    have h2 : (T_and : Set (Fin C.gates.length)) =
        {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
      ext j; simp [T_and]
    rw [h1, ← h2, Set.ncard_coe_finset]
  let k0 : ℕ := A_and.card
  let ord : Fin k0 ↪o ℕ := A_and.orderEmbOfFin rfl
  have memOrd : ∀ i : Fin k0, ord i ∈ A_and := fun i => A_and.orderEmbOfFin_mem rfl i
  have allAnd : ∀ (j : ℕ) (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ i : Fin k0, ord i = j := by
    intro j hj ha
    have hT : (⟨j, hj⟩ : Fin C.gates.length) ∈ T_and := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    have hA : j ∈ A_and := Finset.mem_image.mpr ⟨⟨j, hj⟩, hT, rfl⟩
    change j ∈ Set.range (A_and.orderEmbOfFin rfl)
    rwa [Finset.range_orderEmbOfFin]
  have okOrd : ∀ i : Fin k0, ∃ h : ord i < C.gates.length, C.gates[ord i].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    intro i
    obtain ⟨j, hjT, hjv⟩ := Finset.mem_image.mp (memOrd i)
    have hop := (Finset.mem_filter.mp hjT).2
    refine ⟨hjv ▸ j.isLt, ?_⟩
    simpa [← hjv] using hop
  let collVal (U : Finset (Fin 26)) (v : Fin k0 → Bool) (s : Finset (Fin 26) × Finset (Fin k0)) : Bool :=
    decide ((∃ x ∈ s.1, x ∈ U) ∨ ∃ i ∈ s.2, v i = true)
  let collCollect (L : List ℕ) (s : ℕ → Finset (Fin 26) × Finset (Fin k0)) : Finset (Fin 26) × Finset (Fin k0) :=
    (L.toFinset.biUnion (fun j => (s j).1), L.toFinset.biUnion (fun j => (s j).2))
  have collCollect_true : ∀ (U : Finset (Fin 26)) (v : Fin k0 → Bool) (L : List ℕ)
      (s : ℕ → Finset (Fin 26) × Finset (Fin k0)),
      collVal U v (collCollect L s) = true ↔ ∃ j ∈ L, collVal U v (s j) = true := by
    intro U v L s
    simp only [collVal, collCollect, decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨x, ⟨j, hjL, hxs⟩, hxU⟩
        exact ⟨j, hjL, Or.inl ⟨x, hxs, hxU⟩⟩
      · rcases h2 with ⟨i, ⟨j, hjL, his⟩, hvi⟩
        exact ⟨j, hjL, Or.inr ⟨i, his, hvi⟩⟩
    · intro h
      rcases h with ⟨j, hjL, hjv⟩
      rcases hjv with h1 | h2
      · rcases h1 with ⟨x, hxs, hxU⟩
        exact Or.inl ⟨x, ⟨j, hjL, hxs⟩, hxU⟩
      · rcases h2 with ⟨i, his, hvi⟩
        exact Or.inr ⟨i, ⟨j, hjL, his⟩, hvi⟩
  let collOrig (U : Finset (Fin 26)) (w : ℕ) : Bool :=
    (wiresFrom C.gates (List.ofFn (fun i : Fin 26 => decide (i ∈ U)))).getD w false
  have coll_gate : ∀ (U : Finset (Fin 26)) (j : ℕ) (h : j < C.gates.length),
      collOrig U (26 + j) = (C.gates[j]'h).op.eval ((C.gates[j]'h).inputs.map
        (fun i => if i < 26 + j then collOrig U i else false)) := by
    intro U j h
    simpa only [collOrig, List.length_ofFn] using
      getD_wiresFrom_gate C.gates (List.ofFn (fun i : Fin 26 => decide (i ∈ U))) j h
  let collV (U : Finset (Fin 26)) (j : Fin k0) : Bool := collOrig U (26 + ord j)
  have coll_prior : ∀ (w : ℕ),
      (∀ i < w, ∃ s : Finset (Fin 26) × Finset (Fin k0), (∀ j ∈ s.2, 26 + ord j ≤ i) ∧
        ∀ U : Finset (Fin 26), collVal U (collV U) s = collOrig U i) →
      ∃ f : ℕ → Finset (Fin 26) × Finset (Fin k0), (∀ i j, j ∈ (f i).2 → 26 + ord j < w) ∧
        ∀ i (U : Finset (Fin 26)), collVal U (collV U) (f i) = if i < w then collOrig U i else false := by
    intro w ih
    let f (i : ℕ) : Finset (Fin 26) × Finset (Fin k0) := if hi : i < w then (ih i hi).choose else (∅, ∅)
    refine ⟨f, ?_, ?_⟩
    · intro i j hj
      by_cases hi : i < w
      · simp only [f, dite_eq_left hi] at hj
        exact Nat.lt_of_le_of_lt ((ih i hi).choose_spec.1 _ hj) hi
      · simp [f, hi] at hj
    · intro i U
      by_cases hi : i < w
      · simpa only [f, dite_eq_left hi, ite_eq_left hi] using (ih i hi).choose_spec.2 U
      · simp [f, hi, collVal]
  have coll_wires : ∀ w : ℕ, ∃ s : Finset (Fin 26) × Finset (Fin k0),
      (∀ j ∈ s.2, 26 + ord j ≤ w) ∧ ∀ U : Finset (Fin 26), collVal U (collV U) s = collOrig U w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hinput : w < 26
      · let p : Fin 26 := ⟨w, hinput⟩
        refine ⟨({p}, ∅), by simp, ?_⟩
        intro U
        unfold collOrig
        rw [getD_wiresFrom_lt _ _ _ (by simpa using hinput)]
        rw [List.getD_eq_getElem _ _ (by simpa using hinput), List.getElem_ofFn]
        simp [collVal, p]
      let j := w - 26
      have hw : 26 + j = w := by dsimp [j]; omega
      by_cases hj : j < C.gates.length
      · obtain h | h := (hm C.gates[j] (List.getElem_mem hj)).1
        · obtain ⟨z, hz⟩ := allAnd j hj h
          exact ⟨(∅, {z}), by simp [hz, hw], fun U => by simp [collVal, collV, hz, hw]⟩
        · obtain ⟨f, hf, he⟩ := coll_prior w ih
          refine ⟨collCollect C.gates[j].inputs f, ?_, ?_⟩
          · intro z hz
            obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
            exact Nat.le_of_lt (hf i z hi)
          · intro U
            rw [← hw, coll_gate U j hj, show C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or from h]
            apply Bool.eq_iff_iff.mpr
            rw [collCollect_true]
            rw [op_or_eval]
            simp only [List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
            simp_rw [he, hw]
      · refine ⟨(∅, ∅), by simp, ?_⟩
        intro U
        unfold collOrig
        rw [List.getD_eq_default _ _ (by simp only [length_wiresFrom, List.length_ofFn]; omega)]
        simp [collVal]
  have coll_sides : ∀ i : Fin k0, ∃ l r : Finset (Fin 26) × Finset (Fin k0),
      (∀ z ∈ l.2, z < i) ∧ (∀ z ∈ r.2, z < i) ∧
      ∀ U : Finset (Fin 26), U.Nonempty →
        (collVal U (collV U) l && collVal U (collV U) r) = collV U i := by
    intro i
    obtain ⟨h, hop⟩ := okOrd i
    let g := C.gates[ord i]
    have hlen := (hm g (List.getElem_mem h)).2
    obtain ⟨f, hf, he⟩ := coll_prior (26 + ord i) (fun w _ => coll_wires w)
    have ltj : ∀ (a : ℕ) (z : Fin k0), z ∈ (f a).2 → z < i := fun a z hz =>
      ord.lt_iff_lt.mp (Nat.lt_of_add_lt_add_left (hf _ _ hz))
    have gate : ∀ U : Finset (Fin 26),
        collV U i = (g.inputs.map fun j => collVal U (collV U) (f j)).all id := by
      intro U
      dsimp only [collV]
      rw [coll_gate U (ord i) h, hop]
      rw [op_and_eval]; dsimp only [g]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (he a U).symm
    cases hL : g.inputs with
    | nil =>
      refine ⟨(Finset.univ, ∅), (Finset.univ, ∅), by simp, by simp, ?_⟩
      intro U hu
      rw [gate, hL]
      simpa [collVal] using (show ∃ x, x ∈ U from hu)
    | cons a L =>
      cases L with
      | nil =>
        refine ⟨f a, f a, ltj a, ltj a, ?_⟩
        intro U _
        simp [gate, hL]
      | cons b L =>
        have hem : L = [] := by rw [hL] at hlen; simpa using hlen
        subst L
        refine ⟨f a, f b, ltj a, ltj b, ?_⟩
        intro U _
        simp [gate, hL]
  choose lSide rSide hlSide hrSide hvSide using coll_sides
  obtain ⟨oSide, _, hoSide⟩ := coll_wires C.output
  let D0 : PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨k0, fun i => (lSide i).1, fun i => (lSide i).2,
         fun i => (rSide i).1, fun i => (rSide i).2, oSide.1, oSide.2⟩
  have hD0_size : D0.size = {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
    hA_card
  have hD0_wf : D0.WellFormed := fun i => ⟨hlSide i, hrSide i⟩
  have hD0_eval : ∀ U : Finset (Fin 26), U.Nonempty →
      D0.eval U = PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => Decidable.decide (k ∈ U)) := by
    intro U hU
    have fuel : ∀ (d : ℕ) (i : Fin k0), i.val < d → D0.gateValFuel U d i = collV U i := by
      intro d
      induction d with
      | zero => intro i h; omega
      | succ d ih =>
        intro i hd
        have eqSide : ∀ (s : Finset (Fin 26) × Finset (Fin k0)), (∀ z ∈ s.2, z < i) →
            PEqualNP.AndCount.AndCountCircuit.sideTrue U s.1 s.2 i (D0.gateValFuel U d) = collVal U (collV U) s := by
          intro s hs
          rw [sideTrue_def]; dsimp only [collVal]
          congr 1
          apply propext
          apply or_congr_right
          constructor
          · intro h1
            rcases h1 with ⟨j, hj, hji, hval⟩
            exact ⟨j, hj, (ih j (by have := hji; change j.val < i.val at this; omega)).symm.trans hval⟩
          · intro h1
            rcases h1 with ⟨j, hj, hval⟩
            have hji := hs j hj
            exact ⟨j, hj, hji, (ih j (by change j.val < i.val at hji; omega)).trans hval⟩
        change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (lSide i).1 (lSide i).2 i (D0.gateValFuel U d) &&
                PEqualNP.AndCount.AndCountCircuit.sideTrue U (rSide i).1 (rSide i).2 i (D0.gateValFuel U d)) = _
        rw [eqSide _ (hlSide i), eqSide _ (hrSide i), hvSide i U hU]
    have hgate : ∀ i : Fin k0, D0.gateVal U i = collV U i := fun i => fuel k0 i i.isLt
    have hev : D0.eval U = collOrig U C.output := by
      have h1 : D0.eval U = collVal U (collV U) oSide := by
        rw [eval_def]; simp only [hgate, collVal, D0]
      rw [h1, hoSide U]
    rw [hev]
    show (wiresFrom C.gates (List.ofFn fun i : Fin 26 => decide (i ∈ U))).getD C.output false =
         (C.wires (List.ofFn fun k : Fin 26 => Decidable.decide (k ∈ U))).getD C.output false
    rfl

  -- Part 3: stripCircuit on AndCountCircuit 26
  let stripCircuit (E : PEqualNP.AndCount.AndCountCircuit 26) : PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨E.size,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.leftVars i ∨ ∃ j ∈ E.leftGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.leftGates,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.rightVars i ∨ ∃ j ∈ E.rightGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.rightGates,
     Finset.univ.filter (fun v => v ∈ E.outVars ∨ ∃ j ∈ E.outGates, E.gateVal {v} j = true),
     E.outGates⟩
  have strip_wf : ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed → (stripCircuit E).WellFormed :=
    fun _ hw => hw
  have strip_disj : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (i : Fin (stripCircuit E).size),
      Disjoint ((stripCircuit E).leftVars i) ((stripCircuit E).rightVars i) := by
    intro E i
    rw [Finset.disjoint_left]
    intro v hL hR
    have hL' := (Finset.mem_filter.mp hL).2
    have hR' := (Finset.mem_filter.mp hR).2
    have hvL : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.leftVars i) (E.leftGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hL'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have hvR : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.rightVars i) (E.rightGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hR'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have htrue : E.gateVal {v} i = true := by
      rw [gateVal_eq E {v} i, hvL, hvR]; rfl
    rw [hL'.2] at htrue
    cases htrue
  have strip_gateVal_le : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → (stripCircuit E).gateVal U i = true → E.gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true] at hval
      rw [gateVal_eq E U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
      · have hR := hval.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
  have strip_gateVal_ge : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → E.gateVal U i = true →
      (∃ v ∈ U, E.gateVal {v} i = true) ∨ (stripCircuit E).gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      by_cases hsing : ∃ v ∈ U, E.gateVal {v} i = true
      · exact Or.inl hsing
      · right
        have hno : ∀ v ∈ U, E.gateVal {v} i = false := fun v hvU =>
          Bool.eq_false_iff.mpr (fun hv => hsing ⟨v, hvU, hv⟩)
        rw [gateVal_eq E U i, Bool.and_eq_true] at hval
        rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true]
        constructor
        · have hL := hval.1
          rw [sideTrue_def] at hL ⊢
          rw [decide_eq_true_eq] at hL ⊢
          rcases hL with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
        · have hR := hval.2
          rw [sideTrue_def] at hR ⊢
          rw [decide_eq_true_eq] at hR ⊢
          rcases hR with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
  have strip_eval_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      (stripCircuit E).eval U = E.eval U := by
    intro E U
    rw [eval_def, eval_def]
    refine decide_eq_decide.mpr ?_
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        rcases (Finset.mem_filter.mp hvO).2 with hvC | hjs
        · exact Or.inl ⟨v, hvC, hvU⟩
        · rcases hjs with ⟨j, hjO, hvs⟩
          exact Or.inr ⟨j, hjO, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, strip_gateVal_le E U E.size j j.isLt hjv⟩
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvO⟩, hvU⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        rcases strip_gateVal_ge E U E.size j j.isLt hjv with h3 | hj'
        · rcases h3 with ⟨v, hvU, hvs⟩
          exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjO, hvs⟩⟩, hvU⟩
        · exact Or.inr ⟨j, hjO, hj'⟩
  have strip_gateVal_singleton : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (i : Fin (stripCircuit E).size) (v : Fin 26), (stripCircuit E).gateVal {v} i = false := by
    intro E i v
    induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin E.size → Fin E.size → Prop)).induction with
    | h i ih =>
      rw [Bool.eq_false_iff]
      intro htrue
      rw [gateVal_eq (stripCircuit E) {v} i, Bool.and_eq_true] at htrue
      have getL : v ∈ (stripCircuit E).leftVars i := by
        have hL := htrue.1
        rw [sideTrue_def] at hL
        rw [decide_eq_true_eq] at hL
        rcases hL with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      have getR : v ∈ (stripCircuit E).rightVars i := by
        have hR := htrue.2
        rw [sideTrue_def] at hR
        rw [decide_eq_true_eq] at hR
        rcases hR with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      exact Finset.disjoint_left.mp (strip_disj E i) getL getR
  have strip_exists : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∃ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.size = E.size ∧ D.WellFormed ∧
        (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) ∧
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) ∧
        (∀ U, D.eval U = E.eval U) :=
    fun E hw => ⟨stripCircuit E, rfl, strip_wf E hw, strip_disj E, strip_gateVal_singleton E, strip_eval_eq E⟩

  let inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let liftRow (P : Finset (Fin 13)) : Finset (Fin 26) :=
    Finset.univ.filter fun k : Fin 26 =>
      (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ inc q l
  -- Transfer both prescribed input families to the stripped circuit.
  obtain ⟨D, hD_sz0, hD_wf, hD_disj, hD_sing, hD_ev0⟩ := strip_exists D0 hD0_wf
  have hD_pos : ∀ p l : Fin 13, inc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true := by
    intro p l hinc
    rw [hD_ev0, hD0_eval _ (Finset.insert_nonempty _ _)]
    have hp := hPos p l hinc
    refine Eq.trans ?_ hp
    congr 1; funext k
    exact decide_eq_decide.mpr (by simp only [Finset.mem_insert, Finset.mem_singleton])
  have hD_neg : ∀ P : Finset (Fin 13),
      (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ inc q l) ∧ inc p l) →
      ((¬∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ inc q l) → inc p l) →
      D.eval (liftRow P) = false := by
    intro P hmx hgen
    have hne : (liftRow P).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      have hP0 : P = ∅ := by
        ext p; simp only [Finset.notMem_empty, iff_false]
        intro hp
        have hm : Fin.castAdd 13 p ∈ liftRow P :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, hp, rfl⟩⟩
        rw [hem] at hm; exact Finset.notMem_empty _ hm
      exact hgen.1 ⟨0, fun p hp => by rw [hP0] at hp; exact (Finset.notMem_empty _ hp).elim⟩
    rw [hD_ev0, hD0_eval _ hne]
    have hn := hNeg P hmx hgen
    refine Eq.trans ?_ hn
    congr 1; funext k
    exact decide_eq_decide.mpr (by simp only [liftRow, inc, Finset.mem_filter, Finset.mem_univ, true_and])
  obtain ⟨hD_outVars, hD_ge11, hD_degAll, hD_pairPL, hD_pairSame⟩ :=
    hLadder D hD_wf hD_disj hD_pos hD_neg
  have hD_eq_ncard : D.size = {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
    hD_sz0.trans hD0_size
  rw [← hD_eq_ncard]
  by_contra! hlt13
  have casesSize : D.size = 11 ∨ D.size = 12 := by omega
  rcases casesSize with h11 | h12
  · exact hSize11 D hD_wf h11 hD_outVars hD_sing hD_disj hD_pos hD_neg
      (fun v => by have := hD_degAll v; dsimp only at this ⊢; omega)
      (fun p l h => by have := hD_pairPL p l h; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).1; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).2; dsimp only at this ⊢; omega)
  · exact hSize12 D hD_wf h12 hD_outVars hD_sing hD_disj hD_pos hD_neg
      (fun v => by have := hD_degAll v; dsimp only at this ⊢; omega)
      (fun p l h => by have := hD_pairPL p l h; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).1; dsimp only at this ⊢; omega)
      (fun p q h => by have := (hD_pairSame p q h).2; dsimp only at this ⊢; omega)
