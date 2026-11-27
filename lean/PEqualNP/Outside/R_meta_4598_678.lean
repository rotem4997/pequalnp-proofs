import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_4598_678 :
  (∀ (N : ℕ) (E : Finset (Fin N × Fin N)),
    (∀ p r l m : Fin N, p ≠ r → l ≠ m →
      ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E)) →
    min (E.image Prod.fst).card (E.image Prod.snd).card ≤ 2208 →
    E.card ≤ 24 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1)) →
  (∀ (n : ℕ) (C : Circuit) (S : Finset (Fin n)),
    IsAO2 n C →
    (∀ i ∈ S, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) →
    S.card ≤ C.size + 1) →
  (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (E : Finset (Fin N × Fin N)),
    87 ≤ q → N = q^2 + q + 1 →
    (∀ l, Fintype.card {p // I p l} = q + 1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    IsAO2 (N+N) C →
    (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N+N) C z = false) →
    let hits := fun (v : Fin (N+N)) (e : Fin N × Fin N) =>
      v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
    (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun i => decide (hits i e)) = true ∧
      lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
      lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
    (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) →
    2208 < min (E.image Prod.fst).card (E.image Prod.snd).card →
    24 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) < E.card →
    E.card ≤ 24 * C.size) →
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →               let x13 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2;               (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) → (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) → (4400 : ℕ) < x5.size → x6.card ≤ (24 : ℕ) * x5.size := by
  intro small support large q N I inst C E hq hn hreg huniq hao sound hits good dense hsize
  classical
  let P := E.image Prod.fst
  let L := E.image Prod.snd
  let V := P.image (Fin.castAdd N) ∪ L.image (Fin.natAdd N)
  have diff (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    have := p.isLt
    omega
  have single (v : Fin (N+N)) : circuitFun (N+N) C (fun i => decide (i=v)) = false := by
    apply sound
    · apply Nat.le_trans _ (show 1 ≤ q by omega)
      rw [Fintype.card_subtype]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' : Fin.natAdd N a = v := by simpa using (Finset.mem_filter.mp ha).2
      have hb' : Fin.natAdd N b = v := by simpa using (Finset.mem_filter.mp hb).2
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha'.trans hb'.symm)))
    · rintro ⟨p,l,_,hp,hl⟩
      exact diff p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  have both (e : Fin N × Fin N) (he : e ∈ E) :
    circuitFun (N+N) C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true :=
    (good e he).2.1
  have hv : V.card ≤ C.size + 1 := by
    apply support _ C V hao
    intro v hm
    rcases Finset.mem_union.mp hm with hp | hl
    · obtain ⟨p,hp',rfl⟩ := Finset.mem_image.mp hp
      change p ∈ E.image Prod.fst at hp'
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp'
      refine ⟨fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2),
        fun i => decide (i = Fin.natAdd N e.2), ?_, ?_⟩
      · intro j hj
        simp only [hj,false_or]
      · rw [both e he, single]
        decide
    · obtain ⟨l,hl',rfl⟩ := Finset.mem_image.mp hl
      change l ∈ E.image Prod.snd at hl'
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl'
      refine ⟨fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2),
        fun i => decide (i = Fin.castAdd N e.1), ?_, ?_⟩
      · intro j hj
        simp only [hj,or_false]
      · rw [both e he, single]
        decide
  have hd : Disjoint (P.image (Fin.castAdd N)) (L.image (Fin.natAdd N)) := by
    apply Finset.disjoint_left.mpr
    intro v hp hl
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hl
    exact diff p l hl.symm
  have cast_inj : Function.Injective (Fin.castAdd N : Fin N → Fin (N+N)) :=
    fun _ _ h => Fin.ext (congrArg (fun i : Fin (N+N) => i.val) h)
  have add_inj : Function.Injective (Fin.natAdd N : Fin N → Fin (N+N)) :=
    fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Fin (N+N) => i.val) h))
  change (P.image (Fin.castAdd N) ∪ L.image (Fin.natAdd N)).card ≤ C.size + 1 at hv
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ cast_inj,
    Finset.card_image_of_injective _ add_inj] at hv
  have nor : ∀ p r l m : Fin N, p ≠ r → l ≠ m →
      ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E) := by
    rintro p r l m hpr hlm ⟨a,b,c,d⟩
    obtain ⟨k,_,hk⟩ := huniq p r hpr
    exact hlm ((hk l ⟨(good _ a).1, (good _ b).1⟩).trans
      (hk m ⟨(good _ c).1, (good _ d).1⟩).symm)
  by_cases hsp : E.card ≤ 24 * (P.card + L.card - 1)
  · omega
  have hmin : 2208 < min P.card L.card := by
    by_contra! hh
    exact hsp (small N E nor hh)
  exact large q N I C E hq hn hreg huniq hao sound good dense hmin (Nat.lt_of_not_ge hsp)