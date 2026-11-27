import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover

-- Normalize the two exclusive flags under incidence-preserving point and line permutations.
-- The five positions have the same point, the same line, one cross incidence in either direction, or neither.
theorem PEqualNP.Outside.R_meta_5202_7
  (geometry : let P := singerLines3
    ∀ p l q m : Fin 13, p ∈ P l → q ∈ P m → (p,l) ≠ (q,m) →
    ∃ s t : Equiv.Perm (Fin 13), s p = 0 ∧ t l = 0 ∧
      (s q,t m) ∈ ([(0,4),(1,0),(1,1),(2,1),(2,12)] : List (Fin 13 × Fin 13)) ∧
      (∀ i j, s i ∈ P (t j) ↔ i ∈ P j) ∧
      ∀ Q, IsQuadrangle P Q → IsQuadrangle P (Q.image s.symm) ∧
        missLines P (Q.image s.symm) = (missLines P Q).image t.symm)
  (relabel : let X := fun (A B : Finset (Fin 13)) =>
      (List.ofFn fun i : Fin 13 => decide (i ∈ A)) ++ List.ofFn fun i : Fin 13 => decide (i ∈ B)
    let nested := fun (C : Circuit) (j : ℕ) => (gateAt C j).op = .and ∧
      ∃ i ∈ (gateAt C j).inputs, 26 ≤ i ∧ (gateAt C (i-26)).op = .and
    ∀ (C : Circuit) (s t : Equiv.Perm (Fin 13)), Monotone2 C → ReadsBack 26 C →
    ∃ (D : Circuit) (f : ℕ → ℕ), D.size = C.size ∧ Monotone2 D ∧ ReadsBack 26 D ∧
      (∀ r < 26+C.size, f r < 26+D.size) ∧ (∀ j, nested C j → nested D j) ∧
      ∀ r A B, (D.wires (X A B)).getD (f r) false =
        (C.wires (X (A.image s.symm) (B.image t.symm))).getD r false)
  (canonical : let P := singerLines3
    let X := fun (A B : Finset (Fin 13)) =>
      (List.ofFn fun i : Fin 13 => decide (i ∈ A)) ++ List.ofFn fun i : Fin 13 => decide (i ∈ B)
    let nested := fun (C : Circuit) (j : ℕ) => (gateAt C j).op = .and ∧
      ∃ i ∈ (gateAt C j).inputs, 26 ≤ i ∧ (gateAt C (i-26)).op = .and
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C → max a b < 26+C.size →
    let sig := fun A B => let w := C.wires (X A B); (w.getD a false, w.getD b false)
    (∀ p l, p ∈ P l → sig {p} {l} ≠ (false,false)) →
    (∀ Q, IsQuadrangle P Q → sig Q (missLines P Q) = (false,false)) →
    sig {0} {0} = (true,false) →
    (∃ z ∈ ([(0,4),(1,0),(1,1),(2,1),(2,12)] : List (Fin 13 × Fin 13)), sig {z.1} {z.2} = (false,true)) →
    (∃ i j k : Fin C.size, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ nested C i ∧ nested C j ∧ nested C k) → 63 ≤ C.size)
  : have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∃ x18 ∈ Finset.range x7.size, ∃ x19 ∈ Finset.range x7.size, ∃ x20 ∈ Finset.range x7.size, x18 ≠ x19 ∧ x18 ≠ x20 ∧ x19 ≠ x20 ∧ x6 x7 x18 ∧ x6 x7 x19 ∧ x6 x7 x20) → (63 : ℕ) ≤ x7.size := by
  dsimp only at geometry relabel canonical ⊢
  intro C a b mono back ha hb cover reject first second three
  obtain ⟨p,l,pl,ap,bp⟩ := first
  obtain ⟨q,m,qm,bq,aq⟩ := second
  have separate : (p,l) ≠ (q,m) := by
    rintro e; obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    exact (by decide : true ≠ false) (ap.symm.trans aq)
  obtain ⟨s,t,sp,tl,orbit,inc,quad⟩ := geometry p l q m pl qm separate
  obtain ⟨D,f,size,monoD,backD,rangeF,preserve,values⟩ := relabel C s t mono back
  rw [← size]
  apply canonical D (f a) (f b) monoD backD (max_lt (rangeF a ha) (rangeF b hb))
  · intro i j ij
    have old := (inc (s.symm i) (t.symm j)).mp (by simpa using ij)
    rcases cover (s.symm i) (t.symm j) old with u|v
    · intro both
      have off := congrArg Prod.fst both
      simp only [values, Finset.image_singleton] at off
      exact (by decide : true ≠ false) (u.symm.trans off)
    · intro both
      have off := congrArg Prod.snd both
      simp only [values, Finset.image_singleton] at off
      exact (by decide : true ≠ false) (v.symm.trans off)
  · intro Q hQ
    obtain ⟨hQ', miss⟩ := quad Q hQ
    obtain ⟨ua,ub⟩ := reject (Q.image s.symm) hQ'
    apply Prod.ext <;> simp only [values, ← miss] <;> assumption
  · have marked (r : ℕ) := values r {s p} {t l}
    simp only [Finset.image_singleton, Equiv.symm_apply_apply] at marked
    rw [sp,tl] at marked
    apply Prod.ext <;> simp only [marked] <;> assumption
  · refine ⟨(s q,t m), orbit, ?_⟩
    apply Prod.ext <;> simp only [values, Finset.image_singleton, Equiv.symm_apply_apply] <;> assumption
  · obtain ⟨i,hi,j,hj,k,hk,ij,ik,jk,ni,nj,nk⟩ := three
    simp only [Finset.mem_range] at hi hj hk
    refine ⟨⟨i,size ▸ hi⟩,⟨j,size ▸ hj⟩,⟨k,size ▸ hk⟩,?_,?_,?_,preserve i ni,preserve j nj,preserve k nk⟩
    · exact fun h => ij (congrArg Fin.val h)
    · exact fun h => ik (congrArg Fin.val h)
    · exact fun h => jk (congrArg Fin.val h)
