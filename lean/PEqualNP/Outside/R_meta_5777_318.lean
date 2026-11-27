import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.GenericRejection

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_5777_318
    (transport : ∀ (n : ℕ) (C : Circuit) (e : Equiv.Perm (Fin n)), IsAO2 n C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → ∃ D : Circuit,
        D.size = C.size ∧ IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e))) ∧
        ∀ i : Fin n, D.lineDeg n {(e i).val} = C.lineDeg n {i.val})
    (origin : have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4;
      ∀ D : Circuit, D.size ≤ 27 → IsAO2 14 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
        2 ≤ D.lineDeg 14 {0} → 2 ≤ D.lineDeg 14 {7} →
        ∃ F : DMFormula 14, x2 F ∧ F.leaves ≤ 28 ∧
          (∀ x, F.eval x = D.eval (List.ofFn x)) ∧ 2 ≤ x3 0 F ∧ 2 ≤ x3 7 F) :
    have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x4.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 → (∀ x9 ∈ x4.gates, x9.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x4 → x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x14 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x14 ∧ x14.leaves ≤ (28 : ℕ) ∧ (∀ (x15 : Fin (14 : ℕ) → Bool), x14.eval x15 = x4.eval (List.ofFn x15)) ∧ (2 : ℕ) ≤ x3 (↑x5) x14 ∧ (2 : ℕ) ≤ x3 ((7 : ℕ) + ↑x6) x14 := by
  intro node normal weight C p l size ao nd comp inc hp hl
  have symmetries : ∀ p l : Fin 7, p ∈ fanoLines l → ∃ a : Fin 7,
      (∀ i j : Fin 7, a*i=a*j → i=j) ∧ ∀ u v : Fin 7,
        (a*(u-p) ∈ fanoLines (a*(v-l))) ↔ u ∈ fanoLines v := by
    decide +kernel
  obtain ⟨a,inj,edges⟩ := symmetries p l inc
  have bij (k : Fin 7) : Function.Bijective (fun i : Fin 7 => a*(i-k)) := by
    apply Finite.injective_iff_bijective.mp
    intro i j eq
    have h : i-k=j-k := inj _ _ eq
    simpa using congrArg (fun t : Fin 7 => t+k) h
  let P := Equiv.ofBijective _ (bij p)
  let L := Equiv.ofBijective _ (bij l)
  let splitE : Fin 7 ⊕ Fin 7 ≃ Fin 14 := finSumFinEquiv
  let e := splitE.symm.trans ((Equiv.sumCongr P L).trans splitE)
  have point (u : Fin 7) : e (Fin.castAdd 7 u) = Fin.castAdd 7 (P u) := by
    change splitE ((Equiv.sumCongr P L) (splitE.symm (Fin.castAdd 7 u))) = _
    rw [show splitE.symm (Fin.castAdd 7 u) = Sum.inl u from splitE.symm_apply_apply (.inl u)]
    rfl
  have line (v : Fin 7) : e (Fin.natAdd 7 v) = Fin.natAdd 7 (L v) := by
    change splitE ((Equiv.sumCongr P L) (splitE.symm (Fin.natAdd 7 v))) = _
    rw [show splitE.symm (Fin.natAdd 7 v) = Sum.inr v from splitE.symm_apply_apply (.inr v)]
    rfl
  have on (u v : Fin 7) : P u ∈ fanoLines (L v) ↔ u ∈ fanoLines v := edges u v
  have p0 : P p = 0 := by change a*(p-p)=0; simp
  have l0 : L l = 0 := by change a*(l-l)=0; simp
  obtain ⟨D,ds,dao,dn,ev,deg⟩ := transport 14 C e ao nd
  have spec (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 7, u ∈ fanoLines v ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 v) = true := by
    let X := Finset.univ.filter fun u : Fin 7 => x (Fin.castAdd 7 u) = true
    let Y := Finset.univ.filter fun v : Fin 7 => x (Fin.natAdd 7 v) = true
    have bits : incidenceInput X Y = List.ofFn x := by
      change List.ofFn (fun u : Fin 7 => decide (u ∈ X)) ++
        List.ofFn (fun v : Fin 7 => decide (v ∈ Y)) = List.ofFn x
      rw [← List.ofFn_fin_append]
      congr 1
      funext i
      refine Fin.addCases (fun u => ?_) (fun v => ?_) i
      · rw [Fin.append_left]; simp [X]
      · rw [Fin.append_right]; simp [Y]
    rw [← bits,comp X Y]
    change decide (∃ u ∈ X, ∃ v ∈ Y, u ∈ fanoLines v) = true ↔ _
    simp only [decide_eq_true_eq,X,Y,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨u,hu,v,hv,h⟩; exact ⟨u,v,h,hu,hv⟩
    · rintro ⟨u,v,h,hu,hv⟩; exact ⟨u,hu,v,hv,h⟩
  have dspe (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 7, u ∈ fanoLines v ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 v) = true := by
    rw [ev,spec]
    constructor
    · rintro ⟨u,v,h,hu,hv⟩
      exact ⟨P u,L v,(on _ _).mpr h,by simpa only [Function.comp_apply,point] using hu,
        by simpa only [Function.comp_apply,line] using hv⟩
    · rintro ⟨u,v,h,hu,hv⟩
      refine ⟨P.symm u,L.symm v,(on _ _).mp (by simpa using h),?_,?_⟩
      · simpa only [Function.comp_apply,point,Equiv.apply_symm_apply] using hu
      · simpa only [Function.comp_apply,line,Equiv.apply_symm_apply] using hv
  have ep : (e (Fin.castAdd 7 p)).val = 0 := by rw [point,p0]; rfl
  have el : (e (Fin.natAdd 7 l)).val = 7 := by rw [line,l0]; rfl
  have dp := deg (Fin.castAdd 7 p)
  have dl := deg (Fin.natAdd 7 l)
  rw [ep] at dp
  rw [el] at dl
  obtain ⟨F,hF,sz,vF,d0,d7⟩ := origin D (ds.trans_le size) dao dn dspe
    (by rw [dp]; exact hp) (by rw [dl]; exact hl)
  let rename : DMFormula 14 → DMFormula 14 := DMFormula.rec
    (fun i b => DMFormula.lit (e.symm i) b) (fun _ _ A B => DMFormula.and A B)
    (fun _ _ A B => DMFormula.or A B)
  have lit (A : DMFormula 14) (i : Fin 14) : rename A = .lit i true ↔ A = .lit (e i) true := by
    cases A with
    | lit j b =>
      change DMFormula.lit (e.symm j) b = .lit i true ↔ DMFormula.lit j b = .lit (e i) true
      simp [Equiv.symm_apply_eq]
    | and A B => simp [rename]
    | or A B => simp [rename]
  have norm (A : DMFormula 14) : normal A → normal (rename A) := by
    induction A with
    | lit i b => exact id
    | and A B iA iB | or A B iA iB =>
      rintro ⟨hA,hB,neq⟩
      refine ⟨iA hA,iB hB,?_⟩
      rintro ⟨i,hi,hj⟩
      exact neq ⟨e i,(lit A i).mp hi,(lit B i).mp hj⟩
  have lens (A : DMFormula 14) : (rename A).leaves = A.leaves := by
    induction A with
    | lit i b => rfl
    | and A B iA iB | or A B iA iB => exact congrArg₂ Nat.add iA iB
  have vals (A : DMFormula 14) (x : Fin 14 → Bool) :
      (rename A).eval x = A.eval (x ∘ e.symm) := by
    induction A with
    | lit i b => rfl
    | and A B iA iB => exact congrArg₂ Bool.and iA iB
    | or A B iA iB => exact congrArg₂ Bool.or iA iB
  have w (A : DMFormula 14) (i : Fin 14) : weight i.val (rename A) = weight (e i).val A := by
    induction A with
    | lit j b =>
      change (if (e.symm j).val=i.val then 1 else 0 : ℕ) = (if j.val=(e i).val then 1 else 0)
      simp [Fin.val_inj,Equiv.symm_apply_eq]
    | and A B iA iB => exact congrArg₂ Nat.add iA iB
    | or A B iA iB => exact congrArg₂ max iA iB
  refine ⟨rename F,norm _ hF,(lens F).trans_le sz,?_,?_,?_⟩
  · intro x
    rw [vals,vF,ev]
    simp [Function.comp_def]
  · change 2 ≤ weight (Fin.castAdd 7 p).val (rename F)
    rw [w,ep]
    exact d0
  · change 2 ≤ weight (Fin.natAdd 7 l).val (rename F)
    rw [w,el]
    exact d7

