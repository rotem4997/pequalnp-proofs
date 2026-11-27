import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Strip whole star components and charge each removed star to its essential inputs.
-- The dependency count for a single star follows R_meta_3491_473.
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_3241_673
    (pin : ∀ (n : ℕ) (C : Circuit) (S : Finset (Fin n)), IsAO2 n C →
      (∀ v ∈ S, ∃ x y : Fin n → Bool, (∀ j, j ≠ v → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      let zero (x : Fin n → Bool) (v : Fin n) := if v ∈ S then false else x v
      (∃ x y, circuitFun n C (zero x) ≠ circuitFun n C (zero y)) →
      ∃ D : Circuit, IsAO2 n D ∧ D.size + S.card ≤ C.size ∧
        ∀ x, circuitFun n D x = circuitFun n C (zero x))
    (core : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      let ends (F : Finset (Fin n × Fin m)) :=
        F.biUnion (fun e => {Fin.castAdd m e.1, Fin.natAdd n e.2})
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n + m) C →
      (∀ z, circuitFun (n + m) C z = decide (∃ e ∈ E,
        z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)) →
      (¬ ∃ (F H : Finset (Fin n × Fin m)) (v : Fin (n + m)),
        F.Nonempty ∧ F ∪ H = E ∧ Disjoint (ends F) (ends H) ∧
          ∀ e ∈ F, Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧
        E.card + A.card + B.card ≤ C.size + 1)
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ own : List (ℕ × List ℕ),
        (∀ s ∈ own, s.2 ≠ [] ∧ ((s.1 < n ∧ ∀ t ∈ s.2, n ≤ t ∧ t < n + m) ∨
          (n ≤ s.1 ∧ s.1 < n + m ∧ ∀ t ∈ s.2, t < n))) ∧
        (∀ p : Fin n, ∀ l : Fin m, (p,l) ∈ E ↔ ∃ s ∈ own,
          (s.1 = p.val ∧ n + l.val ∈ s.2) ∨ (s.1 = n + l.val ∧ p.val ∈ s.2)) ∧
        (own.map (fun s => s.2.length)).sum + own.length - 1 ≤ E.card + A.card + B.card - 1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   let x6 : ℕ := x1 + x2;   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 x6 x5 → (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size := by
  classical
  let run (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have other (x : List Bool) (b : Bool) (i : ℕ) (h : i ≠ x.length) :
      (x ++ [b]).getD i false = x.getD i false := by
    by_cases lt : i < x.length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have cone (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
      (n : ℕ) (T : Finset ℕ) :
      ∃ S : Finset ℕ, S.card ≤ T.card + gs.length ∧
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ j ∈ T, (run gs x).getD j false = (run gs y).getD j false := by
    induction gs generalizing n T with
    | nil => exact ⟨T,by simp,fun _ _ _ _ h => h⟩
    | cons g gs ih =>
      obtain ⟨S,small,protect⟩ := ih (fun u hu => arity u (by simp [hu])) (n+1) T
      let value (x : List Bool) := g.op.eval (g.inputs.map fun i => x.getD i false)
      by_cases used : n ∈ S
      · let R := S.erase n ∪ g.inputs.toFinset
        refine ⟨R,?_,?_⟩
        · have h := Finset.card_union_le (S.erase n) g.inputs.toFinset
          have ea := Finset.card_erase_add_one used
          have inputs := List.toFinset_card_le g.inputs
          have two := arity g (by simp)
          change (S.erase n ∪ g.inputs.toFinset).card ≤ T.card + (g :: gs).length
          simp only [List.length_cons]
          omega
        · intro x y hx hy agree
          apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
          intro j hj
          by_cases split : j = n
          · subst j
            have val : value x = value y := by
              apply congrArg g.op.eval
              apply List.map_congr_left
              intro i hi
              exact agree i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
            have atEnd (z : List Bool) (b : Bool) : (z ++ [b]).getD z.length false = b := by simp
            calc
              (x ++ [value x]).getD n false = value x := hx ▸ atEnd x _
              _ = value y := val
              _ = (y ++ [value y]).getD n false := hy ▸ (atEnd y _).symm
          · rw [other x _ j (by omega),other y _ j (by omega)]
            exact agree j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨split,hj⟩))
      · refine ⟨S,by simp only [List.length_cons]; omega,?_⟩
        intro x y hx hy agree
        apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
        intro j hj
        have diff : j ≠ n := fun h => used (h ▸ hj)
        rw [other x _ j (by omega),other y _ j (by omega)]
        exact agree j hj

  have essentialInputs (n : ℕ) (C : Circuit) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
      (A : Finset (Fin n))
      (essential : ∀ i ∈ A, ∃ x y : Fin n → Bool,
        (∀ j, j ≠ i → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
      A.card ≤ C.size + 1 := by
    obtain ⟨S,hs,protect⟩ := cone C.gates arity n {C.output}
    have subset : A.image Fin.val ⊆ S := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      by_contra notin
      obtain ⟨x,y,agree,changeVal⟩ := essential i hi
      apply changeVal
      apply protect (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
      intro k hk
      by_cases h : k < n
      · rw [List.getD_eq_getElem (List.ofFn x) _ (by simpa using h),List.getD_eq_getElem (List.ofFn y) _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        exact agree ⟨k,h⟩ (fun e => notin ((congrArg Fin.val e) ▸ hk))
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
    have ci := Finset.card_le_card subset
    rw [Finset.card_image_of_injective _ Fin.val_injective] at ci
    simp only [Finset.card_singleton] at hs
    change A.card ≤ C.gates.length + 1
    omega
  intro n m I _ C
  dsimp only
  intro square ao correct
  let L (p : Fin n) := Fin.castAdd m p
  let R (l : Fin m) := Fin.natAdd n l
  let edges : Finset (Fin n × Fin m) := Finset.univ.filter (fun e => I e.1 e.2)
  let pair (e : Fin n × Fin m) : Finset (Fin (n + m)) := {L e.1, R e.2}
  let ends (F : Finset (Fin n × Fin m)) := F.biUnion pair
  let cover (E : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)) :=
    ∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B
  let noSquare (E : Finset (Fin n × Fin m)) := ∀ p q l s, p ≠ q → l ≠ s →
    ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)
  let target (E : Finset (Fin n × Fin m)) (z : Fin (n+m) → Bool) : Bool :=
    decide (∃ e ∈ E, z (L e.1) = true ∧ z (R e.2) = true)
  have sep (p : Fin n) (l : Fin m) : L p ≠ R l := by
    intro eq
    have val := congrArg Fin.val eq
    change p.val = n + l.val at val
    omega
  have left (F : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (he : e ∈ F) : L e.1 ∈ ends F :=
    Finset.mem_biUnion.mpr ⟨e, he, by simp [pair]⟩
  have right (F : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (he : e ∈ F) : R e.2 ∈ ends F :=
    Finset.mem_biUnion.mpr ⟨e, he, by simp [pair]⟩
  have dependent (E F : Finset (Fin n × Fin m)) (hsub : F ⊆ E) (C : Circuit)
      (hC : ∀ z, circuitFun (n+m) C z = target E z) :
      ∀ v ∈ ends F, ∃ x y : Fin (n+m) → Bool, (∀ j, j ≠ v → x j = y j) ∧
        circuitFun (n+m) C x ≠ circuitFun (n+m) C y := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    have onPair : circuitFun (n+m) C (fun j => decide (j ∈ pair e)) = true := by
      rw [hC]
      simp only [target, decide_eq_true_eq]
      exact ⟨e, hsub he, by simp [pair], by simp [pair]⟩
    have offSingle (w : Fin (n+m)) : circuitFun (n+m) C (fun j => decide (j = w)) = false := by
      rw [hC]
      simp only [target, decide_eq_false_iff_not]
      rintro ⟨f, _, hL, hR⟩
      exact sep f.1 f.2 ((of_decide_eq_true hL).trans (of_decide_eq_true hR).symm)
    have chooseRow (u w : Fin (n+m)) (hpair : pair e = {u,w}) :
        ∃ x y : Fin (n+m) → Bool, (∀ j, j ≠ u → x j = y j) ∧
          circuitFun (n+m) C x ≠ circuitFun (n+m) C y := by
      refine ⟨fun j => decide (j ∈ pair e), fun j => decide (j = w), ?_, ?_⟩
      · intro j hj
        simp [hpair, hj]
      · rw [onPair, offSingle]
        decide
    rcases (show v = L e.1 ∨ v = R e.2 by simpa [pair] using hve) with rfl | rfl
    · exact chooseRow _ _ rfl
    · exact chooseRow _ _ (Finset.pair_comm ..)
  have centerCard (F : Finset (Fin n × Fin m)) (v : Fin (n+m)) (hF : F.Nonempty)
      (center : ∀ e ∈ F, L e.1 = v ∨ R e.2 = v) : F.card + 1 ≤ (ends F).card := by
    obtain ⟨e₀, he₀⟩ := hF
    have main := (center e₀ he₀).elim (fun h => h ▸ left F e₀ he₀) (fun h => h ▸ right F e₀ he₀)
    let opposite (e : Fin n × Fin m) := if L e.1 = v then R e.2 else L e.1
    have otherIn (e : Fin n × Fin m) (he : e ∈ F) : opposite e ∈ (ends F).erase v := by
      rcases center e he with l | r
      · have nr : R e.2 ≠ v := fun h => sep _ _ (l.trans h.symm)
        simpa [opposite, l] using Finset.mem_erase.mpr ⟨nr, right F e he⟩
      · have nl : L e.1 ≠ v := fun h => sep _ _ (h.trans r.symm)
        simpa [opposite, nl] using Finset.mem_erase.mpr ⟨nl, left F e he⟩
    have leftInj : Function.Injective L := by
      intro a b h
      exact Fin.ext (congrArg (fun z : Fin (n+m) => z.val) h)
    have rightInj : Function.Injective R := by
      intro a b h
      apply Fin.ext
      have val := congrArg Fin.val h
      change n + a.val = n + b.val at val
      omega
    have inj : Set.InjOn opposite (F : Set (Fin n × Fin m)) := by
      intro e he f hf same
      by_cases le : L e.1 = v <;> by_cases lf : L f.1 = v <;> simp only [opposite,le,lf,↓reduceIte] at same
      · exact Prod.ext (leftInj (le.trans lf.symm)) (rightInj same)
      · exact (sep f.1 e.2 same.symm).elim
      · exact (sep e.1 f.2 same).elim
      · exact Prod.ext (leftInj same) (rightInj (((center e he).resolve_left le).trans
          ((center f hf).resolve_left lf).symm))
    have sz := Finset.card_le_card (show F.image opposite ⊆ (ends F).erase v by
      intro j hj
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
      exact otherIn e he)
    rw [Finset.card_image_of_injOn inj] at sz
    have := Finset.card_erase_add_one main
    omega
  have addCenter (F H : Finset (Fin n × Fin m)) (v : Fin (n+m))
      (center : ∀ e ∈ F, L e.1 = v ∨ R e.2 = v) (A : Finset (Fin n)) (B : Finset (Fin m))
      (hcov : cover H A B) : ∃ A' B', cover (F ∪ H) A' B' ∧ A'.card+B'.card ≤ A.card+B.card+1 := by
    refine Fin.addCases (motive := fun w =>
      (∀ e ∈ F, L e.1 = w ∨ R e.2 = w) →
      ∃ A' B', cover (F ∪ H) A' B' ∧ A'.card+B'.card ≤ A.card+B.card+1) ?_ ?_ v center
    · intro p hp
      refine ⟨insert p A, B, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_union.mp he with he | he
        · have eq := (hp e he).resolve_right (by simpa [L, R] using (sep p e.2).symm)
          have hp' : e.1 = p := Fin.ext (congrArg (fun z : Fin (n+m) => z.val) eq)
          exact Or.inl (hp' ▸ Finset.mem_insert_self _ _)
        · exact (hcov e he).imp Finset.mem_insert_of_mem id
      · have := Finset.card_insert_le p A
        omega
    · intro l hl
      refine ⟨A, insert l B, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_union.mp he with he | he
        · have eq := (hl e he).resolve_left (by simpa [L, R] using sep e.1 l)
          have hv := congrArg Fin.val eq
          change n + e.2.val = n + l.val at hv
          have hl' : e.2 = l := Fin.ext (by omega)
          exact Or.inr (hl' ▸ Finset.mem_insert_self _ _)
        · exact (hcov e he).imp id Finset.mem_insert_of_mem
      · have := Finset.card_insert_le l B
        omega
  have solve (E : Finset (Fin n × Fin m)) : noSquare E → ∀ C, IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = target E z) →
      ∃ A B, cover E A B ∧ E.card + A.card + B.card ≤ C.size + 1 := by
    induction E using Finset.strongInduction with
    | H E ih =>
      intro sq C hAO hC
      by_cases split : ∃ (F H : Finset (Fin n × Fin m)) (v : Fin (n+m)),
        F.Nonempty ∧ F ∪ H = E ∧ Disjoint (ends F) (ends H) ∧
          ∀ e ∈ F, L e.1 = v ∨ R e.2 = v
      · obtain ⟨F,H,v,hF,hEq,hdis,hcenter⟩ := split
        have hFsub : F ⊆ E := hEq ▸ Finset.subset_union_left
        have hHsub : H ⊆ E := hEq ▸ Finset.subset_union_right
        have edgeDis : Disjoint F H := Finset.disjoint_left.mpr
          (fun e hf hh => Finset.disjoint_left.mp hdis (left F e hf) (left H e hh))
        have cards : F.card + H.card = E.card := by
          rw [← hEq, Finset.card_union_of_disjoint edgeDis]
        have support := centerCard F v hF hcenter
        have dep := dependent E F hFsub C hC
        by_cases hEmpty : H = ∅
        · have bound : (ends F).card ≤ C.size + 1 :=
            essentialInputs (n+m) C (fun g hg => (hAO.2.2 g hg).le) (ends F) dep
          have hcov : cover H ∅ ∅ := by simp [cover, hEmpty]
          obtain ⟨A,B,hcov,sm⟩ := addCenter F H v hcenter ∅ ∅ hcov
          simp only [Finset.card_empty, zero_add] at sm
          have he : H.card = 0 := by simp [hEmpty]
          exact ⟨A,B,hEq ▸ hcov,by omega⟩
        · let zero (x : Fin (n+m) → Bool) (w : Fin (n+m)) := if w ∈ ends F then false else x w
          have collapse (x : Fin (n+m) → Bool) : target E (zero x) = target H x := by
            apply Bool.eq_iff_iff.mpr
            simp only [target, decide_eq_true_eq]
            constructor
            · rintro ⟨e,he,hl,hr⟩
              have nF : e ∉ F := by
                intro hf
                simp [zero, left F e hf] at hl
              have hH : e ∈ H := (Finset.mem_union.mp (hEq ▸ he)).resolve_left nF
              have nol : L e.1 ∉ ends F := fun h => Finset.disjoint_left.mp hdis h (left H e hH)
              have nor : R e.2 ∉ ends F := fun h => Finset.disjoint_left.mp hdis h (right H e hH)
              exact ⟨e,hH,by simpa [zero,nol] using hl,by simpa [zero,nor] using hr⟩
            · rintro ⟨e,he,hl,hr⟩
              have nol : L e.1 ∉ ends F := fun h => Finset.disjoint_left.mp hdis h (left H e he)
              have nor : R e.2 ∉ ends F := fun h => Finset.disjoint_left.mp hdis h (right H e he)
              exact ⟨e,hHsub he,by simpa [zero,nol] using hl,by simpa [zero,nor] using hr⟩
          have varying : ∃ x y, circuitFun (n+m) C (zero x) ≠ circuitFun (n+m) C (zero y) := by
            obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
            refine ⟨fun _ => false, fun _ => true, ?_⟩
            rw [hC, hC, collapse (fun _ => false), collapse (fun _ => true)]
            have off : target H (fun _ => false) = false := by simp [target]
            have on : target H (fun _ => true) = true := by
              simp only [target, decide_eq_true_eq]
              exact ⟨e,he,trivial,trivial⟩
            rw [off,on]
            decide
          obtain ⟨D,hD,saved,new⟩ := pin (n+m) C (ends F) hAO dep varying
          have sub : H ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hHsub, by
            intro h
            have := hF.card_pos
            rw [h] at cards
            omega⟩
          have squareH : noSquare H := by
            intro p q l s hp hs h
            exact sq p q l s hp hs ⟨hHsub h.1,hHsub h.2.1,hHsub h.2.2.1,hHsub h.2.2.2⟩
          obtain ⟨A,B,cov,cost⟩ := ih H sub squareH D hD (fun x => (new x).trans
            ((hC (zero x)).trans (collapse x)))
          obtain ⟨A',B',cov',bound⟩ := addCenter F H v hcenter A B cov
          exact ⟨A',B',hEq ▸ cov',by omega⟩
      · exact core n m E C sq hAO hC split
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ edges ↔ I p l := by simp [edges]
  have hno : noSquare edges := by simpa only [noSquare,mem] using square
  have hfun (x : Fin (n+m) → Bool) : circuitFun (n+m) C x = target edges x := by
    rw [correct]; apply Bool.eq_iff_iff.mpr
    simp only [target,decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,hp,hl,hr⟩
      exact ⟨(p,l),(mem p l).mpr hp,hl,hr⟩
    · rintro ⟨⟨p,l⟩,hp,hl,hr⟩
      exact ⟨p,l,(mem p l).mp hp,hl,hr⟩
  obtain ⟨A,B,hcov,price⟩ := solve edges hno C ao hfun
  obtain ⟨own,hvalid,hcovers,hprice⟩ := stars n m edges A B hcov
  exact ⟨own,hvalid,by simpa only [mem] using hcovers,by omega⟩
