import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_3491_471
    (cofactor : ∀ (k : ℕ) (C : Circuit) (v : Fin k), IsAO2 k C →
      (∃ x : Fin k → Bool, circuitFun k C x ≠ circuitFun k C (Function.update x v false)) →
      (∃ x y : Fin k → Bool, circuitFun k C (Function.update x v false) ≠ circuitFun k C (Function.update y v false)) →
      ∃ D : Circuit, IsAO2 k D ∧ D.size < C.size ∧
        ∀ x : Fin k → Bool, circuitFun k D x = circuitFun k C (Function.update x v false))
    (core : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)),
      let ends := fun e : Fin n × Fin m => ({Fin.castAdd m e.1, Fin.natAdd n e.2} : Finset (Fin (n+m)))
      let leaves := fun v : Fin (n+m) => E.filter fun e => v ∈ ends e
      PEqualNP.ReadTwo.Lin (fun p l => (p,l) ∈ E) →
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ u ∈ ends e, ∀ v ∈ ends f,
        leaves u = {e} → leaves v = {f} → Disjoint (ends e) (ends f)) →
      (∃ e ∈ E, ∃ f ∈ E, e ≠ f ∧ ¬ Disjoint (ends e) (ends f)) →
      ∀ C : Circuit, IsAO2 (n+m) C →
        (∀ x : Fin (n+m) → Bool, circuitFun (n+m) C x =
          decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)) →
        ∃ S : Finset (Fin (n+m)), (∀ e ∈ E, ∃ i ∈ ends e, i ∈ S) ∧ E.card + S.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : Finset (Fin (x1 + x2))), (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 → Fin.castAdd x2 x10 ∈ x9 ∨ Fin.natAdd x1 x11 ∈ x9) ∧ (PEqualNP.ReadTwo.incid x3).card + x9.card ≤ x5.size + (1 : ℕ) := by
  intro n m I inst C hLin hAO compute
  classical
  have dependencies (k : ℕ) (C : Circuit) (ao : IsAO2 k C) : ∃ S : Finset (Fin k),
      S.card ≤ C.size + 1 ∧ ∀ x y : Fin k → Bool, (∀ v ∈ S, x v = y v) → circuitFun k C x = circuitFun k C y := by
    let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
    have tailRead (w : List Bool) (b : Bool) (j : ℕ) (h : j ≠ w.length) :
        (w ++ [b]).getD j false = w.getD j false := by
      by_cases small : j < w.length
      · exact List.getD_append _ _ _ _ small
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have plan (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length = 2) (l : ℕ) :
        ∃ P : Finset ℕ, P.card ≤ gs.length + 1 ∧ ∀ a b : List Bool,
          a.length=l → b.length=l → (∀ j ∈ P, a.getD j false = b.getD j false) →
          (gs.foldl step a).getD C.output false = (gs.foldl step b).getD C.output false := by
      induction gs generalizing l with
      | nil => exact ⟨{C.output},by simp,fun _ _ _ _ h => h _ (by simp)⟩
      | cons g gs ih =>
        obtain ⟨T,cost,agree⟩ := ih (fun v hv => arity v (List.mem_cons_of_mem _ hv)) (l+1)
        by_cases present : l ∈ T
        · let P := T.erase l ∪ g.inputs.toFinset
          refine ⟨P,?_,?_⟩
          · have h1 := Finset.card_union_le (T.erase l) g.inputs.toFinset
            have h2 := Finset.card_erase_add_one present
            have h3 := List.toFinset_card_le g.inputs
            have h4 := arity g List.mem_cons_self
            change (T.erase l ∪ g.inputs.toFinset).card ≤ gs.length+1+1
            omega
          · intro a b ha hb h
            apply agree (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
            intro j hj
            by_cases hit : j=l
            · subst j
              have vals : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) :=
                List.map_congr_left (fun i hi => h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
              have last (u : List Bool) (hu : u.length=l) :
                  (step u g).getD l false = g.op.eval (g.inputs.map fun i => u.getD i false) := by
                rw [← hu]; simp [step]
              rw [last a ha,last b hb,vals]
            · unfold step
              rw [tailRead _ _ _ (by omega),tailRead _ _ _ (by omega)]
              exact h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hit,hj⟩))
        · refine ⟨T,by simp only [List.length_cons]; omega,?_⟩
          intro a b ha hb h
          apply agree (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
          intro j hj
          have ne : j ≠ l := fun eq => present (eq ▸ hj)
          unfold step
          rw [tailRead _ _ _ (by omega),tailRead _ _ _ (by omega),h j hj]
    obtain ⟨P,bound,agrees⟩ := plan C.gates ao.2.2 k
    let S := Finset.univ.filter (fun i : Fin k => i.val ∈ P)
    have cap : S.card ≤ P.card := by
      rw [← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hi).2
    refine ⟨S,cap.trans bound,?_⟩
    intro x y h
    apply agrees (List.ofFn x) (List.ofFn y) (by simp) (by simp)
    intro j hj
    by_cases small : j<k
    · let i : Fin k := ⟨j,small⟩
      have atInput (a : Fin k → Bool) : (List.ofFn a).getD j false = a i := by
        rw [List.getD_eq_getElem _ _ (by simpa)]
        exact List.getElem_ofFn _
      rw [atInput,atInput]
      exact h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  let ends := fun e : Fin n × Fin m => ({Fin.castAdd m e.1, Fin.natAdd n e.2} : Finset (Fin (n+m)))
  let eval := fun (E : Finset (Fin n × Fin m)) (x : Fin (n+m) → Bool) =>
    decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true)
  have apart (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have := p.isLt
    omega
  have cardTwo (e : Fin n × Fin m) : (ends e).card = 2 := by simp [ends,apart]
  have active (E : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (he : e ∈ E) (u : Fin (n+m))
      (hu : u ∈ ends e) :
      ∃ x : Fin (n+m) → Bool, eval E x ≠ eval E (Function.update x u false) := by
    let x := fun v => decide (v ∈ ends e)
    refine ⟨x,?_⟩
    have yes : eval E x = true := by
      apply decide_eq_true
      exact ⟨e,he,by simp [x,ends]⟩
    rw [yes]
    intro bad
    obtain ⟨f,hf,hboth⟩ := of_decide_eq_true bad.symm
    obtain ⟨L,R⟩ := hboth
    have old (z : Fin (n+m)) (h : Function.update x u false z = true) : z ∈ ends e ∧ z ≠ u := by
      by_cases hz : z=u
      · subst z; simp at h
      · simpa [x,Function.update_of_ne hz,hz] using h
    have l := old _ L
    have r := old _ R
    have sub : ends f ⊆ ends e := by
      intro i h
      rcases (show i = Fin.castAdd m f.1 ∨ i = Fin.natAdd n f.2 by simpa [ends] using h) with rfl | rfl
      · exact l.1
      · exact r.1
    have eq := Finset.eq_of_subset_of_card_le sub (by rw [cardTwo,cardTwo])
    have mem : u ∈ ends f := eq.symm ▸ hu
    rcases (show u = Fin.castAdd m f.1 ∨ u = Fin.natAdd n f.2 by simpa [ends] using mem) with h | h
    · exact l.2 h.symm
    · exact r.2 h.symm
  have solve (b : ℕ) : ∀ E : Finset (Fin n × Fin m), E.card = b →
      PEqualNP.ReadTwo.Lin (fun p l => (p,l) ∈ E) →
      ∀ D : Circuit, IsAO2 (n+m) D → (∀ x, circuitFun (n+m) D x = eval E x) →
      ∃ S : Finset (Fin (n+m)), (∀ e ∈ E, ∃ z ∈ ends e, z ∈ S) ∧ E.card + S.card ≤ D.size+1 := by
    induction b using Nat.strong_induction_on with
    | ind b ih =>
      intro E hCard lin D dao computes
      let leaves := fun v : Fin (n+m) => E.filter fun e => v ∈ ends e
      by_cases twinsFree : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ u ∈ ends e, ∀ v ∈ ends f,
          leaves u = {e} → leaves v = {f} → Disjoint (ends e) (ends f)
      · by_cases branch : ∃ e ∈ E, ∃ f ∈ E, e ≠ f ∧ ¬Disjoint (ends e) (ends f)
        · exact core n m E lin twinsFree branch D dao computes
        · obtain ⟨S,cap,dep⟩ := dependencies (n+m) D dao
          have subset : E.biUnion ends ⊆ S := by
            intro u hu
            obtain ⟨e,he,mem⟩ := Finset.mem_biUnion.mp hu
            obtain ⟨x,hx⟩ := active E e he u mem
            by_contra outside
            have same := dep x (Function.update x u false) (by
              intro z hz
              have ne : z ≠ u := fun e => outside (e ▸ hz)
              simp [Function.update_of_ne ne])
            exact hx ((computes x).symm.trans (same.trans (computes _)))
          have count : (E.biUnion ends).card = 2 * E.card := by
            rw [Finset.card_biUnion (fun i hi j hj hne => by
              by_contra conflict; exact branch ⟨i,hi,j,hj,hne,conflict⟩)]
            simp [cardTwo,Nat.mul_comm]
          let T := E.image fun e => Fin.castAdd m e.1
          refine ⟨T, fun e he => ⟨_,by simp [ends],Finset.mem_image_of_mem _ he⟩,?_⟩
          have h1 := Finset.card_le_card subset
          have h2 : T.card ≤ E.card := Finset.card_image_le
          omega
      · push Not at twinsFree
        obtain ⟨e,he,f,hf,hef,u,hue,v,hvf,hu,hv,overlap⟩ := twinsFree
        obtain ⟨z,hze,hzf⟩ := Finset.not_disjoint_iff.mp overlap
        have only (s : Fin (n+m)) (h : Fin n × Fin m) (single : leaves s = {h})
            (t : Fin n × Fin m) (ht : t ∈ E) (st : s ∈ ends t) : t = h := by
          have mem : t ∈ leaves s := Finset.mem_filter.mpr ⟨ht,st⟩
          simpa only [single,Finset.mem_singleton] using mem
        have vz : v ≠ z := fun eq => hef (only v f hv e he (eq ▸ hze))
        have pairF : ends f = {v,z} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro i hi
            rcases (show i=v ∨ i=z by simpa using hi) with rfl | rfl
            · exact hvf
            · exact hzf
          · simp [cardTwo,vz]
        let R := E.erase e
        have linR : PEqualNP.ReadTwo.Lin (fun p l => (p,l) ∈ R) := by
          intro p p' l l' pp ll rect
          exact lin p p' l l' pp ll ⟨Finset.mem_of_mem_erase rect.1,Finset.mem_of_mem_erase rect.2.1,
            Finset.mem_of_mem_erase rect.2.2.1,Finset.mem_of_mem_erase rect.2.2.2⟩
        obtain ⟨x,diff⟩ := active E e he u hue
        have ufree : u ∉ ends f := fun h => hef (only u e hu f hf h).symm
        have remains : ∃ x y : Fin (n+m) → Bool, circuitFun (n+m) D (Function.update x u false) ≠
            circuitFun (n+m) D (Function.update y u false) := by
          refine ⟨fun _ => false, fun i => decide (i ∈ ends f), ?_⟩
          rw [computes,computes]
          have zero : Function.update (fun _ : Fin (n+m) => false) u false = fun _ => false := by
            funext i; by_cases h : i=u <;> simp [Function.update,h]
          rw [zero]
          have l : Fin.castAdd m f.1 ≠ u := fun eq => ufree (eq ▸ (by simp [ends] : Fin.castAdd m f.1 ∈ ends f))
          have r : Fin.natAdd n f.2 ≠ u := fun eq => ufree (eq ▸ (by simp [ends] : Fin.natAdd n f.2 ∈ ends f))
          have yes : eval E (Function.update (fun i => decide (i ∈ ends f)) u false) = true := by
            apply decide_eq_true
            exact ⟨f,hf,by simp [Function.update_of_ne l,ends],by simp [Function.update_of_ne r,ends]⟩
          rw [yes]
          simp [eval]
        obtain ⟨K,ka,smaller,kfun⟩ := cofactor (n+m) D u dao ⟨x,by simpa only [computes] using diff⟩ remains
        have reduced (x : Fin (n+m) → Bool) : circuitFun (n+m) K x = eval R x := by
          rw [kfun, computes]
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h
            obtain ⟨t,ht,hit⟩ := of_decide_eq_true h
            have both := hit
            have ne (w : Fin (n+m)) (hh : Function.update x u false w = true) : w ≠ u := by
              intro eq; subst w; simp at hh
            have l := ne _ both.1
            have r := ne _ both.2
            have te : t ≠ e := by
              intro eq; subst t
              rcases (show u=Fin.castAdd m e.1 ∨ u=Fin.natAdd n e.2 by simpa [ends] using hue) with hh | hh
              · exact l hh.symm
              · exact r hh.symm
            exact decide_eq_true ⟨t,Finset.mem_erase.mpr ⟨te,ht⟩,by
              simpa [Function.update_of_ne l,Function.update_of_ne r] using hit⟩
          · intro h
            obtain ⟨t,ht,hit⟩ := of_decide_eq_true h
            obtain ⟨ne,mem⟩ := Finset.mem_erase.mp ht
            have no : u ∉ ends t := fun h => ne (only u e hu t mem h)
            have l : Fin.castAdd m t.1 ≠ u := fun eq => no (eq ▸ (by simp [ends] : Fin.castAdd m t.1 ∈ ends t))
            have r : Fin.natAdd n t.2 ≠ u := fun eq => no (eq ▸ (by simp [ends] : Fin.natAdd n t.2 ∈ ends t))
            exact decide_eq_true ⟨t,mem,by simpa [Function.update_of_ne l,Function.update_of_ne r] using hit⟩
        have rcard : R.card + 1 = E.card := Finset.card_erase_add_one he
        obtain ⟨S,covers,cap⟩ := ih R.card (by omega) R rfl linR K ka reduced
        by_cases zs : z ∈ S
        · refine ⟨S,?_,by omega⟩
          intro t ht
          by_cases te : t=e
          · exact ⟨z, te ▸ hze,zs⟩
          · exact covers t (Finset.mem_erase.mpr ⟨te,ht⟩)
        · obtain ⟨w,hw,ws⟩ := covers f (Finset.mem_erase.mpr ⟨hef.symm,hf⟩)
          have vs : v ∈ S := by
            rw [pairF] at hw
            rcases (show w=v ∨ w=z by simpa using hw) with rfl | rfl
            · exact ws
            · contradiction
          let T := insert z (S.erase v)
          have zt : z ∈ T := Finset.mem_insert_self _ _
          refine ⟨T,?_,?_⟩
          · intro t ht
            by_cases te : t=e
            · exact ⟨z,te ▸ hze,zt⟩
            by_cases tf : t=f
            · exact ⟨z,tf ▸ hzf,zt⟩
            obtain ⟨w,hw,ws⟩ := covers t (Finset.mem_erase.mpr ⟨te,ht⟩)
            have wv : w ≠ v := fun eq => tf (only v f hv t ht (eq ▸ hw))
            exact ⟨w,hw,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨wv,ws⟩)⟩
          · have card := Finset.card_insert_le z (S.erase v)
            have erased := Finset.card_erase_add_one vs
            change E.card+(insert z (S.erase v)).card ≤ D.size+1
            omega
  let E := PEqualNP.ReadTwo.incid I
  have memE (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by
    dsimp only [E]
    delta PEqualNP.ReadTwo.incid
    simp
  have linear : PEqualNP.ReadTwo.Lin (fun p l => (p,l) ∈ E) := by
    intro p q l r pq lr rect
    exact hLin p q l r pq lr ⟨(memE _ _).mp rect.1,(memE _ _).mp rect.2.2.1,
      (memE _ _).mp rect.2.1,(memE _ _).mp rect.2.2.2⟩
  have correct (x : Fin (n+m) → Bool) : circuitFun (n+m) C x = eval E x := by
    rw [compute]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,eval]
    constructor
    · rintro ⟨p,l,pl,hp,hl⟩
      exact ⟨(p,l), (memE p l).mpr pl, hp,hl⟩
    · rintro ⟨⟨p,l⟩,pl,hp,hl⟩
      exact ⟨p,l,(memE p l).mp pl,hp,hl⟩
  obtain ⟨S,covers,bound⟩ := solve E.card E rfl linear C hAO correct
  refine ⟨S,?_,bound⟩
  intro p l edge
  obtain ⟨z,hz,hs⟩ := covers (p,l) ((memE p l).mpr edge)
  rcases (show z=Fin.castAdd m p ∨ z=Fin.natAdd n l by simpa [ends] using hz) with rfl | rfl
  · exact Or.inl hs
  · exact Or.inr hs
