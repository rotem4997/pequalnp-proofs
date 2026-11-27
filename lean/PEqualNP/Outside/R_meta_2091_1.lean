import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection in

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2091_1
    (few : let D : Finset (Fin 13) := {0,1,3,9}
      let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 => p-l ∈ D
      ∀ (B : Circuit) (T : Finset (Finset ℕ)), Monotone2 B → T.card ≤ 12 →
        B.size + 2*T.card ≤ 64 → (∀ t ∈ T, t.card ≤ 2 ∧ t ⊆ Finset.range (26+B.size)) →
        let fires := fun (t : Finset ℕ) (x : List Bool) => ∀ i ∈ t, (B.wires x).getD i false = true
        (∀ t ∈ T, ∃ p l, p ∈ S l ∧ fires t (incidenceInput {p} {l}) ∧
          ∀ u ∈ T, u ≠ t → ¬ fires u (incidenceInput {p} {l})) →
        (∀ X Y, IsMaximalFalse S X Y → (¬ InNoLine S X ∨ ¬ InNoPencil S Y) →
          ∀ t ∈ T, ¬ fires t (incidenceInput X Y)) →
        (∃ t ∈ T, let H := (PEqualNP.HeptadCover.incidences S).filter fun e =>
                    fires t (incidenceInput {e.1} {e.2})
                  5 ≤ H.card ∧ ∃ e ∈ H, ∃ f ∈ H, e.1 ∉ S f.2 ∧
                    ¬fires t (incidenceInput {e.1} {f.2})) →
        ∃ p l, p ∈ S l ∧ ∀ t ∈ T, ¬ fires t (incidenceInput {p} {l}))
    (many : let D : Finset (Fin 13) := {0,1,3,9}
      let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 => p-l ∈ D
      ∀ (B : Circuit) (T : Finset (Finset ℕ)), Monotone2 B → B.size ≤ 38 →
        13 ≤ T.card → (∀ t ∈ T, t.card ≤ 2 ∧ t ⊆ Finset.range (26+B.size)) →
        let fires := fun (t : Finset ℕ) (x : List Bool) => ∀ i ∈ t, (B.wires x).getD i false = true
        (∀ t ∈ T, ∃ p l, p ∈ S l ∧ fires t (incidenceInput {p} {l}) ∧
          ∀ u ∈ T, u ≠ t → ¬ fires u (incidenceInput {p} {l})) →
        (∀ X Y, IsMaximalFalse S X Y → (¬ InNoLine S X ∨ ¬ InNoPencil S Y) →
          ∀ t ∈ T, ¬ fires t (incidenceInput X Y)) →
        (∀ p l, p ∈ S l → ∃ t ∈ T, fires t (incidenceInput {p} {l})) →
        65 ≤ B.size + 2*T.card) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  classical
  intro D E A pair row W C hm hs a b _ hp hn
  let run (gs : List Gate) (x : List Bool) := (Circuit.mk gs 0).wires x
  let val (gs : List Gate) (i : ℕ) (x : List Bool) := (run gs x).getD i false
  let hit (gs : List Gate) (R : Finset ℕ) (x : List Bool) := ∃ i ∈ R, val gs i x = true
  let fires (gs : List Gate) (t : List ℕ) (x : List Bool) := ∀ i ∈ t, val gs i x = true
  let good (gs : List Gate) := Monotone2 (Circuit.mk gs 0)
  let ok (gs : List Gate) (i : ℕ) := i < 26 + gs.length ∨ i = 100
  have len (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
    induction gs generalizing x with
    | nil => simp [run]; rfl
    | cons g gs ih =>
      change (run gs (x ++ [_])).length = _
      rw [ih]
      simp; clear * -; lia -abstractProof
  have snoc (gs : List Gate) (g : Gate) (x : List Bool) : run (gs ++ [g]) x =
      run gs x ++ [g.op.eval (g.inputs.map fun i => val gs i x)] := by
    change List.foldl _ _ (gs ++ [g]) = _
    rw [List.foldl_append]; rfl
  have atGate (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 26) :
      val (gs ++ [g]) (26+gs.length) x = g.op.eval (g.inputs.map fun i => val gs i x) := by
    change (run (gs++[g]) x).getD _ false = _
    rw [snoc, ← hx, ← len]
    simp [List.getD_eq_getElem?_getD]
  have other (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 26)
      (i : ℕ) (hi : i ≠ 26+gs.length) : val (gs++[g]) i x = val gs i x := by
    change (run (gs++[g]) x).getD _ false = (run gs x).getD _ false
    rw [snoc]
    by_cases h : i < (run gs x).length
    · exact List.getD_append _ _ _ _ h
    · have hlen := len gs x
      rw [List.getD_eq_default _ _ (by simp; clear * - hlen hx h hi; lia -abstractProof),
        List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
  have dummy (gs : List Gate) (h : gs.length ≤ 62) (x : List Bool) (hx : x.length = 26) :
      val gs 100 x = false := List.getD_eq_default _ _ (by rw [len, hx]; clear * - h; lia -abstractProof)
  have opOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have opAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  -- An exposed gate may also feed the preprocessing network. Replace that use by false:
  -- on rows not accepted by the exposed network the original wire was already false.
  have extract (gs : List Gate) (mono : good gs) (cap : gs.length ≤ 62) (R : Finset ℕ) :
      ∃ (ds : List Gate) (T : List (List ℕ)) (I : Finset ℕ) (ρ : ℕ → ℕ),
        good ds ∧ ds.length ≤ gs.length ∧ ds.length + 2*T.length ≤ gs.length + R.card ∧
        (∀ t ∈ T, t.length ≤ 2 ∧ ∀ i ∈ t, ok ds i) ∧ (∀ i, ok ds (ρ i)) ∧
        (∀ x : List Bool, x.length = 26 → (hit gs R x ↔ hit [] I x ∨ ∃ t ∈ T, fires ds t x)) ∧
        ∀ x : List Bool, x.length = 26 → ¬ hit gs R x → ∀ i, val ds (ρ i) x = val gs i x := by
    induction gs using List.reverseRecOn generalizing R with
    | nil =>
      refine ⟨[], [], R, fun i => if i < 26 then i else 100, mono, le_rfl, by simp, by simp, ?_, by simp, ?_⟩
      · intro i; by_cases h : i < 26 <;> simp [ok,h]
      · intro x hx _ i
        by_cases hi : i < 26
        · simp [hi]
        · simp only [hi, ite_false]
          change x.getD 100 false = x.getD i false
          rw [List.getD_eq_default _ _ (by rw [hx]; decide), List.getD_eq_default _ _ (hx ▸ Nat.le_of_not_gt hi)]
    | append_singleton gs g ih =>
      let j := 26 + gs.length
      let U := R.erase j
      have m0 : good gs := fun z hz => mono z (List.mem_append_left _ hz)
      have mg := mono g (List.mem_append_right _ (List.mem_singleton_self _))
      have ops : g.op = .and ∨ g.op = .or := mg.1
      have ar := mg.2
      have lg : (gs++[g]).length = gs.length+1 := by simp
      have cap0 : gs.length ≤ 62 := by rw [lg] at cap; exact (Nat.le_succ _).trans cap
      have splitR (x : List Bool) (hx : x.length = 26) : hit (gs++[g]) R x ↔
          hit gs U x ∨ (j ∈ R ∧ val (gs++[g]) j x = true) := by
        constructor
        · rintro ⟨i,hi,hv⟩
          by_cases h : i = j
          · subst i; exact Or.inr ⟨hi,hv⟩
          · exact Or.inl ⟨i,Finset.mem_erase.mpr ⟨h,hi⟩,(other gs g x hx i h) ▸ hv⟩
        · rintro (⟨i,hi,hv⟩ | ⟨hi,hv⟩)
          · obtain ⟨ht,hr⟩ := Finset.mem_erase.mp hi
            exact ⟨i,hr,(other gs g x hx i ht).trans hv⟩
          · exact ⟨j,hi,hv⟩
      by_cases root : j ∈ R
      · have count : U.card + 1 = R.card := Finset.card_erase_add_one root
        -- Both root cases delete g. All earlier wires remain addressable by the old map.
        have forget (ds : List Gate) (f : ℕ → ℕ) (hds : ds.length ≤ gs.length)
            (hf : ∀ i, ok ds (f i)) (Q : Finset ℕ)
            (agree : ∀ x : List Bool, x.length = 26 → ¬hit gs Q x → ∀ i, val ds (f i) x = val gs i x)
            (sub : ∀ x : List Bool, x.length = 26 → hit gs Q x → hit (gs++[g]) R x) :
            (∀ i, ok ds (if i=j then 100 else f i)) ∧
            ∀ x : List Bool, x.length = 26 → ¬hit (gs++[g]) R x → ∀ i,
              val ds (if i=j then 100 else f i) x = val (gs++[g]) i x := by
          constructor
          · intro i; split_ifs <;> first | exact Or.inr rfl | exact hf i
          · intro x hx no i
            split_ifs with h
            · subst i; rw [dummy ds (hds.trans cap0) x hx]
              exact (Bool.eq_false_iff.mpr (fun ht => no ⟨j,root,ht⟩)).symm
            · exact (agree x hx (fun ht => no (sub x hx ht)) i).trans (other gs g x hx i h).symm
        rcases ops with ha | ho
        · obtain ⟨ds,T,I,f,md,ld,budget,ht,hf,model,agree⟩ := ih m0 cap0 U
          let t := g.inputs.map f
          have red := forget ds f ld hf U agree (fun x hx h => (splitR x hx).2 (Or.inl h))
          refine ⟨ds,t::T,I,_,md,by rw [lg]; exact ld.trans (Nat.le_succ _),by
            simp only [List.length_cons]; clear * - lg count budget; lia -abstractProof,?_,red.1,?_,red.2⟩
          · intro s hs'
            rcases List.mem_cons.mp hs' with rfl | h
            · exact ⟨by simpa [t] using ar, fun i hi => by obtain ⟨k,_,rfl⟩ := List.mem_map.mp hi; exact hf k⟩
            · exact ht s h
          · intro x hx
            rw [splitR x hx]
            by_cases old : hit gs U x
            · have hitOld := (model x hx).1 old
              constructor
              · intro _; rcases hitOld with h | ⟨s,hs',hv⟩
                · exact Or.inl h
                · exact Or.inr ⟨s,List.mem_cons_of_mem _ hs',hv⟩
              · exact fun _ => Or.inl old
            · have spec : val (gs++[g]) j x = true ↔ fires ds t x := by
                rw [atGate gs g x hx, ha, opAnd, List.all_eq_true]
                change (∀ v ∈ g.inputs.map (fun i => val gs i x), v = true) ↔
                  ∀ i ∈ g.inputs.map f, val ds i x = true
                rw [List.forall_mem_map, List.forall_mem_map]
                exact forall_congr' fun i => forall_congr' fun _ => by rw [agree x hx old]
              have no := (model x hx).not.mp old
              rw [show (j ∈ R ∧ val (gs++[g]) j x = true) ↔ fires ds t x by simp [root,spec]]
              simp only [old,false_or]
              constructor
              · exact fun h => Or.inr ⟨t,List.mem_cons_self,h⟩
              · rintro (h | ⟨s,hs',hv⟩)
                · exact (no (Or.inl h)).elim
                · rcases List.mem_cons.mp hs' with rfl | h
                  · exact hv
                  · exact (no (Or.inr ⟨s,h,hv⟩)).elim
        · let Q := U ∪ g.inputs.toFinset
          have equivQ (x : List Bool) (hx : x.length = 26) : hit (gs++[g]) R x ↔ hit gs Q x := by
            have gate : val (gs++[g]) j x = true ↔ ∃ i ∈ g.inputs, val gs i x = true := by
              rw [atGate gs g x hx, ho, opOr, List.any_eq_true]
              constructor
              · rintro ⟨v,hv,hh⟩
                obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
                exact ⟨i,hi,hh⟩
              · rintro ⟨i,hi,hh⟩
                exact ⟨_,List.mem_map_of_mem hi,hh⟩
            rw [splitR x hx,gate]
            constructor
            · rintro (⟨i,hi,hh⟩ | ⟨_,i,hi,hh⟩)
              · exact ⟨i,Finset.mem_union_left _ hi,hh⟩
              · exact ⟨i,Finset.mem_union_right _ (List.mem_toFinset.mpr hi),hh⟩
            · rintro ⟨i,hi,hh⟩
              rcases Finset.mem_union.mp hi with hi | hi
              · exact Or.inl ⟨i,hi,hh⟩
              · exact Or.inr ⟨root,i,List.mem_toFinset.mp hi,hh⟩
          obtain ⟨ds,T,I,f,md,ld,budget,ht,hf,model,agree⟩ := ih m0 cap0 Q
          have red := forget ds f ld hf Q agree (fun x hx => (equivQ x hx).2)
          have nq := Finset.card_union_le U g.inputs.toFinset
          have nl := List.toFinset_card_le g.inputs
          exact ⟨ds,T,I,_,md,by rw [lg]; exact ld.trans (Nat.le_succ _),by
            dsimp [Q] at budget; clear * - budget nq nl ar count lg; lia -abstractProof,ht,red.1,
            fun x hx => (equivQ x hx).trans (model x hx),red.2⟩
      · have ur : U = R := Finset.erase_eq_of_notMem root
        have eqR (x : List Bool) (hx : x.length = 26) : hit (gs++[g]) R x ↔ hit gs R x := by
          simp only [splitR x hx, ur, root, false_and, or_false]
        obtain ⟨ds,T,I,f,md,ld,budget,ht,hf,model,agree⟩ := ih m0 cap0 R
        let h : Gate := ⟨g.op, g.inputs.map f⟩
        let k := 26+ds.length
        have lk : (ds++[h]).length = ds.length+1 := by simp
        have keep {i : ℕ} (hi : ok ds i) : i ≠ k := by
          change i < 26+ds.length ∨ i=100 at hi
          dsimp [k]; clear * - hi ld cap0; lia -abstractProof
        have up {i : ℕ} (hi : ok ds i) : ok (ds++[h]) i := by
          change i < 26+ds.length ∨ i=100 at hi
          change i < 26+(ds++[h]).length ∨ i=100; clear * - hi lk; lia -abstractProof
        refine ⟨ds++[h],T,I,fun i => if i=j then k else f i,?_,by
          rw [lg,lk]; exact Nat.succ_le_succ ld,by clear * - lk lg budget; lia -abstractProof,?_,?_,?_,?_⟩
        · intro u hu
          rcases List.mem_append.mp hu with hu | hu
          · exact md u hu
          · obtain rfl := List.mem_singleton.mp hu
            exact ⟨mg.1,by simpa [h] using ar⟩
        · intro t hT; exact ⟨(ht t hT).1,fun i hi => up ((ht t hT).2 i hi)⟩
        · intro i; change ok _ (if i=j then k else f i); split_ifs
          · exact Or.inl (by dsimp [k]; rw [lk]; exact Nat.lt_succ_self _)
          · exact up (hf i)
        · intro x hx
          rw [eqR x hx,model x hx]
          apply or_congr_right
          apply exists_congr; intro t
          apply and_congr_right; intro hT
          unfold fires
          exact forall_congr' fun i => forall_congr' fun hi => by rw [other ds h x hx i (keep ((ht t hT).2 i hi))]
        · intro x hx no i
          have eqs := agree x hx (fun a' => no ((eqR x hx).2 a'))
          change val _ (if i=j then k else f i) x = _
          split_ifs with e
          · subst i; rw [atGate ds h x hx,atGate gs g x hx]
            change g.op.eval ((g.inputs.map f).map _) = _
            rw [List.map_map]
            congr 1
            exact List.map_congr_left (fun i _ => eqs i)
          · exact (other ds h x hx (f i) (keep (hf i))).trans ((eqs i).trans (other gs g x hx i e).symm)
  let R : Finset ℕ := {a.val,b.val}
  have rc : R.card ≤ 2 := by
    exact (Finset.card_insert_le ..).trans (by simp)
  have cs : C.gates.length ≤ 62 := hs
  obtain ⟨ds,T,I,_,md,_,budget,terms,_,model,_⟩ := extract C.gates hm cs R
  let B : Circuit := ⟨ds,0⟩
  have cost : B.size + 2*T.length ≤ 64 := budget.trans (Nat.add_le_add cs rc)
  have arity : ∀ t ∈ T, t.length ≤ 2 := fun t ht => (terms t ht).1
  have out (x : Fin 26 → Bool) :
      hit C.gates R (List.ofFn x) ↔ GateOp.or.eval [W C a x,W C b x] = true := by
    rw [opOr,List.any_eq_true]
    change (∃ i ∈ ({a.val,b.val} : Finset ℕ), W C i x = true) ↔ _
    simp
  have neg (P : Finset (Fin 13)) (hc : ∀ v ∉ P, ∃ w, A P w ∧ E v w)
      (hd : (∃ w, ∀ p ∈ P, E p w) ∨ ∃ v, ∀ w, A P w → E v w) :
      ¬(hit [] I (List.ofFn (row P)) ∨ ∃ t ∈ T, fires ds t (List.ofFn (row P))) := by
    intro h
    have tt := (out _).1 ((model _ List.length_ofFn).2 h)
    rw [hn P hc hd] at tt
    contradiction
  have reflE (p : Fin 13) : E p p := ⟨0,by decide,by simp⟩
  have n0 := neg ∅ (fun v _ => ⟨v,by simp [A],reflE v⟩) (Or.inl ⟨0,by simp⟩)
  have n1 := neg Finset.univ (by simp) (Or.inr ⟨0,fun w h => False.elim (h w (Finset.mem_univ _) (reflE w))⟩)
  have noRaw (x : List Bool) (hx : x.length = 26) : ¬ hit [] I x := by
    rintro ⟨i,hi,hv⟩
    change x.getD i false = true at hv
    have lt : i < 26 := by
      by_contra! hn'
      rw [List.getD_eq_default _ _ (hx ▸ hn')] at hv; contradiction
    let u : Fin 26 := ⟨i,lt⟩
    have on : ∀ u : Fin 26, row ∅ u = true ∨ row Finset.univ u = true := by
      intro v
      induction v using Fin.addCases (m := 13) (n := 13) with
      | left p => exact Or.inr (decide_eq_true (Or.inl ⟨p,Finset.mem_univ _,rfl⟩))
      | right w => exact Or.inl (decide_eq_true (Or.inr ⟨w,rfl,by simp⟩))
    have raw (P : Finset (Fin 13)) (h : row P u = true) : hit [] I (List.ofFn (row P)) := by
      refine ⟨i,hi,?_⟩
      change (List.ofFn (row P)).getD i false = true
      rw [List.getD_eq_getElem _ _ (by simpa using lt),List.getElem_ofFn]; exact h
    rcases on u with h|h
    · exact n0 (Or.inl (raw _ h))
    · exact n1 (Or.inl (raw _ h))
  let S (l : Fin 13) := Finset.univ.filter fun p : Fin 13 => p-l ∈ D
  have memS (p l : Fin 13) : p ∈ S l ↔ E p l := by
    constructor
    · exact fun h => ⟨p-l,(Finset.mem_filter.mp h).2,by rw [add_comm l,sub_add_cancel]⟩
    · rintro ⟨d,hd,rfl⟩; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using hd⟩
  have apart : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide
  have cinj : ∀ p q : Fin 13, (Fin.castAdd 13 p = Fin.castAdd 13 q) ↔ p=q := by decide
  have ninj : ∀ p q : Fin 13, (Fin.natAdd 13 p = Fin.natAdd 13 q) ↔ p=q := by decide
  have posInput (p l : Fin 13) : List.ofFn (pair p l) = incidenceInput {p} {l} := by
    change List.ofFn (n := 13+13) (pair p l) = List.ofFn _ ++ List.ofFn _
    rw [List.ofFn_add (n := 13) (m := 13)]
    congr 1 <;> apply congrArg List.ofFn <;> funext i
    · change pair p l (Fin.castAdd 13 i) = decide (i ∈ ({p} : Finset _))
      apply decide_eq_decide.mpr
      rw [Finset.mem_singleton]; simp only [apart,cinj,or_false]
    · apply decide_eq_decide.mpr
      rw [Finset.mem_singleton]; simp only [Ne.symm (apart p i),ninj,false_or]
  have pos (p l : Fin 13) (h : p ∈ S l) : ∃ t ∈ T, fires ds t (incidenceInput {p} {l}) := by
    rw [← posInput]
    exact ((model _ List.length_ofFn).1 ((out _).2 (hp p l ((memS p l).1 h)))).resolve_left
      (noRaw _ List.length_ofFn)
  have safe (X Y : Finset (Fin 13)) (hmf : IsMaximalFalse S X Y)
      (hd : ¬InNoLine S X ∨ ¬InNoPencil S Y) : ∀ t ∈ T, ¬fires ds t (incidenceInput X Y) := by
    obtain ⟨hfalse,hpoint,hline⟩ := hmf
    have hy (l : Fin 13) : l ∈ Y ↔ A X l := by
      constructor
      · intro hl p hp he
        exact Finset.disjoint_left.mp (hfalse l hl) ((memS p l).2 he) hp
      · intro hav
        by_contra hh
        apply hline l hh
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact Finset.disjoint_left.mpr (fun _ hp hx => hav _ hx ((memS _ _).1 hp))
        · exact hfalse r hr
    have hc (v : Fin 13) (hv : v ∉ X) : ∃ l, A X l ∧ E v l := by
      by_contra! h
      apply hpoint v hv
      intro l hl
      exact Finset.disjoint_left.mpr (fun _ hmem hin => by
        rcases Finset.mem_insert.mp hin with rfl | hin
        · exact h l ((hy l).1 hl) ((memS _ _).1 hmem)
        · exact Finset.disjoint_left.mp (hfalse l hl) hmem hin)
    have hd' : (∃ w, ∀ p ∈ X, E p w) ∨ ∃ v, ∀ w, A X w → E v w := by
      rcases hd with h | h
      · change ¬(∀ l, ¬X ⊆ S l) at h
        push Not at h
        obtain ⟨l,hl⟩ := h
        exact Or.inl ⟨l,fun p hp => (memS _ _).1 (hl hp)⟩
      · change ¬(∀ p, ¬∀ l ∈ Y, p ∈ S l) at h
        push Not at h
        obtain ⟨p,hp⟩ := h
        exact Or.inr ⟨p,fun l hl => (memS _ _).1 (hp l ((hy _).2 hl))⟩
    have rep : List.ofFn (row X) = incidenceInput X Y := by
      change List.ofFn (n := 13+13) (row X) = List.ofFn _ ++ List.ofFn _
      rw [List.ofFn_add]
      congr 1 <;> apply congrArg List.ofFn <;> funext i
      · change row X (Fin.castAdd 13 i) = decide (i ∈ X)
        simp only [row,apart,cinj,false_and]
        simp
      · have ef : (∃ _ : Fin 13, False) ↔ False := ⟨fun h => h.elim (fun _ h => h), False.elim⟩
        simp only [row,fun p => Ne.symm (apart p i),ninj,and_false,ef,false_or]
        apply decide_eq_decide.mpr
        change (∃ w, i=w ∧ A X w) ↔ i ∈ Y
        simpa using (hy i).symm
    rintro t ht h
    exact neg X hc hd' (Or.inr ⟨t,ht,rep ▸ h⟩)
  let F (t : Finset ℕ) (x : List Bool) := ∀ i ∈ t, val ds i x = true
  have evalSet (t : List ℕ) (x : List Bool) : F t.toFinset x ↔ fires ds t x :=
    ⟨fun h i hi => h i (List.mem_toFinset.mpr hi), fun h i hi => h i (List.mem_toFinset.mp hi)⟩
  let V := T.toFinset.image List.toFinset
  let covers (U : Finset (Finset ℕ)) := ∀ p l, p ∈ S l → ∃ t ∈ U, F t (incidenceInput {p} {l})
  have coverV : covers V := by
    intro p l h; obtain ⟨t,ht,win⟩ := pos p l h
    exact ⟨_,Finset.mem_image_of_mem _ (List.mem_toFinset.mpr ht),(evalSet _ _).2 win⟩
  obtain ⟨U,sub,minimal⟩ := exists_minimal_le_of_wellFoundedLT covers V coverV
  have capU : U.card ≤ T.length := (Finset.card_le_card sub).trans
    (Finset.card_image_le.trans (List.toFinset_card_le T))
  have budgetU := (Nat.add_le_add_left (Nat.mul_le_mul_left 2 capU) B.size).trans cost
  have origin (t : Finset ℕ) (ht : t ∈ U) : ∃ s ∈ T, s.toFinset = t := by
    obtain ⟨s,hs,e⟩ := Finset.mem_image.mp (sub ht)
    exact ⟨s,List.mem_toFinset.mp hs,e⟩
  have witness (t : Finset ℕ) (ht : t ∈ U) : ∃ p l, p ∈ S l ∧ F t (incidenceInput {p} {l}) ∧
      ∀ u ∈ U, u ≠ t → ¬F u (incidenceInput {p} {l}) := by
    have notCover : ¬covers (U.erase t) := fun c =>
      (Finset.notMem_erase t U) ((minimal.2 c (Finset.erase_subset _ _)) ht)
    change ¬(∀ p l, p ∈ S l → ∃ s ∈ U.erase t, F s (incidenceInput {p} {l})) at notCover
    push Not at notCover
    obtain ⟨p,l,hpl,miss⟩ := notCover
    obtain ⟨s,hs,hsw⟩ := minimal.1 p l hpl
    have rest := fun u (hu : u ∈ U) (ne : u ≠ t) => miss u (Finset.mem_erase.mpr ⟨ne,hu⟩)
    have e : s=t := by by_contra ne; exact rest s hs ne hsw
    exact ⟨p,l,hpl,e ▸ hsw,rest⟩
  have inputs (t : Finset ℕ) (ht : t ∈ U) : t.card ≤ 2 ∧ t ⊆ Finset.range (26+B.size) := by
    obtain ⟨s,hs,rfl⟩ := origin t ht
    refine ⟨(List.toFinset_card_le _).trans (arity _ hs),?_⟩
    obtain ⟨p,l,_,win,_⟩ := witness _ ht
    intro i hi
    apply Finset.mem_range.mpr
    have h := win i hi
    have full : (run ds (incidenceInput {p} {l})).length = 26+B.size := by
      rw [len]; rfl
    exact lt_of_not_ge (fun ge => by
      change (run ds _).getD i false = true at h
      rw [List.getD_eq_default _ _ (full ▸ ge)] at h; contradiction)
  have safeU (X Y : Finset (Fin 13)) (hmf : IsMaximalFalse S X Y)
      (hd : ¬InNoLine S X ∨ ¬InNoPencil S Y) (t) (ht : t ∈ U) : ¬F t (incidenceInput X Y) := by
    obtain ⟨s,hs,rfl⟩ := origin t ht
    exact fun h => safe X Y hmf hd s hs ((evalSet _ _).1 h)
  have monoWire (X Y : Fin 26 → Bool) (inc : ∀ i, X i = true → Y i = true)
      (gs : List Gate) (hm' : good gs) : ∀ i,
      val gs i (List.ofFn X) = true → val gs i (List.ofFn Y) = true := by
    induction gs using List.reverseRecOn with
    | nil =>
      intro i
      change (List.ofFn X).getD i false = true → (List.ofFn Y).getD i false = true
      by_cases hi : i < 26
      · rw [List.getD_eq_getElem _ _ (List.length_ofFn ▸ hi),
          List.getD_eq_getElem _ _ (List.length_ofFn ▸ hi),List.getElem_ofFn,List.getElem_ofFn]
        exact inc _
      · rw [List.getD_eq_default _ _ (List.length_ofFn ▸ Nat.le_of_not_gt hi)]
        exact fun h => Bool.noConfusion h
    | append_singleton gs g ih =>
      have pre := ih (fun z hz => hm' z (List.mem_append_left _ hz))
      have op := (hm' g (List.mem_append_right _ (List.mem_singleton_self _))).1
      intro i
      by_cases last : i = 26+gs.length
      · subst i
        rw [atGate _ _ _ List.length_ofFn,atGate _ _ _ List.length_ofFn]
        rcases op with ha|ho
        · rw [ha,opAnd,opAnd,List.all_eq_true,List.all_eq_true,List.forall_mem_map,List.forall_mem_map]
          exact fun all j hj => pre j (all j hj)
        · rw [ho,opOr,opOr,List.any_eq_true,List.any_eq_true]
          rintro ⟨b,hb,h⟩; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
          exact ⟨_,List.mem_map_of_mem hj,pre j h⟩
      · rw [other _ _ _ List.length_ofFn i last,other _ _ _ List.length_ofFn i last]
        exact pre i
  have separates : ∀ p v : Fin 13, v ≠ p → ∃ w, v ∈ S w ∧ p ∉ S w := by decide
  have off (p l : Fin 13) (hnon : p ∉ S l) (t) (ht : t ∈ U) : ¬F t (incidenceInput {p} {l}) := by
    have avoids (w : Fin 13) (h : p ∉ S w) : A {p} w := by
      intro q hq; obtain rfl := Finset.mem_singleton.mp hq; exact fun he => h ((memS _ _).2 he)
    have closed (v : Fin 13) (hv : v ∉ ({p} : Finset _)) : ∃ w, A {p} w ∧ E v w := by
      obtain ⟨w,hw,hp⟩ := separates p v (fun h => hv (Finset.mem_singleton.mpr h))
      exact ⟨w,avoids w hp,(memS _ _).1 hw⟩
    have rowFalse := neg {p} closed (Or.inl ⟨p,fun q hq => (Finset.mem_singleton.mp hq) ▸ reflE p⟩)
    have lifts (i) (on : pair p l i = true) : row {p} i = true := by
      rcases of_decide_eq_true on with h | h
      · exact decide_eq_true (Or.inl ⟨p,Finset.mem_singleton_self _,h⟩)
      · exact decide_eq_true (Or.inr ⟨l,h,avoids _ hnon⟩)
    obtain ⟨s,hs,rfl⟩ := origin t ht
    rw [← posInput]; intro win
    exact rowFalse (Or.inr ⟨s,hs,fun i hi => monoWire _ _ lifts ds md i (win i (List.mem_toFinset.mpr hi))⟩)
  by_cases small : U.card ≤ 12
  · let flags := PEqualNP.HeptadCover.incidences S
    let wins (t : Finset ℕ) := flags.filter fun e => F t (incidenceInput {e.1} {e.2})
    have allCovered : flags ⊆ U.biUnion wins := by
      intro e he
      obtain ⟨t,ht,h⟩ := minimal.1 _ _ (Finset.mem_filter.mp he).2
      exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_filter.mpr ⟨he,h⟩⟩
    have total : flags.card = 52 := by decide
    have big : ∃ t ∈ U, (wins t).card ≥ 5 := by
      by_contra! h
      have bound := Finset.card_biUnion_le_card_mul U wins 4 (fun t ht => Nat.le_of_lt_succ (h t ht))
      have hh := Finset.card_le_card allCovered
      rw [total] at hh
      exact (by decide : ¬52 ≤ 12*4) ((hh.trans bound).trans (Nat.mul_le_mul_right 4 small))
    obtain ⟨t,ht,five⟩ := big
    let H := wins t
    let pencil (p : Fin 13) := Finset.univ.filter fun l => p ∈ S l
    have lineSize : ∀ l, (S l).card ≤ 4 := by decide
    have pencilSize : ∀ p, (pencil p).card ≤ 4 := by decide
    have meet : ∀ p q : Fin 13, p ≠ q → ((pencil p) ∩ (pencil q)).card ≤ 1 := by decide
    have cross : ∃ e ∈ H, ∃ f ∈ H, e.1 ∉ S f.2 := by
      by_contra! allInc
      obtain ⟨e,he⟩ := Finset.card_pos.mp ((by decide : 0 < 5).trans_le five)
      change e ∈ H at he
      by_cases one : ∀ a ∈ H, a.1 = e.1
      · have le : H.card ≤ (pencil e.1).card := Finset.card_le_card_of_injOn Prod.snd
          (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _,allInc e he a ha⟩)
          (fun a ha b hb eq => Prod.ext ((one a ha).trans (one b hb).symm) eq)
        exact (by decide : ¬5 ≤ 4) ((five.trans le).trans (pencilSize _))
      · push Not at one
        obtain ⟨a,ha,ne⟩ := one
        have mem (b) (hb : b ∈ H) : b.2 ∈ pencil a.1 ∩ pencil e.1 :=
          Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,allInc a ha b hb⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,allInc e he b hb⟩⟩
        have le : H.card ≤ (S e.2).card := Finset.card_le_card_of_injOn Prod.fst
          (fun b hb => allInc b hb e he)
          (fun b hb c hc eq => Prod.ext eq (Finset.card_le_one.mp (meet _ _ ne) _ (mem b hb) _ (mem c hc)))
        exact (by decide : ¬5 ≤ 4) ((five.trans le).trans (lineSize _))
    obtain ⟨e,he,f,hf,bad⟩ := cross
    obtain ⟨p,l,h,miss⟩ := few B U md small budgetU inputs witness safeU
      ⟨t,ht,five,e,he,f,hf,bad,off _ _ bad t ht⟩
    obtain ⟨t,ht,win⟩ := minimal.1 p l h
    exact miss t ht win
  · have ge : 13 ≤ U.card := Nat.lt_of_not_ge small
    have pre : B.size + 26 ≤ 38 + 26 :=
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ge) B.size).trans budgetU
    have bound := many B U md (Nat.le_of_add_le_add_right pre) ge inputs witness safeU minimal.1
    exact (Nat.not_succ_le_self 64) (bound.trans budgetU)
