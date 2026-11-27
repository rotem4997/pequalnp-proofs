import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4789_407
    (geometry : let D : Finset (Fin 13) := {0,1,3,9}
    let I (p l : Fin 13) := ∃ d ∈ D, p=l+d
    let O (s : Finset (Fin 13)) (l : Fin 13) := ∀ p ∈ s, ¬I p l
    let tag (s : Finset (Fin 13)) :=
      14*s.card + ((List.finRange 13).countP fun l => decide (∀ p ∈ s, (p-l).val ∉ ([0,1,3,9] : List ℕ))) ∈
      ([13,23,34,45,86,127,182] : List ℕ)
    ∀ s, tag s ↔ ((∀ p ∉ s, ∃ l, O s l ∧ I p l) ∧
      ((∃ l, ∀ p ∈ s, I p l) ∨ ∃ p, ∀ l, O s l → I p l)))
    (obstruction : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); let tag (s : Finset (Fin 13)) :=
      14*s.card + ((List.finRange 13).countP fun l => decide (∀ p ∈ s, (p-l).val ∉ ([0,1,3,9] : List ℕ))) ∈
      ([13,23,34,45,86,127,182] : List ℕ);
    ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     ∀ (x7 : Finset x1 → x5), (∀ s i, x7 s i=true ↔
      (∃ p ∈ s, i=Fin.castAdd 13 p) ∨ ∃ l, i=Fin.natAdd 13 l ∧ x4 s l) →
    22 ≤ x9.size → ∀ T : Finset (ℕ × ℕ), 2 ≤ T.card → T.card ≤ 21 →
    (∀ e ∈ T, x12 (x13 e) ∧ ¬x12 (x11 e.1) ∧ ¬x12 (x11 e.2)) →
    (∀ s, tag s → ∃ e ∈ T, x13 e (x7 s)=false) →
    (∀ e ∈ T, ∃ s, tag s ∧ x13 e (x7 s)=false ∧ ∀ f ∈ T, f≠e → x13 f (x7 s)=true) →
    65 ≤ x9.size + 2*T.card) :
    let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     have x14 : Finset (ℕ × ℕ) → Prop := fun (x14 : Finset (ℕ × ℕ)) => ∀ (x15 : Finset x1), x8 x15 → ∃ x17 ∈ x14, ¬x13 x17 (x7 x15) = Bool.true;     ∀ (x15 : Finset (ℕ × ℕ)), (2 : ℕ) ≤ x15.card → x9.size + (2 : ℕ) * x15.card ≤ (64 : ℕ) → (∀ x18 ∈ x15, x12 (x13 x18) ∧ ¬x12 (x11 x18.1) ∧ ¬x12 (x11 x18.2)) → x14 x15 → (∀ x20 ∈ x15, ¬x14 (x15.erase x20)) → False := by
  -- Tracing a binary gate backwards adds at most one live coordinate.
  have support : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ W : Finset ℕ,
    ∃ S : Finset (Fin n), S.card ≤ C.size + W.card ∧ ∀ x y : Fin n → Bool,
      (∀ i ∈ S, x i=true → y i=true) → ∀ w ∈ W,
      (C.wires (List.ofFn x ++ [true,false])).getD w false = true →
      (C.wires (List.ofFn y ++ [true,false])).getD w false = true := by
    intro n C legal W
    let step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
    have skip (w : List Bool) (b : Bool) (j : ℕ) (h : j ≠ w.length) :
        (w ++ [b]).getD j false = w.getD j false := by
      by_cases small : j < w.length
      · exact List.getD_append _ _ _ _ small
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
    have plan (gs : List Gate) (good : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
        (l : ℕ) (T : Finset ℕ) :
        ∃ P : Finset ℕ, P.card ≤ gs.length + T.card ∧ ∀ a b : List Bool, a.length=l → b.length=l →
          (∀ j ∈ P, a.getD j false=true → b.getD j false=true) → ∀ j ∈ T,
          (gs.foldl step a).getD j false=true → (gs.foldl step b).getD j false=true := by
      induction gs generalizing l T with
      | nil => exact ⟨T,by simp,fun _ _ _ _ h => h⟩
      | cons g gs ih =>
        obtain ⟨U,cost,act⟩ := ih (fun v hv => good v (List.mem_cons_of_mem _ hv)) (l+1) T
        obtain ⟨op,arity⟩ := good g List.mem_cons_self
        by_cases hit : l ∈ U
        · let P := U.erase l ∪ g.inputs.toFinset
          refine ⟨P,?_,?_⟩
          · have c1 := Finset.card_union_le (U.erase l) g.inputs.toFinset
            have c2 := Finset.card_erase_add_one hit
            have c3 := List.toFinset_card_le g.inputs
            change (U.erase l ∪ g.inputs.toFinset).card ≤ (gs.length+1)+T.card
            omega
          · intro a b ha hb h
            apply act (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
            intro j hj
            by_cases eq : j=l
            · subst j
              have last (w : List Bool) (hl : w.length=l) :
                  (step w g).getD l false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
                rw [← hl]; simp [step]
              have rel (i) (hi : i∈g.inputs) := h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
              rw [last a ha,last b hb]
              rcases op with eo | eo
              · rw [eo]
                change (g.inputs.map fun i => a.getD i false).all id=true → (g.inputs.map fun i => b.getD i false).all id=true
                simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
                exact fun hh i hi => rel i hi (hh i hi)
              · rw [eo]
                change (g.inputs.map fun i => a.getD i false).any id=true → (g.inputs.map fun i => b.getD i false).any id=true
                simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
                rintro ⟨i,hi,hv⟩
                exact ⟨i,hi,rel i hi hv⟩
            · unfold step
              rw [skip _ _ _ (by omega),skip _ _ _ (by omega)]
              exact h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hj⟩))
        · refine ⟨U,by simp only [List.length_cons]; omega,?_⟩
          intro a b ha hb h
          apply act (step a g) (step b g) (by simp [step,ha]) (by simp [step,hb])
          intro j hj
          have ne : j≠l := fun z => hit (z ▸ hj)
          unfold step
          rw [skip _ _ _ (by omega),skip _ _ _ (by omega)]
          exact h _ hj
    obtain ⟨P,cap,a⟩ := plan C.gates legal (n+2) W
    let S := Finset.univ.filter (fun i : Fin n => i.val ∈ P)
    have number : S.card ≤ P.card := by
      rw [← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hi).2
    refine ⟨S,number.trans cap,?_⟩
    intro x y rel
    apply a (List.ofFn x ++ [true,false]) (List.ofFn y ++ [true,false]) (by simp) (by simp)
    intro j hj
    by_cases small : j<n
    · let i : Fin n := ⟨j,small⟩
      have get (z : Fin n → Bool) : (List.ofFn z ++ [true,false]).getD j false = z i := by
        rw [List.getD_append _ _ _ _ (by simpa using small),List.getD_eq_getElem _ _ (by simpa using small)]
        exact List.getElem_ofFn _
      rw [get x,get y]
      exact rel i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
    · have tail (z : Fin n → Bool) : (List.ofFn z ++ [true,false]).getD j false =
            [true,false].getD (j-n) false := by
          rw [List.getD_append_right _ _ _ _ (by simp; omega)]; simp
      rw [tail,tail]; exact id
  intro V D I O X edge row good C legal wire allEdges pair covers T two budget right cover minimal
  let tag (s : Finset (Fin 13)) :=
      14*s.card + ((List.finRange 13).countP fun l => decide (∀ p ∈ s, (p-l).val ∉ ([0,1,3,9] : List ℕ))) ∈
      ([13,23,34,45,86,127,182] : List ℕ)
  have shape (s) : tag s ↔ good s := geometry s
  have incident (i : V) : I i i := ⟨0,by simp [D],by simp⟩
  have ends : good ∅ ∧ good Finset.univ := by
    constructor
    · exact ⟨fun i _ => ⟨i,fun j hj => False.elim (Finset.notMem_empty j hj),incident i⟩,
          Or.inl ⟨0,fun j hj => False.elim (Finset.notMem_empty j hj)⟩⟩
    · exact ⟨fun i hi => False.elim (hi (Finset.mem_univ i)),
          Or.inr ⟨0, fun l hl => False.elim (hl l (Finset.mem_univ l) (incident l))⟩⟩
  -- Two rejecting clauses together need all 26 input coordinates.
  obtain ⟨a,ha,offA⟩ := cover ∅ ends.1
  obtain ⟨b,hb,offB⟩ := cover Finset.univ ends.2
  let W : Finset ℕ := {a.1,a.2,b.1,b.2}
  have wc : W.card ≤ 4 := by
    have e1 := Finset.card_insert_le a.1 ({a.2,b.1,b.2} : Finset ℕ)
    have e2 := Finset.card_insert_le a.2 ({b.1,b.2} : Finset ℕ)
    have e3 := Finset.card_insert_le b.1 ({b.2} : Finset ℕ)
    have e4 : ({b.2} : Finset ℕ).card=1 := Finset.card_singleton _
    dsimp only [W]; omega
  obtain ⟨S,bound,acts⟩ := support 26 C legal W
  have loss (e : ℕ × ℕ) (included : e.1∈W ∧ e.2∈W) (on : e ∈ T) (p : V)
      (s : Finset V) (off : ¬pair e (row s)=true)
      (le : ∀ i ∈ S, edge p p i=true → row s i=true) : False := by
    have yes : pair e (edge p p) = true := (right e on).1 p p (incident p)
    apply off
    rcases Bool.or_eq_true_iff.mp yes with hp | hp
    · exact Bool.or_eq_true_iff.mpr (.inl (acts _ _ le _ included.1 hp))
    · exact Bool.or_eq_true_iff.mpr (.inr (acts _ _ le _ included.2 hp))
  have atLeft (p : V) (i : Fin 26) (ne : i ≠ Fin.castAdd 13 p) (on : edge p p i=true) :
      row ∅ i=true := by
    have h : i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 p := of_decide_eq_true on
    exact decide_eq_true (Or.inr ⟨p,h.resolve_left ne,fun j hj => False.elim (Finset.notMem_empty j hj)⟩)
  have atRight (p : V) (i : Fin 26) (ne : i ≠ Fin.natAdd 13 p) (on : edge p p i=true) :
      row Finset.univ i=true := by
    have h : i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 p := of_decide_eq_true on
    exact decide_eq_true (Or.inl ⟨p,Finset.mem_univ p,h.resolve_right ne⟩)
  have all : S=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    have splitIndex : ∀ k : Fin 26, (∃ p : Fin 13, k=Fin.castAdd 13 p) ∨ (∃ p : Fin 13, k=Fin.natAdd 13 p) := by decide +kernel
    rcases splitIndex i with ⟨p,rfl⟩ | ⟨p,rfl⟩
    · by_contra absent
      have both : a.1∈W ∧ a.2∈W := ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
      have miss (j : Fin 26) (hj : j∈S) : j≠Fin.castAdd 13 p := by
        intro eq
        exact absent ((congrArg (fun k : Fin 26 => k ∈ S) eq).mp hj)
      have rel (j : Fin 26) (hj : j∈S) (hpos : edge p p j=true) : row ∅ j=true :=
        atLeft p j (miss j hj) hpos
      have local1 := loss a
      have local2 := local1 both
      have local3 := local2 ha
      have local4 := local3 p
      have local5 := local4 (∅ : Finset V)
      have local6 := local5 offA
      exact local6 rel
    · by_contra absent
      have both : b.1∈W ∧ b.2∈W := by simp only [W,Finset.mem_insert,Finset.mem_singleton]; tauto
      have miss (j : Fin 26) (hj : j∈S) : j≠Fin.natAdd 13 p := by
        intro eq
        exact absent ((congrArg (fun k : Fin 26 => k ∈ S) eq).mp hj)
      have rel (j : Fin 26) (hj : j∈S) (hpos : edge p p j=true) : row Finset.univ j=true :=
        atRight p j (miss j hj) hpos
      have local1 := loss b
      have local2 := local1 both
      have local3 := local2 hb
      have local4 := local3 p
      have local5 := local4 (Finset.univ : Finset V)
      have local6 := local5 offB
      exact local6 rel
  have cardinal : S.card = 26 := by simp [all]
  have low : 22 ≤ C.size := by omega
  have upper : T.card ≤ 21 := by omega
  -- Each indispensable clause has a private negative input.
  have privateRow (e) (he : e∈T) :
      ∃ s, tag s ∧ pair e (row s)=false ∧ ∀ f ∈ T, f≠e → pair f (row s)=true := by
    have gone : ¬∀ s, good s → ∃ f ∈ T.erase e, ¬pair f (row s)=true := minimal e he
    push_neg at gone
    obtain ⟨s,hs,keep⟩ := gone
    obtain ⟨f,hf,reject⟩ := cover s hs
    have equal : f=e := by
      by_contra ne
      exact reject (keep _ (Finset.mem_erase.mpr ⟨ne,hf⟩))
    subst f
    exact ⟨s,(shape s).mpr hs,Bool.eq_false_iff.mpr reject,fun f hf nf => keep _ (Finset.mem_erase.mpr ⟨nf,hf⟩)⟩
  have rejectAll (s) (hs : tag s) : ∃ e ∈ T, pair e (row s)=false := by
    obtain ⟨e,he,reject⟩ := cover s ((shape s).mp hs)
    exact ⟨e,he,Bool.eq_false_iff.mpr reject⟩
  have rowSpec (s : Finset V) (i : Fin 26) : row s i=true ↔
      (∃ p ∈ s, i=Fin.castAdd 13 p) ∨ ∃ l, i=Fin.natAdd 13 l ∧ O s l :=
    ⟨of_decide_eq_true,decide_eq_true⟩
  have tmp1 := obstruction C legal row rowSpec low T two upper
  have tmp2 := tmp1 right
  have tmp3 := tmp2 rejectAll
  have result := tmp3 privateRow
  omega
