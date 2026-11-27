import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Take enough disjoint copies of a putative one-gate saving for it to exceed
-- any square-root boundary loss. The matching-cover argument follows PR 5142.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3503_41
    (coarse : ∃ K : ℕ, ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) → (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      E.card + M.card ≤ C.size + 1 + K * Nat.sqrt (n+m+1))
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ (D : Circuit) (S : Bool → Finset ℕ),
        IsAO2 (n+m) D ∧ D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        let g := NestedCover.gateAt D
        (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
          ∃ i < D.size, w = n+m+i ∧ (g i).op = GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ S t) ∧
        ∀ i < D.size, (g i).op = GateOp.and →
          ∃ a b t, (g i).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ (x15 ∈ x10 ∧ x16 ∈ x11 ∨ x15 ∈ x11 ∧ x16 ∈ x10) := by
  classical
  have saturate {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (r : α → β → Prop) (A : Finset α) (B : Finset β)
      (cov : ∀ a b, r a b → a ∈ A ∨ b ∈ B)
      (minimal : ∀ (X : Finset α) (Y : Finset β),
        (∀ a b, r a b → a ∈ X ∨ b ∈ Y) → A.card+B.card ≤ X.card+Y.card) :
      ∃ f : A → β, Function.Injective f ∧ ∀ a : A, r a (f a) ∧ f a ∉ B := by
    classical
    let adj (a : A) := Finset.univ.filter fun b => r a b ∧ b ∉ B
    have hall (s : Finset A) : s.card ≤ (s.biUnion adj).card := by
      let X : Finset α := s.map (Function.Embedding.subtype _)
      let Y := s.biUnion adj
      have Xsub : X ⊆ A := by
        intro a ha
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
        exact i.property
      have replacement : ∀ a b, r a b → a ∈ A \ X ∨ b ∈ B ∪ Y := by
        intro a b h
        by_cases hb : b ∈ B
        · exact Or.inr (Finset.mem_union_left _ hb)
        have ha := (cov a b h).resolve_right hb
        by_cases hx : a ∈ X
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
          exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hb⟩⟩))
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨ha,hx⟩)
      have bound := minimal _ _ replacement
      have card := Finset.card_sdiff_add_card_eq_card Xsub
      have union := Finset.card_union_le B Y
      have sizeX : X.card = s.card := Finset.card_map _
      change s.card ≤ Y.card
      omega
    obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
    exact ⟨f,inj,fun a => (Finset.mem_filter.mp (mem a)).2⟩

  have matchingCover (n m : ℕ) (E : Finset (Fin n × Fin m)) :
      ∃ (M : Finset (Fin n × Fin m)) (A : Finset (Fin n)) (B : Finset (Fin m)),
        M ⊆ E ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin m)) ∧
        Set.InjOn Prod.snd (M : Set (Fin n × Fin m)) ∧
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ A.card+B.card ≤ M.card := by
    classical
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) :=
      ∀ a b, (a,b) ∈ E → a ∈ A ∨ b ∈ B
    have has : ∃ k, ∃ A B, cover A B ∧ A.card+B.card = k :=
      ⟨_,Finset.univ,∅,fun a _ _ => Or.inl (Finset.mem_univ a),rfl⟩
    obtain ⟨A,B,cov,least⟩ := Nat.find_spec has
    have minAB (X Y) (h : cover X Y) : A.card+B.card ≤ X.card+Y.card := by
      rw [least]
      exact Nat.find_min' has ⟨X,Y,h,rfl⟩
    obtain ⟨f,fi,hf⟩ := saturate (fun (a : Fin n) (b : Fin m) => (a,b) ∈ E) A B cov minAB
    obtain ⟨g,gi,hg⟩ := saturate (fun (b : Fin m) (a : Fin n) => (a,b) ∈ E) B A
      (fun b a h => (cov a b h).symm) (fun Y X h => by
        simpa only [Nat.add_comm] using minAB X Y (fun a b he => (h b a he).symm))
    let pair : A ⊕ B → Fin n × Fin m := Sum.elim (fun a => (a.val,f a)) (fun b => (g b,b.val))
    have first : Function.Injective (Prod.fst ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (Subtype.ext eq)
        | inr b => exact False.elim ((hg b).2 ((show a.val = g b from eq) ▸ a.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hg b).2 ((show a.val = g b from eq.symm) ▸ a.property))
        | inr b' => exact congrArg Sum.inr (gi eq)
    have second : Function.Injective (Prod.snd ∘ pair) := by
      intro i j eq
      cases i with
      | inl a =>
        cases j with
        | inl a' => exact congrArg Sum.inl (fi eq)
        | inr b => exact False.elim ((hf a).2 ((show b.val = f a from eq.symm) ▸ b.property))
      | inr b =>
        cases j with
        | inl a => exact False.elim ((hf a).2 ((show b.val = f a from eq) ▸ b.property))
        | inr b' => exact congrArg Sum.inr (Subtype.ext eq)
    let M := Finset.univ.image pair
    refine ⟨M,A,B,?_,?_,?_,fun e he => cov _ _ he,?_⟩
    · intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      cases i with
      | inl a => exact (hf a).1
      | inr b => exact (hg b).1
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (first eq)
    · intro e he e' he' eq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he'
      exact congrArg pair (second eq)
    · simp [M,Finset.card_image_of_injective _ (Function.Injective.of_comp first)]

  have szEq (T : Circuit) : T.size = T.gates.length := rfl
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have trace (gs : List Gate) (u : List Bool) :
      ∃ t : List Bool, gs.foldl step u = u ++ t ∧ t.length = gs.length := by
    induction gs generalizing u with
    | nil => exact ⟨[],by simp,rfl⟩
    | cons g gs ih =>
      obtain ⟨t,ht,hlen⟩ := ih (step u g)
      exact ⟨_ :: t,by simpa only [List.foldl_cons,step,List.append_assoc,List.cons_append,List.nil_append] using ht,
        by simp [hlen]⟩

  let legal (n : ℕ) (gs : List Gate) := ∀ i (h : i < gs.length),
    let g := gs[i]
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ u ∈ g.inputs, u < n+i

  have legal_iff (C : Circuit) (n : ℕ) : legal n C.gates ↔ IsAO2 n C := by
    have atG (i : ℕ) (h : i < C.gates.length) : gateAt C i = C.gates[i] := List.getD_eq_getElem _ _ h
    constructor
    · intro h
      refine ⟨?_,?_,?_⟩
      · intro g hg
        obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).1
      · intro i hi u hu
        rw [atG i hi] at hu
        exact (h i hi).2.2 u hu
      · intro g hg
        obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).2.1
    · intro h i hi
      have e := List.getElem_mem hi
      exact ⟨h.1 _ e,h.2.2 _ e,fun u hu => h.2.1 i hi u (by rwa [atG i hi])⟩

  have appendLegal {n : ℕ} {p q : List Gate} (a : legal n p) (b : legal (n+p.length) q) :
      legal n (p++q) := by
    intro i hi
    by_cases hl : i < p.length
    · simpa only [List.getElem_append_left hl] using a i hl
    · have hr : i-p.length < q.length := by simp only [List.length_append] at hi; omega
      have add : n+p.length+(i-p.length) = n+i := by omega
      simpa only [List.getElem_append_right (by omega : p.length ≤ i),add] using b (i-p.length) hr

  let shift (a b o : ℕ) (f : Fin a → Fin b) (i : ℕ) :=
    if h : i < a then (f ⟨i,h⟩).val else b+o+(i-a)

  let rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩

  have shiftedLegal {a b o : ℕ} {gs : List Gate} (h : legal a gs) (f : Fin a → Fin b) :
      legal (b+o) (gs.map (rename (shift a b o f))) := by
    intro i hi
    have hi' : i < gs.length := by simpa using hi
    simp only [List.getElem_map,rename,List.length_map,List.mem_map]
    refine ⟨(h i hi').1,(h i hi').2.1,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    have bound := (h i hi').2.2 z hz
    dsimp [shift]
    split
    next h => have := (f ⟨z,h⟩).isLt; omega
    next => omega

  have simulation {a b o : ℕ} (f : Fin a → Fin b) (y : Fin b → Bool)
      (prior : List Bool) (lo : prior.length = o) (gs : List Gate) :
      ∃ t : List Bool, gs.foldl step (List.ofFn (fun u => y (f u))) = List.ofFn (fun u => y (f u)) ++ t ∧
        (gs.map (rename (shift a b o f))).foldl step (List.ofFn y ++ prior) = (List.ofFn y ++ prior) ++ t ∧
          t.length = gs.length := by
    let U := List.ofFn (fun u => y (f u))
    let V := List.ofFn y ++ prior
    have reads (t : List Bool) (i : ℕ) : (U ++ t).getD i false = (V ++ t).getD (shift a b o f i) false := by
      by_cases hi : i < a
      · dsimp only [shift]; rw [dite_eq_left hi]
        have hright := (f ⟨i,hi⟩).isLt
        simp only [U,V,List.append_assoc,List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using hi),
            List.getElem?_append_left (by simpa only [List.length_ofFn] using hright),
            List.getElem?_ofFn,List.getElem?_ofFn,dite_eq_left hi,dite_eq_left hright]
      · simp only [shift,dite_eq_right hi]
        rw [List.getD_append_right _ _ _ _ (by simp only [U,List.length_ofFn]; omega),
            List.getD_append_right _ _ _ _ (by simp only [V,List.length_append,List.length_ofFn,lo];omega)]
        simp [U,V,lo]
    have run (ls : List Gate) (z : List Bool) : ∃ t : List Bool,
        ls.foldl step (U++z) = U++t ∧ (ls.map (rename (shift a b o f))).foldl step (V++z) = V++t ∧
        t.length=z.length+ls.length := by
      induction ls generalizing z with
      | nil => exact ⟨z,rfl,rfl,by simp⟩
      | cons g ls ih =>
        let bit := g.op.eval (g.inputs.map (fun i => (U++z).getD i false))
        have eqbit : g.op.eval (g.inputs.map (fun i => (U++z).getD i false)) =
            (rename (shift a b o f) g).op.eval ((rename (shift a b o f) g).inputs.map (fun i => (V++z).getD i false)) := by
          congr 1
          simp only [rename,List.map_map]
          apply List.map_congr_left
          intro i _
          exact reads z i
        obtain ⟨v,h1,h2,hl⟩ := ih (z++[bit])
        refine ⟨v,?_,?_,?_⟩
        · simpa only [List.foldl_cons,step,List.append_assoc,bit] using h1
        · change (ls.map _).foldl step ((V++z)++[_])=_
          rw [←eqbit,List.append_assoc]
          exact h2
        · simp only [List.length_append,List.length_cons,List.length_nil] at hl ⊢; omega
    simpa only [List.append_nil,List.length_nil,Nat.zero_add] using run gs []

  have copy (a b : ℕ) (C A : Circuit) (hf : IsAO2 a C) (ha : IsAO2 b A)
      (ho : C.output < a+C.size) (f : Fin a → Fin b) : ∃ B : Circuit,
      IsAO2 b B ∧ B.size = A.size+C.size ∧ B.output < b+B.size ∧
      (∀ y, circuitFun b B y = circuitFun a C (fun u => y (f u))) ∧
      ∀ y : Fin b → Bool, ∀ i < b+A.size, (B.wires (List.ofFn y)).getD i false = (A.wires (List.ofFn y)).getD i false := by
    let f' := shift a b A.size f
    let B : Circuit := ⟨A.gates ++ C.gates.map (rename f'), f' C.output⟩
    have sz : B.size = A.size+C.size := by simp [B,szEq]
    have valid : B.output < b+B.size := by
      rw [sz]; change f' C.output < _
      dsimp [f',shift]; split
      next h => have := (f ⟨C.output,h⟩).isLt; omega
      next => omega
    refine ⟨B,(legal_iff B b).mp (appendLegal ((legal_iff A b).mpr ha) (shiftedLegal ((legal_iff C a).mpr hf) f)),sz,valid,?_,?_⟩
    · intro y
      obtain ⟨pre,old,lp⟩ := trace A.gates (List.ofFn y)
      obtain ⟨t,source,placed,_⟩ := simulation f y pre lp C.gates
      change (C.gates.map (rename f')).foldl step (List.ofFn y ++ pre) = (List.ofFn y ++ pre) ++ t at placed
      change ((A.gates ++ C.gates.map (rename f')).foldl step (List.ofFn y)).getD (f' C.output) false =
        (C.gates.foldl step (List.ofFn (fun u => y (f u)))).getD C.output false
      rw [List.foldl_append,old,placed,source]
      by_cases hi : C.output < a
      · simp only [f',shift,dite_eq_left hi,List.append_assoc,List.getD_eq_getElem?_getD]
        have hr := (f ⟨C.output,hi⟩).isLt
        rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using hr),
            List.getElem?_append_left (by simpa only [List.length_ofFn] using hi),
            List.getElem?_ofFn,List.getElem?_ofFn,dite_eq_left hr,dite_eq_left hi]
      · simp only [f',shift,dite_eq_right hi]
        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append,List.length_ofFn,lp,szEq];omega),
            List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn];omega)]
        simp [lp,szEq]
    · intro y i hi
      obtain ⟨pre,old,lp⟩ := trace A.gates (List.ofFn y)
      obtain ⟨t,_,placed,_⟩ := simulation f y pre lp C.gates
      change (C.gates.map (rename f')).foldl step (List.ofFn y ++ pre) = (List.ofFn y ++ pre) ++ t at placed
      change ((A.gates ++ C.gates.map (rename f')).foldl step (List.ofFn y)).getD i false = _
      rw [List.foldl_append,old,placed,List.getD_append _ _ _ _ (by simpa [lp,szEq] using hi)]
      exact congrArg (fun w : List Bool => w.getD i false) old.symm

  have join (b : ℕ) (B : Circuit) (hb : IsAO2 b B) (i j : ℕ) (hi : i < b+B.size) (hj : j < b+B.size) :
      ∃ D : Circuit, IsAO2 b D ∧ D.size = B.size+1 ∧ D.output < b+D.size ∧
        ∀ y : Fin b → Bool, circuitFun b D y =
        ((B.wires (List.ofFn y)).getD i false || (B.wires (List.ofFn y)).getD j false) := by
    let D : Circuit := ⟨B.gates ++ [⟨.or,[i,j]⟩], b+B.size⟩
    have sz : D.size = B.size+1 := by simp [D,szEq]
    have tail : legal (b+B.gates.length) [⟨.or,[i,j]⟩] := by
      intro v hv
      have h : v=0 := by simpa using hv
      subst v
      refine ⟨Or.inr rfl,rfl,?_⟩
      intro t ht
      change t ∈ [i,j] at ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl
      · exact hi
      · exact hj
    refine ⟨D,(legal_iff D b).mp (appendLegal ((legal_iff B b).mpr hb) tail),sz,by change b+B.size < b+D.size; omega,?_⟩
    intro y
    obtain ⟨p,hp,lp⟩ := trace B.gates (List.ofFn y)
    let w := B.wires (List.ofFn y)
    have len : w.length = b+B.size := by
      change (B.gates.foldl step (List.ofFn y)).length = _
      rw [hp]; simp [lp,szEq]
    change ((B.gates ++ [_]).foldl step (List.ofFn y)).getD (b+B.size) false = _
    rw [List.foldl_append]
    change (w ++ [w.getD i false || (w.getD j false || false)]).getD (b+B.size) false = _
    rw [List.getD_append_right _ _ _ _ (by omega),len,Nat.sub_self]
    simp [w]

  have stack : ∀ (a b k : ℕ) (C : Circuit) (f : Fin k → Fin a → Fin b), 0 < k → IsAO2 a C →
        ∃ D : Circuit, IsAO2 b D ∧ D.size + 1 ≤ k * (C.size + 1) ∧
          ∀ y : Fin b → Bool, circuitFun b D y = decide (∃ j : Fin k, circuitFun a C (fun u => y (f j u)) = true) := by
    intro a b k C f hk hC
    let empty : Circuit := ⟨[],b⟩
    have emp : IsAO2 b empty := by apply (legal_iff _ _).mp; intro i h; simp [empty] at h
    by_cases ho : C.output < a+C.size
    · have build (n : ℕ) (maps : Fin (n+1) → Fin a → Fin b) :
          ∃ D : Circuit, IsAO2 b D ∧ D.size+1 ≤ (n+1)*(C.size+1) ∧ D.output < b+D.size ∧
            ∀ y, circuitFun b D y = decide (∃ j, circuitFun a C (fun u => y (maps j u)) = true) := by
        induction n with
        | zero =>
          obtain ⟨D,hD,sz,valid,funD,_⟩ := copy a b C empty hC emp ho (maps 0)
          refine ⟨D,hD,by simpa [empty,szEq] using congrArg Nat.succ sz |>.le,valid,?_⟩
          intro y
          rw [funD]
          have e : (∃ j, circuitFun a C (fun u => y (maps j u)) = true) ↔ circuitFun a C (fun u => y (maps 0 u)) = true := by simp
          exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using e.symm)
        | succ n ih =>
          obtain ⟨A,hA,szA,oA,vA⟩ := ih (fun j => maps j.castSucc)
          obtain ⟨B,hB,szB,oB,vB,pre⟩ := copy a b C A hC hA ho (maps (Fin.last (n+1)))
          obtain ⟨D,hD,szD,oD,vD⟩ := join b B hB A.output B.output (by omega) oB
          refine ⟨D,hD,?_,oD,?_⟩
          · rw [Nat.succ_mul]; omega
          · intro y
            rw [vD,pre y _ oA]
            change (circuitFun b A y || circuitFun b B y) = _
            rw [vA,vB]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true,decide_eq_true_eq]
            constructor
            · rintro (⟨i,hi⟩|hi)
              · exact ⟨i.castSucc,hi⟩
              · exact ⟨Fin.last _,hi⟩
            · rintro ⟨i,hi⟩
              exact Fin.lastCases (motive := fun i => circuitFun a C (fun u => y (maps i u)) = true →
                _ ∨ circuitFun a C (fun u => y (maps (Fin.last _) u)) = true)
                Or.inr (fun j h => Or.inl ⟨j,h⟩) i hi
      cases k with
      | zero => omega
      | succ n =>
        obtain ⟨D,hD,sz,_,v⟩ := build n f
        exact ⟨D,hD,sz,v⟩
    · refine ⟨empty,emp,by change 1 ≤ k*(C.size+1); exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),?_⟩
      intro y
      have no (j : Fin k) : circuitFun a C (fun u => y (f j u)) = false := by
        obtain ⟨vs,hvs,lv⟩ := trace C.gates (List.ofFn (fun u => y (f j u)))
        change (C.gates.foldl step _).getD C.output false = _
        rw [hvs,List.getD_eq_default _ _ (by simp only [List.length_append,List.length_ofFn,lv]; change a+C.size ≤ C.output; omega)]
      have h : ¬∃j, circuitFun a C (fun u => y (f j u))=true := by rintro ⟨j,h⟩; simp [no] at h
      rw [decide_eq_false h]
      change (List.ofFn y).getD b false = _
      rw [List.getD_eq_default _ _ (by simp)]
  obtain ⟨K,hcoarse⟩ := coarse
  have charge (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit)
      (free : ∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E))
      (hc : IsAO2 (n+m) C)
      (he : ∀ z, circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true))
      (sub : M ⊆ E) (mr : ∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d)
      (mc : ∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) :
      E.card + M.card ≤ C.size + 1 := by
    by_contra! hbad
    let k := K*K*(n+m+1)+1
    have hk : 0 < k := Nat.zero_lt_succ _
    let row : Fin k × Fin n ≃ Fin (k*n) := finProdFinEquiv
    let col : Fin k × Fin m ≃ Fin (k*m) := finProdFinEquiv
    let enc (t : Fin k × (Fin n × Fin m)) := (row (t.1,t.2.1),col (t.1,t.2.2))
    have inj : Function.Injective enc := by
      rintro ⟨i,p,l⟩ ⟨j,q,s⟩ h
      have u : (i,p) = (j,q) := row.injective (congrArg Prod.fst h)
      have v : (i,l) = (j,s) := col.injective (congrArg Prod.snd h)
      cases u; cases v; rfl
    let copies (X : Finset (Fin n × Fin m)) := ((Finset.univ : Finset (Fin k)) ×ˢ X).image enc
    have count (X : Finset (Fin n × Fin m)) : (copies X).card = k * X.card := by
      simp [copies,Finset.card_image_of_injective _ inj]
    have mem (X : Finset (Fin n × Fin m)) (i j : Fin k) (p : Fin n) (l : Fin m) :
        (row (i,p),col (j,l)) ∈ copies X ↔ i=j ∧ (p,l) ∈ X := by
      constructor
      · intro h
        obtain ⟨⟨v,a,b⟩,ht,eq⟩ := Finset.mem_image.mp h
        have u : (v,a) = (i,p) := row.injective (congrArg Prod.fst eq)
        have w : (v,b) = (j,l) := col.injective (congrArg Prod.snd eq)
        cases u; cases w
        exact ⟨rfl,(Finset.mem_product.mp ht).2⟩
      · rintro ⟨rfl,h⟩
        exact Finset.mem_image.mpr ⟨(i,p,l),Finset.mem_product.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
    have sq (p q : Fin (k*n)) (l s : Fin (k*m)) (hp : p ≠ q) (hl : l ≠ s) :
        ¬ ((p,l) ∈ copies E ∧ (p,s) ∈ copies E ∧ (q,l) ∈ copies E ∧ (q,s) ∈ copies E) := by
      obtain ⟨⟨i,a⟩,rfl⟩ := row.surjective p
      obtain ⟨⟨j,b⟩,rfl⟩ := row.surjective q
      obtain ⟨⟨t,c⟩,rfl⟩ := col.surjective l
      obtain ⟨⟨u,d⟩,rfl⟩ := col.surjective s
      simp only [mem]
      rintro ⟨⟨rfl,h1⟩,⟨rfl,h2⟩,⟨rfl,h3⟩,_,h4⟩
      exact free a b c d (fun h => hp (h ▸ rfl)) (fun h => hl (h ▸ rfl)) ⟨h1,h2,h3,h4⟩
    have sub' : copies M ⊆ copies E := Finset.image_mono enc (Finset.product_subset_product_right sub)
    have matching (left : Bool) (e d : Fin (k*n) × Fin (k*m))
        (he' : e ∈ copies M) (hd : d ∈ copies M)
        (eq : if left then e.1=d.1 else e.2=d.2) : e=d := by
      obtain ⟨⟨i,a⟩,hi,rfl⟩ := Finset.mem_image.mp he'
      obtain ⟨⟨j,b⟩,hj,rfl⟩ := Finset.mem_image.mp hd
      have ha := (Finset.mem_product.mp hi).2
      have hb := (Finset.mem_product.mp hj).2
      cases left
      · have eq' : (i,a.2) = (j,b.2) := col.injective eq
        have h := mc a ha b hb (congrArg (fun z : Fin k × Fin m => z.2) eq')
        have h' := congrArg Prod.fst eq'
        cases h; cases h'; rfl
      · have eq' : (i,a.1) = (j,b.1) := row.injective eq
        have h := mr a ha b hb (congrArg (fun z : Fin k × Fin n => z.2) eq')
        have h' := congrArg Prod.fst eq'
        cases h; cases h'; rfl
    let place (j : Fin k) : Fin (n+m) → Fin (k*n+k*m) := Fin.addCases
      (fun p => Fin.castAdd (k*m) (row (j,p))) (fun l => Fin.natAdd (k*n) (col (j,l)))
    obtain ⟨D,hdAO,hdSize,hdFun⟩ := stack (n+m) (k*n+k*m) k C place hk hc
    have exactD (y : Fin (k*n+k*m) → Bool) :
        circuitFun (k*n+k*m) D y = decide (∃ p l, (p,l) ∈ copies E ∧
          y (Fin.castAdd (k*m) p) = true ∧ y (Fin.natAdd (k*n) l) = true) := by
      rw [hdFun]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨j,h⟩
        rw [he,decide_eq_true_eq] at h
        obtain ⟨p,l,edge,hp,hl⟩ := h
        exact ⟨row (j,p),col (j,l),(mem E ..).mpr ⟨rfl,edge⟩,
          by simpa [place] using hp,by simpa [place] using hl⟩
      · rintro ⟨p,l,ed,hp,hl⟩
        obtain ⟨⟨i,a⟩,rfl⟩ := row.surjective p
        obtain ⟨⟨j,b⟩,rfl⟩ := col.surjective l
        obtain ⟨rfl,edge⟩ := (mem E ..).mp ed
        refine ⟨i,?_⟩
        rw [he,decide_eq_true_eq]
        exact ⟨a,b,edge,by simpa [place] using hp,by simpa [place] using hl⟩
    have h := hcoarse (k*n) (k*m) (copies E) (copies M) D sq hdAO exactD sub'
      (fun e he' d hd h => matching true e d he' hd h)
      (fun e he' d hd h => matching false e d he' hd h)
    rw [count,count,← Nat.mul_add] at h
    have lower : k*(C.size+1)+k ≤ k*(E.card+M.card) := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hbad
    let s := Nat.sqrt (k*n+k*m+1)
    have up : k ≤ K*s := by dsimp only [s]; omega
    have sqk := Nat.mul_le_mul up up
    have sqs : s*s ≤ k*n+k*m+1 := Nat.sqrt_le _
    have hklen : k*n+k*m+1 ≤ k*(n+m+1) := by
      simp only [Nat.mul_add, Nat.mul_one]; omega
    have contradiction : k*k ≤ k*(K*K*(n+m+1)) := calc
      k*k ≤ (K*s)*(K*s) := sqk
      _ = (K*K)*(s*s) := by ring
      _ ≤ (K*K)*(k*(n+m+1)) := Nat.mul_le_mul_left _ (sqs.trans hklen)
      _ = k*(K*K*(n+m+1)) := by ring
    have le := Nat.le_of_mul_le_mul_left contradiction hk
    dsimp only [k] at le
    omega

  intro n m I _ C square ao correct
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  obtain ⟨M,A,B,sub,points,lines,cover,dual⟩ := matchingCover n m E
  have budget := charge n m E M C (by simpa only [mem] using square) ao
    (by simpa only [mem] using correct) sub
    (fun _ he _ hf h => points he hf h) (fun _ he _ hf h => lines he hf h)
  obtain ⟨D,S,strict,size,eval,closed,ands⟩ := stars n m E A B cover
  refine ⟨D,S false,S true,strict,by simpa only [mem] using eval,by omega,?_,?_,?_⟩
  · intro w hw
    rcases closed false w hw with ⟨_,side⟩ | gate
    · exact Or.inl (by simpa using side)
    · exact Or.inr gate
  · intro w hw
    rcases closed true w hw with ⟨bound,side⟩ | gate
    · exact Or.inl ⟨by simpa using side,bound⟩
    · exact Or.inr gate
  · intro i hi hand
    obtain ⟨a,b,t,inputs,ha,hb⟩ := ands i hi hand
    refine ⟨a,b,inputs,?_⟩
    cases t with
    | false => exact Or.inl ⟨ha,hb⟩
    | true => exact Or.inr ⟨ha,hb⟩
