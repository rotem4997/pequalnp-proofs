import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4227_37
    (saving : let I := fun (u v : Fin 42) => u.val < 21 ∧ 21 < v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      ∃ (S : Finset (Fin 42)) (D : Circuit), (∀ v ∈ S, 21 < v.val) ∧ S.card ≤ 10 ∧
        Monotone2 D ∧ ReadsBack 42 D ∧ D.output < 42+D.size ∧ D.size+2 ≤ 6*S.card ∧
        ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v, I u v ∧ v ∈ S ∧ x u = true ∧ x v = true)
    (extend : ∀ (n : ℕ) (D : Circuit) (v : Fin n) (A : Finset (Fin n)),
      A.card = 5 → Monotone2 D → ReadsBack n D → D.output < n+D.size →
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.output < n+C.size ∧
        C.size ≤ D.size+6 ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          (D.eval (List.ofFn x) || (x v && decide (∃ u ∈ A, x u = true)))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (42 : ℕ) x1 ∧ x1.output < (42 : ℕ) + x1.size ∧ x1.size ≤ (118 : ℕ) ∧ (∀ (x2 : Fin (42 : ℕ)), ↑x2 ∈ [(0 : ℕ), (1 : ℕ), (4 : ℕ), (14 : ℕ)] → ∃ x4 ∈ x1.gates, ↑x2 ∈ x4.inputs) ∧ ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) < ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true) := by
  let I := fun (u v : Fin 42) => u.val < 21 ∧ 21 < v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
  let U := Finset.univ.filter (fun v : Fin 42 => 21 < v.val)
  let pts := fun v : Fin 42 => Finset.univ.filter (fun u => I u v)
  have five : ∀ v ∈ U, (pts v).card = 5 := by decide +kernel
  have twenty : U.card = 20 := by decide +kernel
  obtain ⟨S,D,valid,_,mono,back,out,cheap,base⟩ := saving
  have sub : S ⊆ U := fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid v hv⟩
  have grow (T : Finset (Fin 42)) (ht : T ⊆ U) :
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack 42 C ∧ C.output < 42+C.size ∧
        C.size ≤ D.size+6*T.card ∧ ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u v, I u v ∧ (v ∈ S ∨ v ∈ T) ∧ x u = true ∧ x v = true := by
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨D,mono,back,out,by simp,?_⟩
      intro x
      simpa [I] using base x
    | @insert v T fresh ih =>
      have hv := ht (Finset.mem_insert_self v T)
      obtain ⟨B,bm,bb,bo,bs,bv⟩ := ih (fun z hz => ht (Finset.mem_insert_of_mem hz))
      obtain ⟨C,cm,cb,co,cs,cv⟩ := extend 42 B v (pts v) (five v hv) bm bb bo
      refine ⟨C,cm,cb,co,?_,?_⟩
      · rw [Finset.card_insert_of_notMem fresh]; omega
      · intro x
        rw [cv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bv]
        simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro (⟨a,b,e,old,ha,hb⟩ | ⟨hv',a,e,ha⟩)
          · exact ⟨a,b,e,old.imp_right Or.inr,ha,hb⟩
          · exact ⟨a,v,e,Or.inr (Or.inl rfl),ha,hv'⟩
        · rintro ⟨a,b,e,(old | rfl | inside),ha,hb⟩
          · exact Or.inl ⟨a,b,e,Or.inl old,ha,hb⟩
          · exact Or.inr ⟨hb,a,e,ha⟩
          · exact Or.inl ⟨a,b,e,Or.inr inside,ha,hb⟩
  obtain ⟨C4,m4,k4,o4,bound,h4⟩ := grow (U \ S) Finset.sdiff_subset
  have count : (U \ S).card = U.card-S.card := Finset.card_sdiff_of_subset sub
  have small : C4.size ≤ 118 := by have sc := Finset.card_le_card sub; omega
  have correct (x : Fin 42 → Bool) : C4.eval (List.ofFn x) = true ↔
      ∃ p q, I p q ∧ x p = true ∧ x q = true := by
    rw [h4]
    constructor
    · rintro ⟨p,q,h,_,hp,hq⟩; exact ⟨p,q,h,hp,hq⟩
    · rintro ⟨p,q,h,hp,hq⟩
      refine ⟨p,q,h,?_,hp,hq⟩
      by_cases mem : q ∈ S
      · exact Or.inl mem
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.1⟩,mem⟩)
  refine ⟨C4,m4,k4,o4,small,?_,correct⟩
  intro i watched
  have neighbor : ∃ l : Fin 42, I i l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at watched
    rcases watched with h | h | h | h
    · have h0 : i = 0 := Fin.ext h
      subst i
      exact ⟨26, by decide +kernel⟩
    · have h1 : i = 1 := Fin.ext h
      subst i
      exact ⟨22, by decide +kernel⟩
    · have h4 : i = 4 := Fin.ext h
      subst i
      exact ⟨25, by decide +kernel⟩
    · have h14 : i = 14 := Fin.ext h
      subst i
      exact ⟨35, by decide +kernel⟩
  obtain ⟨l, incident⟩ := neighbor
  let single (v : Fin 42) : Fin 42 → Bool := fun t => decide (t = v)
  have singleFalse (v : Fin 42) : C4.eval (List.ofFn (single v)) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨p, q, h, hp, hq⟩ := (correct _).mp he
    simp only [single, decide_eq_true_eq] at hp hq
    subst p
    subst q
    have lo : v.val < 21 := h.1
    have hi : 21 < v.val := h.2.1
    omega
  let pair : Fin 42 → Bool := fun t => decide (t = i ∨ t = l)
  have pairTrue : C4.eval (List.ofFn pair) = true :=
    (correct _).mpr ⟨i, l, incident, by simp [pair], by simp [pair]⟩
  have inValue (x : Fin 42 → Bool) (j : Fin 42) :
      (List.ofFn x).getD j.val false = x j := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have keepRaw (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  have notOutput : C4.output ≠ i.val := by
    intro index
    have yes : C4.eval (List.ofFn (single i)) = true := by
      change (C4.gates.foldl step (List.ofFn (single i))).getD C4.output false = true
      rw [index, keepRaw _ _ _ (by simp)]
      rw [inValue]
      simp [single]
    exact Bool.noConfusion (yes.symm.trans (singleFalse i))
  by_contra omitted
  have unobserved (g : Gate) (hg : g ∈ C4.gates) : i.val ∉ g.inputs :=
    fun hi => omitted ⟨g, hg, hi⟩
  have agree (j : ℕ) (ne : j ≠ i.val) :
      (List.ofFn pair).getD j false = (List.ofFn (single l)).getD j false := by
    by_cases hj : j < 42
    · let k : Fin 42 := ⟨j, hj⟩
      have nk : k ≠ i := fun eq => ne (congrArg Fin.val eq)
      change (List.ofFn pair).getD k.val false = (List.ofFn (single l)).getD k.val false
      rw [inValue pair k, inValue (single l) k]
      simp only [pair, single, nk, false_or]
    · rw [List.getD_eq_default (List.ofFn pair) _ (by simp; omega),
        List.getD_eq_default (List.ofFn (single l)) _ (by simp; omega)]
  have replay (gs : List Gate) (notRead : ∀ g ∈ gs, i.val ∉ g.inputs)
      (u v : List Bool) (len : u.length = v.length)
      (rows : ∀ j, j ≠ i.val → u.getD j false = v.getD j false) :
      ∀ j, j ≠ i.val → (gs.foldl step u).getD j false = (gs.foldl step v).getD j false := by
    induction gs generalizing u v with
    | nil => exact rows
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun a ha => notRead a (List.mem_cons_of_mem _ ha))
        (step u g) (step v g) (by simp [step, len])
      intro j hj
      have equalGate : g.op.eval (g.inputs.map fun k => u.getD k false) =
          g.op.eval (g.inputs.map fun k => v.getD k false) := by
        congr 1
        exact List.map_congr_left (fun k hk => rows k (fun eq => notRead g List.mem_cons_self (eq ▸ hk)))
      dsimp only [step]
      rw [equalGate]
      by_cases hk : j < u.length
      · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (len ▸ hk)]
        exact rows j hj
      · have outside : u.length ≤ j := Nat.le_of_not_gt hk
        rw [List.getD_append_right _ _ _ _ outside, List.getD_append_right _ _ _ _ (len ▸ outside), len]
  have eq : C4.eval (List.ofFn pair) = C4.eval (List.ofFn (single l)) :=
    replay C4.gates unobserved _ _ (by simp) agree C4.output notOutput
  exact Bool.noConfusion (pairTrue.symm.trans (eq.trans (singleFalse l)))
