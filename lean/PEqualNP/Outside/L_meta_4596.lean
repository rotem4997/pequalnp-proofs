import PEqualNP.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace PEqualNP.Outside.L_meta_4596_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def runGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma readOld (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hi : i < w.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by omega)]

lemma readNew (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma cone (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length = 2) (n : ℕ) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.length ∧
      ∀ w v : List Bool, w.length = n → v.length = n →
        (∀ i ∈ T, w.getD i false = v.getD i false) →
        ∀ i ∈ S, (gs.foldl runGate w).getD i false = (gs.foldl runGate v).getD i false := by
  induction gs generalizing n S with
  | nil => exact ⟨S, by simp, fun w v _ _ h => h⟩
  | cons g gs ih =>
    obtain ⟨U, hU, agree⟩ := ih (fun a ha => arity a (List.mem_cons_of_mem g ha)) (n+1) S
    have finish (T : Finset ℕ)
        (keep : ∀ i ∈ U, i ≠ n → i ∈ T)
        (reads : n ∈ U → ∀ i ∈ g.inputs, i ∈ T) :
        ∀ w v : List Bool, w.length = n → v.length = n →
          (∀ i ∈ T, w.getD i false = v.getD i false) →
          ∀ i ∈ S, ((g::gs).foldl runGate w).getD i false = ((g::gs).foldl runGate v).getD i false := by
      intro w v hw hv same
      apply agree (runGate w g) (runGate v g) (by simp [runGate, hw]) (by simp [runGate, hv])
      intro i hi
      by_cases h : i = n
      · subst i
        have eq : g.inputs.map (fun j => w.getD j false) = g.inputs.map (fun j => v.getD j false) :=
          List.map_congr_left (fun j hj => same j (reads hi j hj))
        unfold runGate
        conv_lhs => pattern n; rw [← hw]
        conv_rhs => pattern n; rw [← hv]
        simp only [readNew,eq]
      · unfold runGate
        rw [readOld w _ _ (by simpa [hw] using h), readOld v _ _ (by simpa [hv] using h)]
        exact same i (keep i hi h)
    by_cases hn : n ∈ U
    · let T := U.erase n ∪ g.inputs.toFinset
      refine ⟨T, ?_, finish T (fun i hi h => Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h,hi⟩)) (fun _ i hi => Finset.mem_union_right _ (List.mem_toFinset.mpr hi))⟩
      have u := Finset.card_union_le (U.erase n) g.inputs.toFinset
      have a := List.toFinset_card_le g.inputs
      have ne : 0 < U.card := Finset.card_pos.mpr ⟨n,hn⟩
      rw [Finset.card_erase_of_mem hn] at u
      have hg := arity g List.mem_cons_self
      change (U.erase n ∪ g.inputs.toFinset).card ≤ S.card + (g::gs).length
      simp only [List.length_cons]
      omega
    · refine ⟨U, by simp only [List.length_cons]; omega, finish U (fun _ h _ => h) (fun h => (hn h).elim)⟩

lemma support (C : Circuit) (n : ℕ) (h : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∃ T : Finset ℕ, T.card ≤ C.size+1 ∧
      ∀ x y : Fin n → Bool, (∀ i, i.val ∈ T → x i = y i) → circuitFun n C x = circuitFun n C y := by
  obtain ⟨T,hT,H⟩ := cone C.gates h n {C.output}
  refine ⟨T, by simpa [Circuit.size,Nat.add_comm] using hT, ?_⟩
  intro x y A
  apply H (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hh : j < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn,hh] using A ⟨j,hh⟩ hj
  · simp [List.getD_eq_getElem?_getD, hh]

end PEqualNP.Outside.L_meta_4596_aux

namespace PEqualNP.Outside.L_meta_4596_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma countEndpoints {q n : ℕ} (R : Fin n → Fin n → Prop) (C : Circuit)
    (E : Finset (Fin n × Fin n)) (hq : 1 ≤ q) (hC : PEqualNP.TopForm.IsAO2 (n+n) C)
    (sound : ∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
      (¬ ∃ p l, R p l ∧ x (p.castAdd n) = true ∧ x (Fin.natAdd n l) = true) →
      circuitFun (n+n) C x = false)
    (flags : ∀ e ∈ E, R e.1 e.2 ∧ circuitFun (n+n) C
      (fun i => decide (i = e.1.castAdd n ∨ i = Fin.natAdd n e.2)) = true) :
    (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size+1 := by
  classical
  obtain ⟨T,nb,depends⟩ := support C (n+n) hC.2.2
  have apart (p l : Fin n) : p.castAdd n ≠ Fin.natAdd n l := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at this
    omega
  have both (e : Fin n × Fin n) (he : e ∈ E) : e.1.val ∈ T ∧ n+e.2.val ∈ T := by
    have pos := (flags e he).2
    constructor
    · by_contra absent
      let x : Fin (n+n) → Bool := fun i => decide (i = Fin.natAdd n e.2)
      have few : Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ 1 := by
        apply Fintype.card_le_one_iff_subsingleton.mpr
        constructor
        intro a b
        apply Subtype.ext
        have ha : a.val = e.2 := by simpa [x] using a.property
        have hb : b.val = e.2 := by simpa [x] using b.property
        exact ha.trans hb.symm
      have no := sound x (few.trans hq) (by
        rintro ⟨p,l,_,hp,_⟩
        exact apart p e.2 (of_decide_eq_true hp))
      have same := depends (fun i => decide (i = e.1.castAdd n ∨ i = Fin.natAdd n e.2)) x (by
        intro i hi
        have h : i ≠ e.1.castAdd n := fun h => absent (by simpa [h] using hi)
        simp only [h,false_or,x])
      rw [pos,no] at same
      contradiction
    · by_contra absent
      let x : Fin (n+n) → Bool := fun i => decide (i = e.1.castAdd n)
      have few : Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ 1 := by
        apply Fintype.card_le_one_iff_subsingleton.mpr
        constructor
        intro a _
        obtain ⟨l,hl⟩ := a
        exact ((apart e.1 l).symm (of_decide_eq_true hl)).elim
      have no := sound x (few.trans hq) (by
        rintro ⟨p,l,_,_,hl⟩
        exact (apart e.1 l).symm (of_decide_eq_true hl))
      have same := depends (fun i => decide (i = e.1.castAdd n ∨ i = Fin.natAdd n e.2)) x (by
        intro i hi
        have h : i ≠ Fin.natAdd n e.2 := fun h => absent (by simpa only [h,Fin.val_natAdd] using hi)
        simp only [h,or_false,x])
      rw [pos,no] at same
      contradiction
  let f : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let g : Fin n ↪ ℕ := ⟨fun l => n+l.val, fun _ _ h => Fin.ext (Nat.add_left_cancel h)⟩
  let P := (E.image Prod.fst).map f
  let L := (E.image Prod.snd).map g
  have disj : Disjoint P L := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨l,_,eq⟩ := Finset.mem_map.mp hj
    change n+l.val = p.val at eq
    omega
  have sub : P ∪ L ⊆ T := by
    intro i hi
    rcases Finset.mem_union.mp hi with hp|hl
    · obtain ⟨p,hp',rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp'
      exact (both e he).1
    · obtain ⟨l,hl',rfl⟩ := Finset.mem_map.mp hl
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl'
      exact (both e he).2
  have H := (Finset.card_le_card sub).trans nb
  simpa [Finset.card_union_of_disjoint disj,P,L] using H
end PEqualNP.Outside.L_meta_4596_aux

namespace PEqualNP.Outside.L_meta_4596_aux

private lemma numericInt (a b e s : ℤ) (hs : s ≤ 4400) (hc : a+b ≤ s+1)
    (ha : 0 < a) (hb : 0 < b) (h1 : e^2 ≤ a*(b^2+e)) (h2 : e^2 ≤ b*(a^2+e)) : e ≤ 24*s := by
  by_contra! bad
  let t := a+b
  have tpos : 0 < t := by dsimp [t]; omega
  have tcap : t ≤ 4401 := by dsimp [t]; omega
  have square : 0 < t^2 := sq_pos_of_pos tpos
  have upper : 8*e^2 ≤ t^3+4*t*e := by
    dsimp [t]
    nlinarith only [h1,h2,mul_nonneg (le_of_lt tpos : 0 ≤ a+b) (sq_nonneg (a-b))]
  by_cases low : t ≤ 95
  · have h : 0 ≤ 4*e-48*t := by dsimp [t] at *; omega
    have k : 0 ≤ 4*e+46*t := by omega
    nlinarith only [upper,square,mul_nonneg h k,mul_nonneg (sub_nonneg.mpr low) (le_of_lt square)]
  · have h : 0 ≤ 4*e-95*t := by dsimp [t] at *; omega
    have k : 0 ≤ 4*e+93*t := by omega
    nlinarith only [upper,square,mul_nonneg h k,mul_nonneg (sub_nonneg.mpr tcap) (le_of_lt square)]

theorem numeric (a b e s : ℕ) (hs : s ≤ 4400) (hc : a+b ≤ s+1) (ha : 0 < a) (hb : 0 < b)
    (h1 : e^2 ≤ a*(b^2+e)) (h2 : e^2 ≤ b*(a^2+e)) : e ≤ 24*s := by
  exact_mod_cast numericInt (a : ℤ) b e s (by exact_mod_cast hs) (by exact_mod_cast hc)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast h1) (by exact_mod_cast h2)

end PEqualNP.Outside.L_meta_4596_aux

namespace PEqualNP.Outside.L_meta_4596_aux

private lemma countSide {α β : Type} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β))
    (rect : ∀ x z y w, y ≠ w → (x,y) ∈ E → (x,w) ∈ E →
        (z,y) ∈ E → (z,w) ∈ E → x = z) :
    E.card ^ 2 ≤ (E.image Prod.fst).card * ((E.image Prod.snd).card ^ 2 + E.card) := by
  classical
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let F (x : α) := B.filter (fun y => (x,y) ∈ E)
  have row (x : α) (y : β) : y ∈ F x ↔ y ∈ B ∧ (x,y) ∈ E := Finset.mem_filter
  have fiber (x : α) : (E.filter (fun p => p.1 = x)).card = (F x).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · rintro ⟨u,v⟩ h
      obtain ⟨he, rfl⟩ := Finset.mem_filter.mp h
      exact (row _ _).mpr ⟨Finset.mem_image_of_mem Prod.snd he, he⟩
    · rintro ⟨u,v⟩ h ⟨z,w⟩ k eq
      exact Prod.ext ((Finset.mem_filter.mp h).2.trans (Finset.mem_filter.mp k).2.symm) eq
    · intro y hy
      exact ⟨(x,y), Finset.mem_filter.mpr ⟨((row _ _).mp hy).2,rfl⟩,rfl⟩
  have total : E.card = ∑ x ∈ A, (F x).card := by
    rw [Finset.card_eq_sum_card_image Prod.fst E]
    exact Finset.sum_congr rfl (fun x _ => fiber x)
  have bound : (A.sigma (fun x => (F x).offDiag)).card ≤ B.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun z => z.2)
    · rintro ⟨x,y,w⟩ hz
      obtain ⟨hy,hw,hn⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hz).2
      exact Finset.mem_offDiag.mpr ⟨((row _ _).mp hy).1, ((row _ _).mp hw).1,hn⟩
    · rintro ⟨x,y,w⟩ hx ⟨z,u,v⟩ hz h
      change (y,w) = (u,v) at h
      cases h
      obtain ⟨hxy,hxw,hn⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hx).2
      obtain ⟨hzy,hzw,_⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hz).2
      obtain rfl := rect x z y w hn ((row _ _).mp hxy).2 ((row _ _).mp hxw).2
        ((row _ _).mp hzy).2 ((row _ _).mp hzw).2
      rfl
  have identity (x : α) : (F x).card ^ 2 = (F x).offDiag.card + (F x).card := by
    rw [Finset.offDiag_card, sq]
    have h := Nat.le_mul_self (F x).card
    omega
  have squares : (∑ x ∈ A, (F x).card ^ 2) ≤ B.card ^ 2 + E.card := by
    simp_rw [identity]
    rw [Finset.sum_add_distrib, ← total, ← Finset.card_sigma]
    apply Nat.add_le_add_right
    exact bound.trans (by rw [Finset.offDiag_card,sq]; omega)
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => 1 : α → ℕ) (fun x => (F x).card)
  simp [← total] at cauchy
  exact cauchy.trans (Nat.mul_le_mul_left A.card squares)

theorem sides {n : ℕ} (R : Fin n → Fin n → Prop) (E : Finset (Fin n × Fin n))
    (hi : ∀ e ∈ E, R e.1 e.2)
    (hu : ∀ p q, p ≠ q → ∃! l, R p l ∧ R q l) :
    E.card ^ 2 ≤ (E.image Prod.fst).card * ((E.image Prod.snd).card ^ 2 + E.card) ∧
    E.card ^ 2 ≤ (E.image Prod.snd).card * ((E.image Prod.fst).card ^ 2 + E.card) := by
  classical
  constructor
  · apply countSide
    intro x z y w hy hxy hxw hzy hzw
    by_contra h
    exact hy ((hu x z h).unique ⟨hi _ hxy, hi _ hzy⟩ ⟨hi _ hxw, hi _ hzw⟩)
  · let S := E.image Prod.swap
    have swapMem (x y : Fin n) (h : (x,y) ∈ S) : (y,x) ∈ E := by
      obtain ⟨⟨p,q⟩, hp, he⟩ := Finset.mem_image.mp h
      cases he
      exact hp
    have h := countSide S (by
      intro x z y w hy hxy hxw hzy hzw
      exact (hu y w hy).unique ⟨hi _ (swapMem _ _ hxy), hi _ (swapMem _ _ hxw)⟩
        ⟨hi _ (swapMem _ _ hzy), hi _ (swapMem _ _ hzw)⟩)
    have cs : S.card = E.card := Finset.card_image_of_injective _ Prod.swap_injective
    simpa only [cs, S, Finset.image_image, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using h

theorem count {n : ℕ} (R : Fin n → Fin n → Prop) (E : Finset (Fin n × Fin n)) (s : ℕ)
    (hs : s ≤ 4400) (hc : (E.image Prod.fst).card + (E.image Prod.snd).card ≤ s+1)
    (hi : ∀ e ∈ E, R e.1 e.2)
    (hu : ∀ p q, p ≠ q → ∃! l, R p l ∧ R q l) : E.card ≤ 24*s := by
  classical
  rcases E.eq_empty_or_nonempty with he | he
  · simp [he]
  obtain ⟨h1,h2⟩ := sides R E hi hu
  exact numeric _ _ _ _ hs hc (Finset.card_pos.mpr (he.image _)) (Finset.card_pos.mpr (he.image _)) h1 h2

end PEqualNP.Outside.L_meta_4596_aux

theorem PEqualNP.Outside.L_meta_4596 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x2 × Fin x2)), (1 : ℕ) ≤ x1 → (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x9 = Bool.false) → (∀ x10 ∈ x5, x3 x10.1 x10.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 fun (x12 : Fin (x2 + x2)) => Decidable.decide (x12 = Fin.castAdd x2 x10.1 ∨ x12 = Fin.natAdd x2 x10.2)) = Bool.true) → x4.size ≤ (4400 : ℕ) → x5.card ≤ (24 : ℕ) * x4.size := by
  intro q n R C E hq unique ao sound flags small
  exact PEqualNP.Outside.L_meta_4596_aux.count R E C.size small
    (PEqualNP.Outside.L_meta_4596_aux.countEndpoints R C E hq ao sound flags)
    (fun e he => (flags e he).1) unique
