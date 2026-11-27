import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Positive leaves are evaluated as their input, independently of the unused literal sign.
-- A cover fitting the budget gives a direct rectangle construction.
-- The sparse negative inputs are the open neighborhoods of the singleton or edge columns
-- with the column endpoints removed. They are independent by the two short-cycle exclusions.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_4123_718
    (protocol : ∀ (n : ℕ) (p : DMFormula n),
      let val (x : Fin n → Bool) := p.rec (fun v _ => x v)
        (fun _ _ a b => a && b) (fun _ _ a b => a || b)
      ∃ (X Y : Fin p.leaves → (Fin n → Bool) → Prop) (label : Fin p.leaves → Fin n),
      ∀ x y, val x = true → val y = false →
        (∃! i, X i x ∧ Y i y) ∧ ∀ i, X i x → Y i y → x (label i) = true ∧ y (label i) = false)
    (compress : ∀ (n s : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (z : Fin n),
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ v (q : G.Walk v v), q.IsCycle → 7 ≤ q.length) →
      H = G.deleteEdges (G.incidenceSet z) →
      let f := graphFun H ∅
      let neg (v w i : Fin n) := decide ((H.Adj v i ∨ H.Adj w i) ∧ i ≠ v ∧ i ≠ w)
      HasCircuitSize n f s → (∀ t, HasCircuitSize n f t → s ≤ t) →
      (∀ T : Finset (Fin n), (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) → s + 1 < H.edgeSet.ncard + T.card) →
      (∀ v w, v = w ∨ H.Adj v w → f (neg v w) = false) →
      ∃ p : DMFormula n, p.leaves ≤ s + 1 ∧
        ∀ x : Fin n → Bool,
        ((∃ a b, H.Adj a b ∧ x = pairInput a b) ∨ (∃ v w, (v = w ∨ H.Adj v w) ∧ x = neg v w)) →
        p.rec (fun i _ => x i) (fun _ _ a b => a && b) (fun _ _ a b => a || b) = f x) :
∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool), (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) → (x3.neighborSet x5).ncard = (3 : ℕ) → (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → x4 = x3.deleteEdges (x3.incidenceSet x5) → (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 → ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x15 : Fin (x2 + (1 : ℕ)) → Fin x1), ∀ (x16 x17 x18 x19 : Fin x1), x4.Adj x16 x17 → x18 = x19 ∨ x4.Adj x18 x19 → (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧ ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 → (x15 x22 = x16 ∨ x15 x22 = x17) ∧ ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19) := by
  classical
  intro n budget G H z f deg hz girth heq spec size
  let hit := graphFun H ∅
  let neg (v w i : Fin n) := decide ((H.Adj v i ∨ H.Adj w i) ∧ i ≠ v ∧ i ≠ w)
  have edge (x : Fin n → Bool) : hit x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ a b, H.Adj a b ∧ x a = true ∧ x b = true)) = true ↔ _
    simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  have original : f = hit := funext fun x => Bool.eq_iff_iff.mpr ((spec x).trans (edge x).symm)
  rw [original] at size
  let possible := fun t => HasCircuitSize n hit t
  have any : ∃ t, possible t := ⟨budget,size⟩
  let s := Nat.find any
  have small : possible s := Nat.find_spec any
  have le : s ≤ budget := Nat.find_min' any size
  have low (t : ℕ) (ht : possible t) : s ≤ t := Nat.find_min' any ht
  have sub : H ≤ G := by rw [heq]; exact G.deleteEdges_le _
  have legal {a b v w : Fin n} (ab : H.Adj a b) (vw : v = w ∨ H.Adj v w) :
      ¬ ((H.Adj v a ∨ H.Adj w a) ∧ a ≠ v ∧ a ≠ w) ∨
      ¬ ((H.Adj v b ∨ H.Adj w b) ∧ b ≠ v ∧ b ≠ w) := by
    have triangle {p z u : Fin n} (pz : G.Adj p z) (pu : G.Adj p u) (zu : G.Adj z u) : False := by
      let t : G.Walk p p := .cons pz (.cons zu (.cons pu.symm .nil))
      have cycle : t.IsCycle := by
        rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
        constructor
        · rw [SimpleGraph.Walk.isPath_def]
          simp [t, zu.ne, pz.ne.symm, pu.ne.symm]
        · simp [t]
      have h := girth p t cycle
      simp [t] at h
    have square {p z i j : Fin n} (pz : p ≠ z) (ij : i ≠ j)
        (pi : G.Adj p i) (zi : G.Adj z i) (pj : G.Adj p j) (zj : G.Adj z j) : False := by
      let t : G.Walk p p := .cons pi (.cons zi.symm (.cons zj (.cons pj.symm .nil)))
      have cycle : t.IsCycle := by
        rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
        constructor
        · rw [SimpleGraph.Walk.isPath_def]
          simp [t, pz.symm, ij, zi.ne.symm, pi.ne.symm, zj.ne, pj.ne.symm]
        · simp [t]
      have h := girth p t cycle
      simp [t] at h
    by_cases badA : (H.Adj v a ∨ H.Adj w a) ∧ a ≠ v ∧ a ≠ w
    · right
      obtain ⟨ha,av,aw⟩ := badA
      rintro ⟨hb,bv,bw⟩
      rcases vw with rfl | vw
      · exact triangle (sub (ha.elim id id)) (sub (hb.elim id id)) (sub ab)
      · rcases ha with va | wa <;> rcases hb with vb | wb
        · exact triangle (sub va) (sub vb) (sub ab)
        · exact square bv.symm aw (sub va) (sub ab.symm) (sub vw) (sub wb.symm)
        · exact square bw.symm av (sub wa) (sub ab.symm) (sub vw.symm) (sub vb.symm)
        · exact triangle (sub wa) (sub wb) (sub ab)
    · exact Or.inl badA
  by_cases cheap : ∃ T : Finset (Fin n), (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧ H.edgeSet.ncard + T.card ≤ s+1
  · obtain ⟨T,cover,cost⟩ := cheap
    let m := budget+1
    have enough : H.edgeSet.ncard + T.card ≤ m := by dsimp [m]; omega
    let I := ↥T ⊕ ↥H.edgeSet
    have orient : ∀ e : H.edgeSet, ∃ (c : T) (d : Fin n), e.val = s(c.val,d) := by
      rintro ⟨e,he⟩
      induction e using Sym2.inductionOn with
      | _ a b =>
        have ab : H.Adj a b := he
        rcases cover a b ab with ha | hb
        · exact ⟨⟨a,ha⟩,b,rfl⟩
        · exact ⟨⟨b,hb⟩,a,Sym2.eq_swap⟩
    choose head tip orientEq using orient
    let safe (i v w : Fin n) := ¬ ((H.Adj v i ∨ H.Adj w i) ∧ i ≠ v ∧ i ≠ w)
    let X : I → Fin n → Fin n → Prop := Sum.elim
      (fun t a b => ∃ h : s(a,b) ∈ H.edgeSet, head ⟨s(a,b),h⟩ = t)
      (fun e a b => e.val = s(a,b))
    let Y : I → Fin n → Fin n → Prop := Sum.elim (fun t v w => safe t.val v w)
      (fun e v w => ¬safe (head e).val v w)
    let L : I → Fin n := Sum.elim Subtype.val tip
    have eq (a b v w : Fin n) (ab : H.Adj a b) (vw : v=w ∨ H.Adj v w) :
        (∃! i, X i a b ∧ Y i v w) ∧
        ∀ i, X i a b → Y i v w → (L i = a ∨ L i = b) ∧ safe (L i) v w := by
      let e : H.edgeSet := ⟨s(a,b),ab⟩
      have eh : (head e).val = a ∧ tip e = b ∨ (head e).val = b ∧ tip e = a :=
        Sym2.eq_iff.mp (orientEq e).symm
      have headEnds : (head e).val = a ∨ (head e).val = b := eh.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      have tailEnds : tip e = a ∨ tip e = b := eh.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
      have tailLegal (nh : ¬safe (head e).val v w) : safe (tip e) v w := by
        have ok := legal ab vw
        change safe a v w ∨ safe b v w at ok
        rcases eh with ⟨h,t⟩ | ⟨h,t⟩ <;> rw [h] at nh <;> rw [t] <;> tauto
      constructor
      · by_cases h : safe (head e).val v w
        · refine ⟨Sum.inl (head e),⟨⟨ab,rfl⟩,h⟩,?_⟩
          intro i hi
          cases i with
          | inl k => exact congrArg Sum.inl hi.1.choose_spec.symm
          | inr j =>
            have je : j = e := Subtype.ext hi.1
            subst j
            exact False.elim (hi.2 h)
        · refine ⟨Sum.inr e,⟨rfl,h⟩,?_⟩
          intro i hi
          cases i with
          | inl k =>
            have eqk : head e = k := hi.1.choose_spec
            exact False.elim (h (eqk.symm ▸ hi.2))
          | inr j => exact congrArg Sum.inr (Subtype.ext hi.1)
      · intro i hi hn
        cases i with
        | inl k =>
          have hk : head e = k := hi.choose_spec
          subst k
          exact ⟨headEnds,hn⟩
        | inr j =>
          have hj : j = e := Subtype.ext hi
          subst j
          exact ⟨tailEnds,tailLegal hn⟩
    let k := Fintype.card I
    let equiv : I ≃ Fin k := Fintype.equivFin I
    have limit : k ≤ m := by
      change Fintype.card (↥T ⊕ ↥H.edgeSet) ≤ m
      rw [Fintype.card_sum,Fintype.card_coe,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Nat.add_comm]
      exact enough
    let X' (i : Fin m) (a b : Fin n) := ∃ h : i.val < k, X (equiv.symm ⟨i.val,h⟩) a b
    let Y' (i : Fin m) (v w : Fin n) := ∃ h : i.val < k, Y (equiv.symm ⟨i.val,h⟩) v w
    let L' (i : Fin m) := if h : i.val < k then L (equiv.symm ⟨i.val,h⟩) else z
    refine ⟨X',Y',L',?_⟩
    intro a b v w ab vw
    obtain ⟨⟨i,⟨xx,yy⟩,uniq⟩,labs⟩ := eq a b v w ab vw
    have base : equiv.symm (equiv i) = i := equiv.symm_apply_apply _
    refine ⟨⟨⟨(equiv i).val,(equiv i).isLt.trans_le limit⟩,
      ⟨⟨(equiv i).isLt,by simpa only [base] using xx⟩,⟨(equiv i).isLt,by simpa only [base] using yy⟩⟩,?_⟩,?_⟩
    · rintro j ⟨⟨h,hx⟩,⟨_,hy⟩⟩
      have hi : (⟨j.val,h⟩ : Fin k) = equiv i := equiv.symm_apply_eq.mp (uniq _ ⟨hx,hy⟩)
      exact Fin.ext (congrArg (Fin.val (n:=k)) hi)
    · rintro j ⟨h,hx⟩ ⟨_,hy⟩
      have lab : L' j = L (equiv.symm ⟨j.val,h⟩) := dite_eq_left h
      rw [lab]
      exact labs _ hx hy
  have hard (T : Finset (Fin n)) (cover : ∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) : s+1 < H.edgeSet.ncard + T.card :=
    Nat.lt_of_not_ge (fun h => cheap ⟨T,cover,h⟩)
  have negative (v w : Fin n) (h : v = w ∨ H.Adj v w) : hit (neg v w) = false := by
    cases hf : hit (neg v w) with
    | false => rfl
    | true =>
      obtain ⟨a,b,ab,ha,hb⟩ := (edge _).mp hf
      rcases legal ab h with ea | eb
      · exact False.elim (ea (of_decide_eq_true ha))
      · exact False.elim (eb (of_decide_eq_true hb))
  have positive (a b : Fin n) (ab : H.Adj a b) : hit (pairInput a b) = true := by
    apply (edge _).mpr
    exact ⟨a,b,ab,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
  obtain ⟨p,count,fit⟩ := compress n s G H z deg hz girth heq small low hard negative
  obtain ⟨X,Y,label,valid⟩ := protocol n p
  let NX (i : Fin (budget+1)) (a b : Fin n) := ∃ h : i.val < p.leaves, X ⟨i.val,h⟩ (pairInput a b)
  let NY (i : Fin (budget+1)) (v w : Fin n) := ∃ h : i.val < p.leaves, Y ⟨i.val,h⟩ (neg v w)
  let lab (i : Fin (budget+1)) := if h : i.val < p.leaves then label ⟨i.val,h⟩ else z
  refine ⟨NX,NY,lab,?_⟩
  intro a b v w ab good
  obtain ⟨⟨k,⟨kx,ky⟩,only⟩,labels⟩ := valid (pairInput a b) (neg v w)
    ((fit _ (Or.inl ⟨a,b,ab,rfl⟩)).trans (positive a b ab))
    ((fit _ (Or.inr ⟨v,w,good,rfl⟩)).trans (negative v w good))
  refine ⟨⟨⟨k.val,by omega⟩,⟨⟨k.isLt,kx⟩,⟨k.isLt,ky⟩⟩,?_⟩,?_⟩
  · rintro i ⟨⟨h,hx⟩,⟨_,hy⟩⟩
    apply Fin.ext
    exact congrArg (Fin.val (n := p.leaves)) (only ⟨i.val,h⟩ ⟨hx,hy⟩)
  · rintro i ⟨h,hx⟩ ⟨_,hy⟩
    obtain ⟨yes,no⟩ := labels ⟨i.val,h⟩ hx hy
    have eq : lab i = label ⟨i.val,h⟩ := dite_eq_left h
    rw [eq]
    exact ⟨of_decide_eq_true yes,of_decide_eq_false no⟩
