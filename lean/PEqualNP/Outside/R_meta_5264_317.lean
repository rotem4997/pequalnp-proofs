import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open scoped Sym2

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5264_317
    (counting : ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (i : Fin n) (p : G.Walk i i), p.IsCycle → 5≤p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      ∀ E ⊆ Ustar G C, (∀ e∈E, ∃ (u v : Fin n) (m : ℕ), e=s(u,v) ∧ m<C.size ∧
        (gateAt C m).op=.or ∧ (orIn n C (n+m)).Nonempty ∧ u∈wmax G C m ∧
        (∀ t∈orIn n C (n+m), t≠u ∧ t≠v) ∧ ∃ b : Fin 2, orIn n C (opnd C m b)=∅ ∧
        (C.wires (List.ofFn (pairInput u v))).getD (opnd C m b) false=true) →
      E.card ≤ K*(C.size+1))
    (rawPaths : ∀ (n : ℕ) (C : Circuit), (∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k) →
      ∀ w (i : Fin n), i∈orIn n C w ↔ Relation.ReflTransGen (fun u v => ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs) w i.val)
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ∃ x12 ∈ PEqualNP.TopForm.side x7 x11 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x11 (1 : Fin (2 : ℕ)), x12 ∈ x10}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  have wireLaw : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool),
      let V := fun i => (C.wires (List.ofFn x)).getD i false
      (∀ i : Fin n, V i=x i) ∧ ∀ k<C.size, ∀ l r, (gateAt C k).inputs=[l,r] → l<n+k → r<n+k →
        ((gateAt C k).op=.and → V (n+k)=(V l && V r)) ∧ ((gateAt C k).op=.or → V (n+k)=(V l || V r)) := by
    let stepWire (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wires_eq_foldl (C : Circuit) (x : List Bool) :
        C.wires x = C.gates.foldl stepWire x := rfl
    have foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl stepWire w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
        rw [ih (stepWire w g) hlt]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
        (gs.foldl stepWire w).getD (w.length + j) false =
          (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
            if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
      induction gs generalizing w j with
      | nil => simp at hj
      | cons g gs ih =>
        rw [List.foldl_cons]
        cases j with
        | zero =>
          have h1 : w.length < (stepWire w g).length := by simp [stepWire]
          rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
          simp only [List.getElem_cons_zero]
          have h2 : (stepWire w g).getD w.length false =
              g.op.eval (g.inputs.map fun i => w.getD i false) := by
            simp [stepWire, List.getD_eq_getElem?_getD]
          rw [h2]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < w.length
          · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
            simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [if_neg hi]; exact getD_ge w i (by omega)
        | succ j =>
          have hj' : j < gs.length := by simpa using hj
          have key := ih (stepWire w g) j hj'
          have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
          rw [hl] at key
          have e : w.length + (j + 1) = w.length + 1 + j := by omega
          simp only [List.getElem_cons_succ]
          rw [e]
          exact key
    let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
    have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
      change C.gates.getD j _ = C.gates[j]
      simp [List.getD_eq_getElem?_getD,hj]
    have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
        val C x u = x.getD u false := by
      unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)
    have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
        (hj : j < C.gates.length) :
        val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
          if i < n + j then val C x i else false) := by
      subst hx
      rw [gateAt_eq hj]
      exact foldl_getD_gate C.gates x j hj
    intro n C x
    constructor
    · intro i
      change val C (List.ofFn x) i=_
      rw [val_input (n:=n) (by simp) i.isLt]
      simp [List.getD_eq_getElem?_getD]
    · intro k hk l r ins hl hr
      have h := val_gate (C:=C) (x:=List.ofFn x) (n:=n) (by simp) hk
      rw [ins] at h
      simp only [List.map_cons,List.map_nil,if_pos hl,if_pos hr] at h
      constructor
      · intro op
        rw [op] at h
        change _ = ([val C (List.ofFn x) l,val C (List.ofFn x) r].all id) at h
        simpa [val] using h
      · intro op
        rw [op] at h
        change _ = ([val C (List.ofFn x) l,val C (List.ofFn x) r].any id) at h
        simpa [val] using h
  let W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD u false
  let AO (n : ℕ) (C : Circuit) : Prop :=
    ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k
  let OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
    ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs
  let OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)
  have W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
      W n C x u = x ⟨u, hu⟩ := by
    exact (wireLaw n C x).1 ⟨u,hu⟩
  have W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
      (ha : a < n + k) (hb : b < n + k) :
      W n C x (n + k) = (W n C x a && W n C x b) := by
    exact ((wireLaw n C x).2 k hk a b hin ha hb).1 hop
  have W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
      (ha : a < n + k) (hb : b < n + k) :
      W n C x (n + k) = (W n C x a || W n C x b) := by
    exact ((wireLaw n C x).2 k hk a b hin ha hb).2 hop
  have gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
    change C.gates.getD k _ = C.gates[k]
    simp [List.getD_eq_getElem?_getD,hk]
  have ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
    obtain ⟨h1, h2, h3⟩ := h
    intro k hk
    have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq C k hk]; exact List.getElem_mem hk
    refine ⟨h1 _ hmem, ?_⟩
    have hl := h3 _ hmem
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
    exact ⟨a, b, hab, h2 k hk a (by rw [hab]; simp), h2 k hk b (by rw [hab]; simp)⟩
  have orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
      (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
    obtain ⟨k, rfl, hk, hop, hin⟩ := h
    obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
    rw [W_or n C x k hk hop a b hab ha hb]
    rw [hab] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · simp [hv]
    · simp [hv]
  have orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
      (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih
  have mem_orIn (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (i : Fin n) :
      i ∈ PEqualNP.TopForm.orIn n C w ↔ OrR n C w i.val := by
    exact rawPaths n C hA w i
  have trace {n : ℕ} {C : Circuit} (ao : AO n C) (x : Fin n → Bool) :
      ∀ w, w < n+C.size → W n C x w=true →
      (orIn n C w).Nonempty → (∀ i ∈ orIn n C w, x i=false) →
      ∃ m<C.size, OrR n C w (n+m) ∧ (gateAt C m).op=.or ∧
        (orIn n C (n+m)).Nonempty ∧
        ∃ b : Fin 2, orIn n C (opnd C m b)=∅ ∧ W n C x (opnd C m b)=true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro bound on pos off
      by_cases raw : w<n
      · let i : Fin n := ⟨w,raw⟩
        have mem : i ∈ orIn n C w := (mem_orIn n C ao w i).mpr Relation.ReflTransGen.refl
        have eq := W_input n C x w raw
        exact (Bool.noConfusion (on.symm.trans (eq.trans (off i mem))))
      · obtain ⟨m,rfl⟩ : ∃ m,w=n+m := ⟨w-n,by omega⟩
        have hm : m<C.gates.length := by change n+m<n+C.gates.length at bound;omega
        obtain ⟨ops,l,r,inputs,hl,hr⟩ := ao m hm
        have hor : (gateAt C m).op=.or := by
          obtain ⟨i,hi⟩ := pos
          have path := (mem_orIn n C ao _ i).mp hi
          rcases Relation.ReflTransGen.cases_head path with eq | ⟨v,⟨k,eq,hk,op,_⟩,_⟩
          · have := i.isLt;omega
          · have : k=m := by omega
            simpa [this] using op
        rw [W_or n C x m hm hor l r inputs hl hr,Bool.or_eq_true] at on
        have go (v : ℕ) (b : Fin 2) (child : opnd C m b=v) (belongs : v∈(gateAt C m).inputs)
            (lt : v<n+m) (onV : W n C x v=true) :
            ∃ k<C.size, OrR n C (n+m) (n+k) ∧ (gateAt C k).op=.or ∧
            (orIn n C (n+k)).Nonempty ∧
            ∃ d : Fin 2, orIn n C (opnd C k d)=∅ ∧ W n C x (opnd C k d)=true := by
          have step : OrStep n C (n+m) v := ⟨m,rfl,hm,hor,belongs⟩
          by_cases hv : (orIn n C v).Nonempty
          · have offV (i : Fin n) (hi : i∈orIn n C v) := off i ((mem_orIn n C ao _ i).mpr
                (Relation.ReflTransGen.head step ((mem_orIn n C ao v i).mp hi)))
            obtain ⟨k,hk,path,h⟩ := ih v lt (lt.trans bound) onV hv offV
            exact ⟨k,hk,.head step path,h⟩
          · exact ⟨m,hm,.refl,hor,pos,b,by simpa [child] using Finset.not_nonempty_iff_eq_empty.mp hv,
              by simpa [child] using onV⟩
        rcases on with on|on
        · exact go l 0 (by change (gateAt C m).inputs.getD _ _ = _; rw [inputs] <;> rfl) (by simp [inputs]) hl on
        · exact go r 1 (by change (gateAt C m).inputs.getD _ _ = _; rw [inputs] <;> rfl) (by simp [inputs]) hr on
  have graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
      graphFun G ∅ (pairInput u v)=true ↔ G.Adj u v := by
    change (_ || decide (∃ s t,G.Adj s t ∧ decide (s=u ∨ s=v)=true ∧ decide (t=u ∨ t=v)=true))=true ↔ _
    simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
    constructor
    · rintro ⟨s,t,adj,rfl|rfl,rfl|rfl⟩ <;> first | exact adj | exact adj.symm | exact (adj.ne rfl).elim
    · intro adj
      exact ⟨u,v,adj,Or.inl rfl,Or.inr rfl⟩
  have raw_on {n : ℕ} {C : Circuit} (ao : AO n C) {w : ℕ}
      {i : Fin n} (mem : i ∈ orIn n C w) {x : Fin n → Bool} (on : x i=true) :
      W n C x w=true := by
    exact orR_mono n C ao x _ _ ((mem_orIn n C ao _ i).mp mem)
      ((W_input n C x _ i.isLt).trans on)
  have routing (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (least : IsLeastAO G C) (a : ℕ) (top : a∈tops G C)
      (p q : ℕ) (order : (gateAt C a).inputs=[p,q] ∨ (gateAt C a).inputs=[q,p])
      (u v : Fin n) (leaf : u∈orIn n C p) (nonempty : (orIn n C q).Nonempty)
      (outside : s(u,v)∈Ustar G C) (on : gateVal n C a (pairInput u v)=true) :
      ∃ m<C.size, (gateAt C m).op=.or ∧ (orIn n C (n+m)).Nonempty ∧
        u∈wmax G C m ∧ (∀ t∈orIn n C (n+m), t≠u ∧ t≠v) ∧
        ∃ b : Fin 2, orIn n C (opnd C m b)=∅ ∧ W n C (pairInput u v) (opnd C m b)=true := by
    have ao := ao_of n C least.1
    have ha := top
    change a ∈ (Finset.range C.gates.length).filter (fun j => (gateAt C j).op=.and ∧ BelowF G C j) at ha; rw [Finset.mem_filter,Finset.mem_range] at ha
    obtain ⟨len,andGate,below⟩ := ha
    obtain ⟨_,l,r,ins,hl,hr⟩ := ao a len
    have pairOrder : (l=p ∧ r=q) ∨ (l=q ∧ r=p) := by
      simpa [ins] using order
    have inputs (x) : gateVal n C a x=(W n C x p && W n C x q) := by
      change W n C x (n+a)=_
      rw [W_and n C x a len andGate l r ins hl hr]
      rcases pairOrder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [Bool.and_comm]
    have qlt : q<n+C.size := by
      change q<n+C.gates.length
      rcases pairOrder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
    have child0 (i : ℕ) (l r : ℕ) (ins : (gateAt C i).inputs=[l,r]) : opnd C i 0=l ∧ opnd C i 1=r := by
      change (gateAt C i).inputs.getD 0 0=l ∧ (gateAt C i).inputs.getD 1 0=r
      rw [ins];exact ⟨rfl,rfl⟩
    have otherOff (t : Fin n) (mem : t ∈ orIn n C q) : pairInput u v t=false := by
      change decide (t=u ∨ t=v)=false
      apply decide_eq_false_iff_not.mpr
      rintro (hu|hv)
      · subst u
        have fl : pairInput t t t=true := by change decide (t=t ∨ t=t)=true; simp
        have topOn : gateVal n C a (pairInput t t)=true := by
          rw [inputs,raw_on ao leaf fl,raw_on ao mem fl];rfl
        exact G.irrefl ((graph_pair G t t).mp (below _ topOn))
      · subst v
        apply (Finset.mem_sdiff.mp outside).2
        change _∈ (tops G C).biUnion _
        apply Finset.mem_biUnion.mpr
        refine ⟨a,top,Finset.mem_image.mpr ?_⟩
        rcases order with h|h
        · exact ⟨(u,t), Finset.mem_product.mpr ⟨by change u∈orIn n C (opnd C a 0);rw [(child0 _ _ _ h).1];exact leaf,
            by change t∈orIn n C (opnd C a 1);rw [(child0 _ _ _ h).2];exact mem⟩, rfl⟩
        · exact ⟨(t,u), Finset.mem_product.mpr ⟨by change t∈orIn n C (opnd C a 0);rw [(child0 _ _ _ h).1];exact mem,
            by change u∈orIn n C (opnd C a 1);rw [(child0 _ _ _ h).2];exact leaf⟩, Sym2.eq_swap⟩
    rw [inputs,Bool.and_eq_true] at on
    obtain ⟨m,hm,path,op,pos,b,empty,fire⟩ := trace ao (pairInput u v) q qlt on.2 nonempty otherOff
    refine ⟨m,hm,op,pos,?_,?_,b,empty,fire⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro x active xu
      apply below
      rw [inputs,Bool.and_eq_true]
      exact ⟨raw_on ao leaf xu,orR_mono n C ao x _ _ path active⟩
    · intro t ht
      have h := otherOff t ((mem_orIn n C ao _ t).mpr (path.trans ((mem_orIn n C ao _ t).mp ht)))
      change decide (t=u ∨ t=v)=false at h
      simpa using h
  obtain ⟨K,budget⟩ := counting
  refine ⟨K,?_⟩
  intro n G _ girth ne C least form
  apply budget n G girth ne C least form
  · exact Finset.filter_subset _ _
  · intro e he
    obtain ⟨uncovered,_,a,ha,edge,t,ht,hte⟩ := Finset.mem_filter.mp he
    obtain ⟨top,notEmpty⟩ := Finset.mem_sdiff.mp ha
    have ht0 : a<C.gates.length := by
      have ht := top
      change a ∈ (Finset.range C.gates.length).filter (fun j => (gateAt C j).op=.and ∧ BelowF G C j) at ht; rw [Finset.mem_filter,Finset.mem_range] at ht
      exact ht.1
    have gateMem : gateAt C a ∈ C.gates := by
      change C.gates.getD a _ ∈ C.gates
      simp [List.getD_eq_getElem?_getD,ht0]
    obtain ⟨l,r,ins⟩ := List.length_eq_two.mp (least.1.2.2 _ gateMem)
    have both : (side (n:=n) C a 0).Nonempty ∧ (side (n:=n) C a 1).Nonempty := by
      have no : ¬(side (n:=n) C a 0=∅ ∨ side (n:=n) C a 1=∅) := fun z => notEmpty (Finset.mem_filter.mpr ⟨top,z⟩)
      have non := not_or.mp no
      exact ⟨Finset.nonempty_iff_ne_empty.mpr non.1,Finset.nonempty_iff_ne_empty.mpr non.2⟩
    obtain ⟨_,s,z,eq,lit⟩ := Finset.mem_filter.mp edge
    have child0 (i : ℕ) (l r : ℕ) (ins : (gateAt C i).inputs=[l,r]) : opnd C i 0=l ∧ opnd C i 1=r := by
      change (gateAt C i).inputs.getD 0 0=l ∧ (gateAt C i).inputs.getD 1 0=r
      rw [ins];exact ⟨rfl,rfl⟩
    have oriented (u v : Fin n) (same : e=s(u,v)) (eqt : t=u)
        (fire : gateVal n C a (pairInput u v)=true) : ∃ (u v : Fin n) (m : ℕ), e=s(u,v) ∧ m<C.size ∧ (gateAt C m).op=.or ∧
            (orIn n C (n+m)).Nonempty ∧ u∈wmax G C m ∧ (∀ t∈orIn n C (n+m), t≠u ∧ t≠v) ∧
            ∃ b : Fin 2, orIn n C (opnd C m b)=∅ ∧
              (C.wires (List.ofFn (pairInput u v))).getD (opnd C m b) false=true := by
      have un : s(u,v)∈Ustar G C := by rwa [← same]
      have use (p q : ℕ) (ord : (gateAt C a).inputs=[p,q] ∨ (gateAt C a).inputs=[q,p])
          (left : u∈orIn n C p) (right : (orIn n C q).Nonempty) :
          ∃ (u v : Fin n) (m : ℕ), e=s(u,v) ∧ m<C.size ∧ (gateAt C m).op=.or ∧
            (orIn n C (n+m)).Nonempty ∧ u∈wmax G C m ∧ (∀ t∈orIn n C (n+m), t≠u ∧ t≠v) ∧
            ∃ b : Fin 2, orIn n C (opnd C m b)=∅ ∧
              (C.wires (List.ofFn (pairInput u v))).getD (opnd C m b) false=true := by
        obtain ⟨m,hm,h⟩ := routing n G C least a top p q ord u v left right un fire
        exact ⟨u,v,m,same,hm,h⟩
      rcases Finset.mem_union.mp ht with h|h
      · apply use l r (Or.inl ins)
        · change t∈orIn n C (opnd C a 0) at h
          rw [(child0 _ _ _ ins).1,eqt] at h;exact h
        · have bh := both.2
          change (orIn n C (opnd C a 1)).Nonempty at bh
          rwa [(child0 _ _ _ ins).2] at bh
      · apply use r l (Or.inr ins)
        · change t∈orIn n C (opnd C a 1) at h
          rw [(child0 _ _ _ ins).2,eqt] at h;exact h
        · have bh := both.1
          change (orIn n C (opnd C a 0)).Nonempty at bh
          rwa [(child0 _ _ _ ins).1] at bh
    rw [eq,Sym2.mem_iff] at hte
    rcases hte with h|h
    · exact oriented s z eq h lit
    · have swap : pairInput z s=pairInput s z := by funext i;change decide (i=z ∨ i=s)=decide (i=s ∨ i=z); simp [or_comm]
      exact oriented z s (eq.trans Sym2.eq_swap) h (by rwa [swap])
