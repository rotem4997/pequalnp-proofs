import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Duality puts the singleton-true reread on the line side. Along its route to the
-- output, an AND first blocks that singleton. Its other operand separates the cases.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4693_2
    (blocked : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let w (u : ℕ) (p l : Fin 14) := wireVal 14 C u (pairInput p l)
      let a (k : ℕ) := (gateAt C k).op = .and
      let c := InCone 14 C
      let out (k : ℕ) := 14+k = C.output ∨ c k (C.output-14)
      let r (x : Fin 14) (k : ℕ) := a k ∧ out k ∧ w (14+k) 0 7 = true ∧
        ∀ b : Fin 2, w (opnd C k b) x x = false
      ∀ i j, i ≠ j → ¬c i j → ¬c j i → r 0 i → r 7 j → w (14+i) 7 7 = true →
      ∀ (h k : ℕ) (b : Fin 2), (h = i ∨ c i h) → opnd C k b = 14+h → a k → out k →
        w (14+h) 7 7 = true → w (opnd C k (1-b)) 7 7 = false → w (opnd C k (1-b)) 0 7 = false → (∃ t, c k t ∧ out t ∧ ¬a t ∧ w (14+t) 0 7 = true) → False)
    (restored : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
      let w (u : ℕ) (p l : Fin 14) := wireVal 14 C u (pairInput p l)
      let a (k : ℕ) := (gateAt C k).op = .and
      let c := InCone 14 C
      let out (k : ℕ) := 14+k = C.output ∨ c k (C.output-14)
      let r (x : Fin 14) (k : ℕ) := a k ∧ out k ∧ w (14+k) 0 7 = true ∧
        ∀ b : Fin 2, w (opnd C k b) x x = false
      ∀ i j, i ≠ j → ¬c i j → ¬c j i → r 0 i → r 7 j → w (14+i) 7 7 = true →
      ∀ (h k : ℕ) (b : Fin 2), (h = i ∨ c i h) → opnd C k b = 14+h → a k → out k →
        w (14+h) 7 7 = true → w (opnd C k (1-b)) 7 7 = false → w (opnd C k (1-b)) 0 7 = true → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) →           have x6 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x6 : ℕ) (x7 x8 : Fin (14 : ℕ)) => PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8);           have x7 : ℕ → Prop := fun (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;           have x8 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;           have x9 : Fin (14 : ℕ) → ℕ → Prop := fun (x9 : Fin (14 : ℕ)) (x10 : ℕ) => x7 x10 ∧ ((14 : ℕ) + x10 = x1.output ∨ x8 x10 (x1.output - (14 : ℕ))) ∧ x6 x10 (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x11) (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.false;           ∀ (x10 x11 : ℕ), x10 ≠ x11 → ¬x8 x10 x11 → ¬x8 x11 x10 → x9 (0 : Fin (14 : ℕ)) x10 → x9 (7 : Fin (14 : ℕ)) x11 → (∃ (x17 : ℕ), x7 x17 ∧ (x8 x10 x17 ∧ x6 x10 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ x6 x17 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∨ x8 x11 x17 ∧ x6 x11 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x6 x17 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false)) → False := by
  classical
  have gateDef (C : Circuit) (j : ℕ) : gateAt C j = C.gates.getD j ⟨.or, []⟩ := rfl
  have opndDef (C : Circuit) (j : ℕ) (b : Fin 2) :
      opnd C j b = (gateAt C j).inputs.getD b.val 0 := rfl
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wire_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step w g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

  have old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      apply List.getD_append
      exact hi

  have gate_value (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
      (valid : ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < w.length + j) :
      let W := gs.foldl step w
      W.getD (w.length + j) false = (gs.getD j ⟨.or, []⟩).op.eval
        ((gs.getD j ⟨.or, []⟩).inputs.map fun i => W.getD i false) := by
    induction gs using List.reverseRecOn with
    | nil => simp at hj
    | append_singleton gs g ih =>
      have before : ((gs ++ [g]).foldl step w) = step (gs.foldl step w) g := by
        rw [List.foldl_append]; rfl
      rw [List.length_append, List.length_singleton] at hj
      by_cases he : j < gs.length
      · rw [List.getD_append _ _ _ _ he] at valid
        simp only [before, List.getD_append _ _ _ _ he]
        have h₁ : w.length + j < (gs.foldl step w).length := by rw [wire_len]; omega
        have h₂ (i : ℕ) (hi : i ∈ (gs.getD j ⟨.or, []⟩).inputs) :
            (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
          apply List.getD_append
          rw [wire_len]
          have := valid i hi
          omega
        change (step (gs.foldl step w) g).getD (w.length + j) false = _
        rw [show (step (gs.foldl step w) g).getD (w.length + j) false =
          (gs.foldl step w).getD (w.length + j) false from List.getD_append _ _ _ _ h₁,
          List.map_congr_left h₂]
        exact ih he valid
      · have heq : j = gs.length := by omega
        subst j
        simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at valid ⊢
        rw [before]
        have h₁ : w.length + gs.length = (gs.foldl step w).length := (wire_len gs w).symm
        have h₂ (i : ℕ) (hi : i ∈ g.inputs) :
            (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
          apply List.getD_append
          exact (valid i hi).trans_eq h₁
        change (step (gs.foldl step w) g).getD (w.length + gs.length) false = _
        rw [List.map_congr_left h₂, h₁]
        simp [step, List.getD_eq_getElem?_getD]

  have wire_at {n : ℕ} (C : Circuit) (B : ReadsBack n C) (x : Fin n → Bool)
      (j : ℕ) (hj : j < C.gates.length) :
      wireVal n C (n + j) x = (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
    have h := gate_value C.gates (List.ofFn x) j hj (by simpa only [List.length_ofFn, gateDef] using B j hj)
    let W := C.gates.foldl step (List.ofFn x)
    change W.getD (n + j) false = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => W.getD i false)
    simpa only [W, List.length_ofFn, gateDef] using h

  have input_at {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
      wireVal n C i x = x i := by
    unfold wireVal
    change (C.gates.foldl step (List.ofFn x)).getD i false = x i
    rw [old_read _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]

  have or_at {n : ℕ} (C : Circuit) (B : ReadsBack n C) (x : Fin n → Bool)
      (j i : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = .or)
      (hi : i ∈ (gateAt C j).inputs) (ht : wireVal n C i x = true) :
      wireVal n C (n + j) x = true := by
    rw [wire_at C B x j hj, ho]
    change (((gateAt C j).inputs.map fun k => wireVal n C k x).any id) = true
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨i, hi, ht⟩, rfl⟩

  let run {α : Type} (next : List α → Gate → α) (gs : List Gate) : List α :=
    gs.foldl (fun s g => s ++ [next s g]) []

  have run_length {α : Type} (next : List α → Gate → α) (gs : List Gate) :
      (run next gs).length = gs.length := by
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      unfold run at ih ⊢
      rw [List.foldl_append]
      simp [ih]

  have run_slot {α : Type} (next : List α → Gate → α) (d : α)
      (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      (run next gs).getD j d = next ((run next gs).take j) (gs.getD j ⟨.or, []⟩) := by
    induction gs using List.reverseRecOn with
    | nil => simp at hj
    | append_singleton gs g ih =>
      have grow : run next (gs ++ [g]) = run next gs ++ [next (run next gs) g] := by
        unfold run
        rw [List.foldl_append]
        rfl
      have len := run_length next gs
      rw [grow]
      by_cases h : j < gs.length
      · have hs : j < (run next gs).length := h.trans_eq len.symm
        rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ h,
          List.take_append_of_le_length (Nat.le_of_lt hs)]
        exact ih h
      · rw [List.length_append, List.length_singleton] at hj
        have eq : j = gs.length := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl,
          len, Nat.sub_self, List.getD_cons_zero, List.getD_cons_zero,
          List.take_append_of_le_length (by omega)]
        simp [←len]

  let coneEntry (n : ℕ) (s : List (List ℕ)) (g : Gate) : List ℕ :=
    (g.inputs.filter fun w => decide (n ≤ w ∧ w < n + s.length)).flatMap
      (fun w => (w - n) :: s.getD (w - n) [])

  have cone_from_pin {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (w : ℕ) (hw : w ∈ (gateAt C j).inputs) (hl : n ≤ w) (hh : w < n + j)
      (k : ℕ) (hk : k = w - n ∨ InCone n C k (w - n)) : InCone n C k j := by
    let s := run (coneEntry n) C.gates
    have len : (s.take j).length = j := by
      simp [s, run_length, Nat.min_eq_left (Nat.le_of_lt hj)]
    have slot := run_slot (coneEntry n) [] C.gates j hj
    change k ∈ s.getD j []
    rw [slot]
    change k ∈ coneEntry n (s.take j) (gateAt C j)
    simp only [coneEntry, len, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    refine ⟨w, ⟨hw, hl, hh⟩, ?_⟩
    rcases hk with h | h
    · exact Or.inl h
    · right
      change k ∈ s.getD (w - n) [] at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
      simpa only [List.getD_eq_getElem?_getD] using h

  have gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _

  have coneParent {n : ℕ} (C : Circuit) (i j : ℕ) (inside : InCone n C i j) :
      j < C.gates.length ∧ ∃ k < j, n+k ∈ (gateAt C j).inputs ∧ (i = k ∨ InCone n C i k) := by
    let s := run (coneEntry n) C.gates
    change i ∈ s.getD j [] at inside
    have hj : j < C.gates.length := by
      by_contra h
      rw [List.getD_eq_default _ _ (by change (run (coneEntry n) C.gates).length ≤ j; rw [run_length]; omega)] at inside
      exact List.not_mem_nil inside
    have len : (s.take j).length = j := by
      simp [s,run_length,Nat.min_eq_left hj.le]
    have slot := run_slot (coneEntry n) [] C.gates j hj
    rw [slot] at inside
    change i ∈ coneEntry n (s.take j) (gateAt C j) at inside
    simp only [coneEntry,len,List.mem_flatMap,List.mem_filter,decide_eq_true_eq,List.mem_cons] at inside
    obtain ⟨w,⟨wm,lo,hi⟩,loc⟩ := inside
    refine ⟨hj,w-n,by omega,by simpa only [show n+(w-n)=w by omega] using wm,?_⟩
    rcases loc with same | old
    · exact Or.inl same
    · right
      change i ∈ s.getD (w-n) []
      rwa [List.getD_eq_getElem?_getD,List.getElem?_take_of_lt (by omega),
        ←List.getD_eq_getElem?_getD] at old
  let exactFano (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
  let singleton (C : Circuit) (w : ℕ) (a : Fin 14) := wireVal 14 C w (pairInput a a)
  let flag (C : Circuit) (w : ℕ) := wireVal 14 C w (pairInput 0 7)
  let andAt (C : Circuit) (j : ℕ) := (gateAt C j).op = .and
  let root (C : Circuit) (j : ℕ) := 14+j = C.output ∨ InCone 14 C j (C.output-14)
  let reread (C : Circuit) (x : Fin 14) (j : ℕ) := andAt C j ∧ root C j ∧
    flag C (14+j) = true ∧ ∀ b : Fin 2, singleton C (opnd C j b) x = false
  have rejects (C : Circuit) (eqn : exactFano C) (a : Fin 14) :
      C.eval (List.ofFn (pairInput a a)) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro yes
    obtain ⟨p,l,_,py,ly⟩ := (eqn _).mp yes
    have hp : Fin.castAdd 7 p = a ∨ Fin.castAdd 7 p = a := of_decide_eq_true py
    have hl : Fin.natAdd 7 l = a ∨ Fin.natAdd 7 l = a := of_decide_eq_true ly
    have bad := congrArg Fin.val ((hp.elim id id).trans (hl.elim id id).symm)
    change p.val = 7+l.val at bad
    have := p.isLt
    omega
  have outputInternal (C : Circuit) (eqn : exactFano C) : 14 ≤ C.output := by
    by_contra h
    let a : Fin 14 := ⟨C.output,by omega⟩
    have on : wireVal 14 C C.output (pairInput a a) = true := by
      change wireVal 14 C a.val (pairInput a a) = true
      rw [input_at C _ a]
      exact decide_eq_true (Or.inl rfl)
    change C.eval (List.ofFn (pairInput a a)) = true at on
    rw [rejects C eqn a] at on
    contradiction
  have directLoss (C : Circuit) (AO : IsAO2 14 C) (i : ℕ) (x : Fin 14)
      (on : singleton C (14+i) x = true) :
      ∀ j, InCone 14 C i j → singleton C (14+j) x = false →
      ∃ (h k : ℕ) (b : Fin 2), (h = i ∨ InCone 14 C i h) ∧
        opnd C k b = 14+h ∧ andAt C k ∧ (k = j ∨ InCone 14 C k j) ∧
        singleton C (14+h) x = true ∧ singleton C (opnd C k (1-b)) x = false := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro inside off
      obtain ⟨jl,h,hl,hm,below⟩ := coneParent C i j inside
      by_cases active : singleton C (14+h) x = true
      · have hand : andAt C j := by
          rcases AO.1 _ (gate_mem C j jl) with a | o
          · exact a
          · have nay := or_at C AO.2.1 (pairInput x x) j (14+h) jl o hm active
            exact Bool.noConfusion (nay.symm.trans off)
        obtain ⟨r,s,pins⟩ := List.length_eq_two.mp (AO.2.2 _ (gate_mem C j jl))
        have both : (singleton C r x && singleton C s x) = false := by
          have eqn := wire_at C AO.2.1 (pairInput x x) j jl
          have aop : (gateAt C j).op = .and := hand
          rw [aop,pins] at eqn
          change wireVal 14 C (14+j) (pairInput x x) =
            (singleton C r x && (singleton C s x && true)) at eqn
          simpa only [Bool.and_true] using eqn.symm.trans off
        have input : 14+h = r ∨ 14+h = s := by simpa only [pins,List.mem_cons,List.not_mem_nil,or_false] using hm
        have desc : h = i ∨ InCone 14 C i h := below.imp_left Eq.symm
        rcases input with hr | hs
        · have other : singleton C s x = false := by
            rw [←hr,active,Bool.true_and] at both
            exact both
          refine ⟨h,j,0,desc,?_,hand,Or.inl rfl,active,?_⟩
          · simpa [opndDef,pins] using hr.symm
          · simpa [opndDef,pins] using other
        · have other : singleton C r x = false := by
            rw [←hs,active,Bool.and_true] at both
            exact both
          refine ⟨h,j,1,desc,?_,hand,Or.inl rfl,active,?_⟩
          · simpa [opndDef,pins] using hs.symm
          · simpa [opndDef,pins] using other
      · rcases below with same | path
        · exact (active (same ▸ on)).elim
        · obtain ⟨p,k,b,pr,pin,ka,krel,yes,no⟩ := ih h hl path (Bool.eq_false_of_not_eq_true active)
          refine ⟨p,k,b,pr,pin,ka,Or.inr ?_,yes,no⟩
          apply cone_from_pin C j jl (14+h) hm (by omega) (by omega) k
          simpa only [Nat.add_sub_cancel_left] using krel
  have lossToOutput (C : Circuit) (ao : IsAO2 14 C) (eqn : exactFano C) (i : ℕ)
      (rr : reread C 0 i) (on : singleton C (14+i) 7 = true) :
      ∃ (h k : ℕ) (b : Fin 2), (h = i ∨ InCone 14 C i h) ∧
        opnd C k b = 14+h ∧ andAt C k ∧ root C k ∧
        singleton C (14+h) 7 = true ∧ singleton C (opnd C k (1-b)) 7 = false := by
    let o := C.output-14
    have offset : 14+o = C.output := by have := outputInternal C eqn; dsimp [o]; omega
    have off : singleton C (14+o) 7 = false := by rw [offset]; exact rejects C eqn 7
    rcases rr.2.1 with eq | inside
    · rw [eq] at on
      have stop := rejects C eqn 7
      exact Bool.noConfusion (on.symm.trans stop)
    · obtain ⟨h,k,b,desc,pin,ka,r,yes,no⟩ := directLoss C ao i 7 on o inside off
      refine ⟨h,k,b,desc,pin,ka,?_,yes,no⟩
      rcases r with eq | path
      · exact Or.inl (eq ▸ offset)
      · exact Or.inr path
  have regained (C : Circuit) (ao : IsAO2 14 C) (k : ℕ) (lost : flag C (14+k) = false) :
      ∀ o, InCone 14 C k o → flag C (14+o) = true →
      ∃ t, InCone 14 C k t ∧ (t = o ∨ InCone 14 C t o) ∧ ¬andAt C t ∧ flag C (14+t) = true := by
    intro o
    induction o using Nat.strong_induction_on with
    | ind o ih =>
      intro inside yes
      by_cases isAnd : andAt C o
      · obtain ⟨ol,h,hl,hm,desc⟩ := coneParent C k o inside
        have op : (gateAt C o).op = .and := isAnd
        have eqn := wire_at C ao.2.1 (pairInput 0 7) o ol
        rw [op] at eqn
        have good : ((gateAt C o).inputs.map fun w => flag C w).all id = true := eqn.symm.trans yes
        have hyes : flag C (14+h) = true := List.all_eq_true.mp good _
          (List.mem_map.mpr ⟨14+h,hm,rfl⟩)
        rcases desc with rfl | path
        · exact Bool.noConfusion (hyes.symm.trans lost)
        · obtain ⟨t,kt,toh,ta,tf⟩ := ih h hl path hyes
          refine ⟨t,kt,Or.inr ?_,ta,tf⟩
          apply cone_from_pin C o ol (14+h) hm (by omega) (by omega) t
          simpa only [Nat.add_sub_cancel_left] using toh
      · exact ⟨o,inside,Or.inl rfl,isAnd,yes⟩
  have regainAtOutput (C : Circuit) (ao : IsAO2 14 C) (eqn : exactFano C) (k : ℕ) (b : Fin 2)
      (ka : andAt C k) (kr : root C k) (other : flag C (opnd C k b) = false) :
      ∃ t, InCone 14 C k t ∧ root C t ∧ ¬andAt C t ∧ flag C (14+t) = true := by
    have ko : (gateAt C k).op = .and := ka
    have kl : k < C.gates.length := by
      by_contra h
      change (C.gates.getD k ⟨.or,[]⟩).op = .and at ko
      rw [List.getD_eq_default _ _ (by omega)] at ko
      contradiction
    have pinMem : opnd C k b ∈ (gateAt C k).inputs := by
      rw [opndDef, List.getD_eq_getElem _ _ (by rw [ao.2.2 _ (gate_mem C k kl)]; exact b.isLt)]
      exact List.getElem_mem _
    have lost : flag C (14+k) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro yes
      have gateEval :=  wire_at C ao.2.1 (pairInput 0 7) k kl
      rw [ko] at gateEval
      have h : ((gateAt C k).inputs.map fun w => flag C w).all id = true := gateEval.symm.trans yes
      have activated : flag C (opnd C k b) = true := List.all_eq_true.mp h _
        (List.mem_map.mpr ⟨_,pinMem,rfl⟩)
      rw [other] at activated
      contradiction
    have outputYes : flag C C.output = true := by
      apply (eqn _).mpr
      exact ⟨0,0,Or.inl rfl,by decide,by decide⟩
    let o := C.output-14
    have offset : 14+o = C.output := by have := outputInternal C eqn; dsimp [o]; omega
    rcases kr with eq | cone
    · rw [eq,outputYes] at lost
      contradiction
    · obtain ⟨t,kt,tr,ta,tf⟩ := regained C ao k lost o cone (by rwa [offset])
      refine ⟨t,kt,?_,ta,tf⟩
      rcases tr with same | anc
      · exact Or.inl (same ▸ offset)
      · exact Or.inr anc
  have dualData (C : Circuit) (AO : IsAO2 14 C)
      (nodup : ∀ g ∈ C.gates, g.inputs.Nodup)
      (comp : exactFano C) :
      ∃ D : Circuit, D.size = C.size ∧ IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        exactFano D ∧ D.output = C.output ∧
        (∀ j, (gateAt D j).op = (gateAt C j).op) ∧
        (∀ i j, InCone 14 D i j ↔ InCone 14 C i j) ∧
        (∀ j, gateVal 14 D j (pairInput 0 7) = gateVal 14 C j (pairInput 0 7) ∧
          gateVal 14 D j (pairInput 0 0) = gateVal 14 C j (pairInput 7 7) ∧
          gateVal 14 D j  (pairInput 7 7) = gateVal 14 C j (pairInput 0 0)) ∧
        (∀ j < C.size, ∀ b : Fin 2,
          wireVal 14 D (opnd D j b) (pairInput 0 0) =
            wireVal 14 C (opnd C j b) (pairInput 7 7) ∧
          wireVal 14 D (opnd D j b) (pairInput 7 7) =
            wireVal 14 C (opnd C j b) (pairInput 0 0)) := by
    let rename {n : ℕ} (p : Fin n → Fin n) (i : ℕ) : ℕ := if h : i < n then (p ⟨i, h⟩).val else i

    have rename_small {n : ℕ} (p : Fin n → Fin n) (i : ℕ) : rename p i < n ↔ i < n := by
      by_cases hi : i < n
      · simp [rename, hi, (p ⟨i, hi⟩).isLt]
      · simp [rename, hi]

    have rename_internal {n : ℕ} (p : Fin n → Fin n) {i : ℕ} (hi : n ≤ i) : rename p i = i := by
      simp [rename, Nat.not_lt.mpr hi]

    let mapGate {n : ℕ} (p : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rename p)⟩

    let mapCircuit {n : ℕ} (p : Fin n → Fin n) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate p), rename p C.output⟩

    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

    have same_after_append {n : ℕ} (p : Fin n → Fin n) (old new : List Bool)
        (hlen : old.length = new.length) (hraw : n ≤ old.length)
        (hbit : ∀ i, new.getD (rename p i) false = old.getD i false) (b : Bool) :
        ∀ i, (new ++ [b]).getD (rename p i) false = (old ++ [b]).getD i false := by
      intro i
      by_cases hi : i < old.length
      · have hnew : rename p i < new.length := by
          by_cases h : i < n
          · have hp := (rename_small p i).mpr h
            omega
          · rw [rename_internal p (Nat.le_of_not_gt h)]
            omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hnew,
          List.getElem?_append_left hi]
        simpa only [List.getD_eq_getElem?_getD] using hbit i
      · have hri := rename_internal p (by omega : n ≤ i)
        have hnew : new.length ≤ i := by omega
        rw [hri]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_gt hi),
          List.getElem?_append_right hnew, hlen]

    have propagate {n : ℕ} (p : Fin n → Fin n) (gs : List Gate) (old new : List Bool)
        (hlen : old.length = new.length) (hraw : n ≤ old.length)
        (hbit : ∀ i, new.getD (rename p i) false = old.getD i false) :
        ∀ i, ((gs.map (mapGate p)).foldl step new).getD (rename p i) false =
          (gs.foldl step old).getD i false := by
      induction gs generalizing old new with
      | nil => exact hbit
      | cons g gs ih =>
        change ∀ i, ((gs.map (mapGate p)).foldl step (step new (mapGate p g))).getD (rename p i) false =
          (gs.foldl step (step old g)).getD i false
        have eqb : (g.inputs.map (rename p)).map (fun i => new.getD i false) =
            g.inputs.map (fun i => old.getD i false) := by
          rw [List.map_map]
          exact List.map_congr_left fun i _ => hbit i
        have hn : step new (mapGate p g) = new ++ [g.op.eval (g.inputs.map fun i => old.getD i false)] := by
          simp only [step, mapGate, eqb]
        rw [hn]
        exact ih _ _ (by simp [step, hlen]) (by simp [step]; omega)
          (same_after_append p old new hlen hraw hbit _)

    have input_read {n : ℕ} (p : Fin n → Fin n) (x : Fin n → Bool) :
        ∀ i : ℕ, (List.ofFn x).getD (rename p i) false = (List.ofFn (x ∘ p)).getD i false := by
      intro i
      by_cases hi : i < n
      · simp [rename, hi, List.getD_eq_getElem?_getD, (p ⟨i, hi⟩).isLt]
      · simp [rename, hi, List.getD_eq_getElem?_getD]

    have map_ao {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (H : IsAO2 n C) :
        IsAO2 n (mapCircuit p C) := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
        exact H.1 old ho
      · intro j hj i hi
        have hc : j < C.gates.length := by simpa [mapCircuit] using hj
        have eqGate : gateAt (mapCircuit p C) j = mapGate p (gateAt C j) := by
          change (C.gates.map (mapGate p)).getD j ⟨.or, []⟩ =
            mapGate p (C.gates.getD j ⟨.or, []⟩)
          rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getD_eq_getElem _ _ hc]
          simp only [List.getElem_map]
        rw [eqGate] at hi
        obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hi
        have back := H.2.1 j hc raw hraw
        by_cases hn : raw < n
        · have := (rename_small p raw).mpr hn
          omega
        · rw [rename_internal p (Nat.le_of_not_gt hn)]
          exact back
      · intro g hg
        obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
        simpa [mapGate] using H.2.2 _ ho

    have map_eval {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
        circuitFun n (mapCircuit p C) x = circuitFun n C (x ∘ p) :=
      propagate p C.gates (List.ofFn (x ∘ p)) (List.ofFn x) (by simp) (by simp) (input_read p x) C.output

    let dual : Fin 14 → Fin 14 := fun w =>
      Fin.addCases (motive := fun _ : Fin (7 + 7) => Fin 14)
        (fun p : Fin 7 => Fin.natAdd 7 (-p)) (fun l : Fin 7 => Fin.castAdd 7 (-l)) w
    have dualL (p : Fin 7) : dual (Fin.castAdd 7 p) = Fin.natAdd 7 (-p) := by
      dsimp only [dual]
      rw [Fin.addCases_left]
    have dualR (l : Fin 7) : dual (Fin.natAdd 7 l) = Fin.castAdd 7 (-l) := by
      dsimp only [dual]
      rw [Fin.addCases_right]
    have dualTwice (u : Fin 14) : dual (dual u) = u := by
      refine Fin.addCases (m := 7) (n := 7) (motive := fun u => dual (dual u) = u) ?_ ?_ u
      · intro p
        rw [dualL, dualR, neg_neg]
      · intro l
        rw [dualR, dualL, neg_neg]
    have dualInj : Function.Injective dual := by
      intro a b eq
      calc
        a = dual (dual a) := (dualTwice a).symm
        _ = dual (dual b) := congrArg dual eq
        _ = b := dualTwice b
    have dualZero : dual 0 = 7 := by
      have h := dualL 0
      rw [neg_zero, show Fin.castAdd 7 (0 : Fin 7) = (0 : Fin 14) by decide,
        show Fin.natAdd 7 (0 : Fin 7) = (7 : Fin 14) by decide] at h
      exact h
    have dualSeven : dual 7 = 0 := by
      have h := dualR 0
      rw [neg_zero, show Fin.castAdd 7 (0 : Fin 7) = (0 : Fin 14) by decide,
        show Fin.natAdd 7 (0 : Fin 7) = (7 : Fin 14) by decide] at h
      exact h

    have renameInj : Function.Injective (rename dual) := by
      intro a b eq
      by_cases ha : a < 14
      · have hb : b < 14 := (rename_small dual b).mp (eq ▸ (rename_small dual a).mpr ha)
        have h : (dual ⟨a,ha⟩).val = (dual ⟨b,hb⟩).val := by
          simpa only [rename, dite_eq_left ha, dite_eq_left hb] using eq
        exact congrArg Fin.val (dualInj (Fin.val_injective h))
      · have hb : ¬ b < 14 := by
          intro h
          exact ha ((rename_small dual a).mp (eq.symm ▸ (rename_small dual b).mpr h))
        rwa [rename_internal dual (Nat.le_of_not_gt ha), rename_internal dual (Nat.le_of_not_gt hb)] at eq

    have nodupDual (C : Circuit) (h : ∀ g ∈ C.gates, g.inputs.Nodup) :
        ∀ g ∈ (mapCircuit dual C).gates, g.inputs.Nodup := by
      intro g hg
      obtain ⟨r,mem,rfl⟩ := List.mem_map.mp hg
      exact (h r mem).map renameInj

    let fano (x : Fin 14 → Bool) : Prop :=
      ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
    have incidence (p l : Fin 7) :
        (p = l ∨ p = l+1 ∨ p = l+3) ↔
          (-l = -p ∨ -l = -p+1 ∨ -l = -p+3) := by
      have tab : ∀ p l : Fin 7,
          (p = l ∨ p = l+1 ∨ p = l+3) ↔
            (-l = -p ∨ -l = -p+1 ∨ -l = -p+3) := by decide
      exact tab p l
    have fanoSame (x : Fin 14 → Bool) : fano (x ∘ dual) ↔ fano x := by
      constructor
      · rintro ⟨p,l,h,hp,hl⟩
        have ap : x (Fin.natAdd 7 (-p)) = true := by
          change x (dual (Fin.castAdd 7 p)) = true at hp
          rwa [dualL] at hp
        have al : x (Fin.castAdd 7 (-l)) = true := by
          change x (dual (Fin.natAdd 7 l)) = true at hl
          rwa [dualR] at hl
        exact ⟨-l,-p,(incidence p l).mp h,al,ap⟩
      · rintro ⟨p,l,h,hp,hl⟩
        refine ⟨-l,-p,(incidence p l).mp h,?_,?_⟩
        · change x (dual (Fin.castAdd 7 (-l))) = true
          rwa [dualL, neg_neg]
        · change x (dual (Fin.natAdd 7 (-p))) = true
          rwa [dualR, neg_neg]

    have samePair (u v : Fin 14) : pairInput u v ∘ dual = pairInput (dual u) (dual v) := by
      funext w
      change decide (dual w = u ∨ dual w = v) = decide (w = dual u ∨ w = dual v)
      have one (t : Fin 14) : dual w = t ↔ w = dual t := by
        constructor
        · intro h
          simpa only [dualTwice] using congrArg dual h
        · intro h
          simpa only [dualTwice] using congrArg dual h
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,one]
    have swapPair : pairInput (7 : Fin 14) 0 = pairInput 0 7 := by
      funext w
      change decide (w = 7 ∨ w = 0) = decide (w = 0 ∨ w = 7)
      simp only [or_comm]
    have rowsPair (x : Fin 14 → Bool) (i : ℕ) (C : Circuit) :
        wireVal 14 (mapCircuit dual C) (rename dual i) x = wireVal 14 C i (x ∘ dual) :=
      propagate dual C.gates (List.ofFn (x ∘ dual)) (List.ofFn x) (by simp) (by simp)
        (input_read dual x) i
    have gatesPair (C : Circuit) (j : ℕ) (u v : Fin 14) :
        gateVal 14 (mapCircuit dual C) j (pairInput u v) =
          gateVal 14 C j (pairInput (dual u) (dual v)) := by
      have h := rowsPair (pairInput u v) (14+j) C
      rw [rename_internal dual (by omega), samePair] at h
      exact h

    have originalOutInternal (C : Circuit)
        (h : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) :
        14 ≤ C.output := by
      by_contra! lt
      let u : Fin 14 := ⟨C.output,lt⟩
      have single (z : Fin 14) (b : Fin 14) : pairInput z z b = true → b = z := by
        intro e
        change decide (b = z ∨ b = z) = true at e
        simpa using e
      have falseAt : ¬ fano (pairInput u u) := by
        rintro ⟨p,l,_,a,b⟩
        have eq : Fin.castAdd 7 p = Fin.natAdd 7 l :=
          (single u _ a).trans (single u _ b).symm
        have pe : p.val < 7 := p.isLt
        have ex := congrArg Fin.val eq
        change p.val = 7 + l.val at ex
        omega
      have oldRead (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
          (gs.foldl step W).getD i false = W.getD i false := by
        induction gs generalizing W with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons, ih _ (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hi
      have on : C.eval (List.ofFn (pairInput u u)) = true := by
        change (C.gates.foldl step (List.ofFn (pairInput u u))).getD C.output false = true
        rw [oldRead _ _ _ (by simpa using lt)]
        change (List.ofFn (pairInput u u)).getD u.val false = true
        rw [List.getD_eq_getElem _ _ (by simpa using u.isLt), List.getElem_ofFn]
        change decide (u=u ∨ u=u) = true
        simp
      exact falseAt ((h _).mp on)

    have outDual (C : Circuit)
        (h : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) :
        (mapCircuit dual C).output = C.output := rename_internal dual (originalOutInternal C h)
    have semDual (C : Circuit)
        (h : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) :
        ∀ x : Fin 14 → Bool, (mapCircuit dual C).eval (List.ofFn x) = true ↔ fano x := by
      intro x
      change circuitFun 14 (mapCircuit dual C) x = true ↔ fano x
      rw [map_eval]
      exact (h (x ∘ dual)).trans (fanoSame x)

    let renameGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

    have rename_filter {n : ℕ} (ρ : ℕ → ℕ) (raw : ∀ w < n, ρ w < n)
        (fixed : ∀ w, n ≤ w → ρ w = w) (m : ℕ) (ws : List ℕ) :
        (ws.map ρ).filter (fun w => decide (n ≤ w ∧ w < n + m)) =
        ws.filter (fun w => decide (n ≤ w ∧ w < n + m)) := by
      induction ws with
      | nil => rfl
      | cons w ws ih =>
        simp only [List.map_cons, List.filter_cons, ih]
        by_cases h : w < n
        · simp [Nat.not_le.mpr h, Nat.not_le.mpr (raw w h)]
        · simp [fixed w (Nat.le_of_not_gt h)]

    have rename_coneStep {n : ℕ} (ρ : ℕ → ℕ) (raw : ∀ w < n, ρ w < n)
        (fixed : ∀ w, n ≤ w → ρ w = w) (cs : List (List ℕ)) (g : Gate) :
        coneStep n cs (renameGate ρ g) = coneStep n cs g := by
      change cs ++ [((g.inputs.map ρ).filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap _] = _
      rw [rename_filter ρ raw fixed]
      rfl

    have rename_cones {n : ℕ} (ρ : ℕ → ℕ) (raw : ∀ w < n, ρ w < n)
        (fixed : ∀ w, n ≤ w → ρ w = w) (C D : Circuit)
        (renamed : D.gates = C.gates.map (renameGate ρ)) : cones n D = cones n C := by
      have fold : ∀ (gs : List Gate) (cs : List (List ℕ)),
          (gs.map (renameGate ρ)).foldl (coneStep n) cs = gs.foldl (coneStep n) cs := by
        intro gs
        induction gs with
        | nil => intro cs; rfl
        | cons g gs ih =>
          intro cs
          simp only [List.map_cons, List.foldl_cons, rename_coneStep ρ raw fixed, ih]
      change D.gates.foldl (coneStep n) [] = C.gates.foldl (coneStep n) []
      rw [renamed]
      exact fold C.gates []

    have rename_inCone {n : ℕ} (ρ : ℕ → ℕ) (raw : ∀ w < n, ρ w < n)
        (fixed : ∀ w, n ≤ w → ρ w = w) (C D : Circuit)
        (renamed : D.gates = C.gates.map (renameGate ρ)) (i j : ℕ) :
        InCone n D i j ↔ InCone n C i j := by
      unfold InCone
      rw [rename_cones ρ raw fixed C D renamed]

    have rename_gateAt (ρ : ℕ → ℕ) (C D : Circuit)
        (renamed : D.gates = C.gates.map (renameGate ρ)) (i : ℕ) :
        gateAt D i = renameGate ρ (gateAt C i) := by
      unfold gateAt
      simp only [renamed, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases C.gates[i]? <;> rfl

    have rename_gateOp (ρ : ℕ → ℕ) (C D : Circuit)
        (renamed : D.gates = C.gates.map (renameGate ρ)) (i : ℕ) :
        (gateAt D i).op = (gateAt C i).op := by
      rw [rename_gateAt ρ C D renamed]

    have rename_opnd (ρ : ℕ → ℕ) (C D : Circuit)
        (renamed : D.gates = C.gates.map (renameGate ρ)) (i : ℕ) (b : Fin 2)
        (inRange : b.val < (gateAt C i).inputs.length) : opnd D i b = ρ (opnd C i b) := by
      unfold opnd
      rw [rename_gateAt ρ C D renamed]
      change ((gateAt C i).inputs.map ρ).getD b.val 0 = ρ ((gateAt C i).inputs.getD b.val 0)
      have mappedRange : b.val < ((gateAt C i).inputs.map ρ).length := by simpa using inRange
      rw [List.getD_eq_getElem _ _ mappedRange, List.getD_eq_getElem _ _ inRange, List.getElem_map]

    have rename_opnd_AO2 {n : ℕ} (ρ : ℕ → ℕ) (C D : Circuit)
        (renamed : D.gates = C.gates.map (renameGate ρ)) (AO : IsAO2 n C)
        (i : ℕ) (valid : i < C.gates.length) (b : Fin 2) : opnd D i b = ρ (opnd C i b) := by
      apply rename_opnd ρ C D renamed
      have mem : gateAt C i ∈ C.gates := by
        change C.gates.getD i ⟨.or, []⟩ ∈ C.gates
        rw [List.getD_eq_getElem _ _ valid]
        exact List.getElem_mem valid
      rw [AO.2.2 _ mem]
      exact b.isLt

    have dualData (C : Circuit) (AO : IsAO2 14 C)
        (nodup : ∀ g ∈ C.gates, g.inputs.Nodup)
        (comp : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) :
        ∃ D : Circuit, D.size = C.size ∧ IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
          (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔ fano x) ∧ D.output = C.output ∧
          (∀ j, (gateAt D j).op = (gateAt C j).op) ∧
          (∀ i j, InCone 14 D i j ↔ InCone 14 C i j) ∧
          (∀ j, gateVal 14 D j (pairInput 0 7) = gateVal 14 C j (pairInput 0 7) ∧
            gateVal 14 D j (pairInput 0 0) = gateVal 14 C j (pairInput 7 7) ∧
            gateVal 14 D j  (pairInput 7 7) = gateVal 14 C j (pairInput 0 0)) ∧
          (∀ j < C.size, ∀ b : Fin 2,
            wireVal 14 D (opnd D j b) (pairInput 0 0) =
              wireVal 14 C (opnd C j b) (pairInput 7 7) ∧
            wireVal 14 D (opnd D j b) (pairInput 7 7) =
              wireVal 14 C (opnd C j b) (pairInput 0 0)) := by
      let D := mapCircuit dual C
      have len : D.size = C.size := by
        change (C.gates.map (mapGate dual)).length = C.gates.length
        simp
      have ren : D.gates = C.gates.map (renameGate (rename dual)) := rfl
      have raw : ∀ w < 14, rename dual w < 14 := fun w h => (rename_small dual w).mpr h
      have fix : ∀ w, 14 ≤ w → rename dual w = w := fun _ h => rename_internal dual h
      refine ⟨D, len, map_ao dual C AO, nodupDual C nodup, semDual C comp, outDual C comp,
        rename_gateOp (rename dual) C D ren, rename_inCone (rename dual) raw fix C D ren, ?_, ?_⟩
      · intro j
        refine ⟨?_,?_,?_⟩
        · simpa only [dualZero, dualSeven, swapPair] using gatesPair C j 0 7
        · simpa only [dualZero] using gatesPair C j 0 0
        · simpa only [dualSeven] using gatesPair C j 7 7
      · intro j hj b
        have opEq := rename_opnd_AO2 (rename dual) C D ren AO j hj b
        constructor
        · rw [opEq, rowsPair, samePair, dualZero]
        · rw [opEq, rowsPair, samePair, dualSeven]
    exact dualData C AO nodup comp
  have onBranch (C : Circuit) (sz : C.size ≤ 27) (ao : IsAO2 14 C)
      (nd : ∀ g ∈ C.gates, g.inputs.Nodup) (equation : exactFano C)
      (i j : ℕ) (ne : i ≠ j) (ij : ¬InCone 14 C i j) (ji : ¬InCone 14 C j i)
      (ri : reread C 0 i) (rj : reread C 7 j) (hot : singleton C (14+i) 7 = true) : False := by
    obtain ⟨h,k,b,reach,pin,ka,kr,active,sideOff⟩ := lossToOutput C ao equation i ri hot
    cases hb : flag C (opnd C k (1-b)) with
    | false =>
      exact blocked C sz ao nd equation i j ne ij ji ri rj hot h k b reach pin ka kr active sideOff hb
        (regainAtOutput C ao equation k (1-b) ka kr hb)
    | true =>
      exact restored C sz ao nd equation i j ne ij ji ri rj hot h k b reach pin ka kr active sideOff hb
  intro C sz ao nd equation
  dsimp only
  intro i j ne ij ji ri rj obstruction
  change reread C 0 i at ri
  change reread C 7 j at rj
  obtain ⟨_,_,h | h⟩ := obstruction
  · exact onBranch C sz ao nd equation i j ne ij ji ri rj h.2.1
  · obtain ⟨D,len,dao,dnd,deq,outEq,opEq,coneEq,gateEq,pinEq⟩ := dualData C ao nd equation
    have internal (k : ℕ) (andGate : andAt C k) : k < C.size := by
      by_contra no
      change (C.gates.getD k ⟨.or,[]⟩).op = .and at andGate
      rw [List.getD_eq_default _ _ (show C.gates.length ≤ k from Nat.le_of_not_gt no)] at andGate
      contradiction
    have rootEq (k : ℕ) : root C k → root D k := by
      rintro (same | inside)
      · exact Or.inl (same.trans outEq.symm)
      · right
        rw [outEq]
        exact (coneEq _ _).mpr inside
    have bit (k : ℕ) : flag D (14+k) = flag C (14+k) := (gateEq k).1
    have flippedJ : reread D 0 j :=
      ⟨(opEq j).trans rj.1,rootEq j rj.2.1,(bit j).trans rj.2.2.1,
        fun b => ((pinEq j (internal j rj.1) b).1).trans (rj.2.2.2 b)⟩
    have flippedI : reread D 7 i :=
      ⟨(opEq i).trans ri.1,rootEq i ri.2.1,(bit i).trans ri.2.2.1,
        fun b => ((pinEq i (internal i ri.1) b).2).trans (ri.2.2.2 b)⟩
    exact onBranch D (len.trans_le sz) dao dnd deq j i ne.symm
      (fun x => ji ((coneEq _ _).mp x)) (fun x => ij ((coneEq _ _).mp x)) flippedJ flippedI
      ((gateEq j).2.2.trans h.2.1)
