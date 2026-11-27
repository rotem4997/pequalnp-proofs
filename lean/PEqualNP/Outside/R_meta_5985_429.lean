import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_5985_429
  (forced : let G := edgeGraph 26 ((List.range 12).flatMap fun p => (List.range 12).filterMap fun l =>
      if (p + 13 - l) % 13 ∈ [0,1,3,9] then some (p+1,l+14) else none);
    ∀ C : Circuit, Monotone2 C → C.size ≤ 55 → circuitFun 26 C = graphFun G ∅ →
      ∃ j, IsDirtyAnd 26 G C j ∧ ∃ a b c d : Fin 26,
        G.Adj a b ∧ G.Adj c d ∧ a < b ∧ c < d ∧ (a,b) ≠ (c,d) ∧
        gateVal 26 C j (pairInput a b) = true ∧ gateVal 26 C j (pairInput c d) = true)
  (ruled : let G := edgeGraph 26 ((List.range 12).flatMap fun p => (List.range 12).filterMap fun l =>
      if (p + 13 - l) % 13 ∈ [0,1,3,9] then some (p+1,l+14) else none);
    ∀ C : Circuit, IsMinimalMonoCircuit 26 C → C.size ≤ 55 →
      circuitFun 26 C = graphFun G ∅ →
      (∃ j, IsDirtyAnd 26 G C j ∧ ∃ a b c d : Fin 26,
        G.Adj a b ∧ G.Adj c d ∧ a < b ∧ c < d ∧ (a,b) ≠ (c,d) ∧
        gateVal 26 C j (pairInput a b) = true ∧ gateVal 26 C j (pairInput c d) = true) → False) :
  (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 (0 : Fin (26 : ℕ)) = Bool.false → x4 (13 : Fin (26 : ℕ)) = Bool.false → (x2.eval (List.ofFn x4) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x4 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x8) = Bool.true)) → (56 : ℕ) ≤ x2.size) := by
  intro I C mono spec
  by_contra! below
  let G := edgeGraph 26 ((List.range 12).flatMap fun p => (List.range 12).filterMap fun l =>
      if (p + 13 - l) % 13 ∈ [0,1,3,9] then some (p+1,l+14) else none)
  have square : ∀ p l : Fin 13, G.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) ↔
        p ≠ 0 ∧ l ≠ 0 ∧ I p l := by
      decide +kernel
  
  have noLeft : ∀ p q : Fin 13, ¬ G.Adj (Fin.castAdd 13 p) (Fin.castAdd 13 q) := by
    decide +kernel
  have noRight : ∀ p q : Fin 13, ¬ G.Adj (Fin.natAdd 13 p) (Fin.natAdd 13 q) := by
    decide +kernel
  
  have endpoints {u v : Fin 26} (e : G.Adj u v) :
      ∃ p l : Fin 13, p ≠ 0 ∧ l ≠ 0 ∧ I p l ∧
        ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
         (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p)) := by
    revert e
    refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) u <;>
      refine Fin.addCases (m := 13) (n := 13) (fun p' => ?_) (fun l' => ?_) v <;> intro e
    · exact False.elim (noLeft p p' e)
    · obtain ⟨hnp,hnl,h⟩ := (square p l').mp e
      exact ⟨p,l',hnp,hnl,h,Or.inl ⟨rfl,rfl⟩⟩
    · obtain ⟨hnp,hnl,h⟩ := (square p' l).mp e.symm
      exact ⟨p',l,hnp,hnl,h,Or.inr ⟨rfl,rfl⟩⟩
    · exact False.elim (noRight l l' e)
  have leftNotPinned {p : Fin 13} (hnp : p ≠ 0) :
      ¬ (Fin.castAdd 13 p = 0 ∨ Fin.castAdd 13 p = 13) := by
    rintro (he | he)
    · apply hnp
      apply Fin.ext
      have h := congrArg Fin.val he
      exact h
    · have h := congrArg Fin.val he
      have := p.isLt
      simp only [Fin.val_castAdd] at h
      change p.val = 13 at h
      omega
  have rightNotPinned {l : Fin 13} (hnl : l ≠ 0) :
      ¬ (Fin.natAdd 13 l = 0 ∨ Fin.natAdd 13 l = 13) := by
    rintro (he | he)
    · have h := congrArg Fin.val he
      simp only [Fin.val_natAdd] at h
      change 13 + l.val = 0 at h
      omega
    · apply hnl
      apply Fin.ext
      have h := congrArg Fin.val he
      simp only [Fin.val_natAdd] at h
      change 13 + l.val = 13 at h
      change l.val = 0
      omega
  let pinInput (x : Fin 26 → Bool) (i : Fin 26) : Bool :=
    if i = 0 ∨ i = 13 then false else x i
  let endWire := 26 + C.size
  let redirect (w : ℕ) := if w = 0 ∨ w = 13 then endWire else w
  let rg (g : Gate) : Gate := ⟨g.op, g.inputs.map redirect⟩
  let D : Circuit := ⟨C.gates.map rg, redirect C.output⟩
  have sizeD : D.size = C.size := by
    change (C.gates.map rg).length = C.gates.length
    simp only [List.length_map]
  have monoD : Monotone2 D := by
    intro g hg
    obtain ⟨g',mem,rfl⟩ := List.mem_map.mp hg
    simpa [rg] using mono g' mem
  have transfer (x : Fin 26 → Bool) :
      D.eval (List.ofFn x) = C.eval (List.ofFn (pinInput x)) := by
    let newIn := List.ofFn x
    let oldIn := List.ofFn (pinInput x)
    have oldLength : oldIn.length = 26 := by simp [oldIn]
    have newLength : newIn.length = 26 := by simp [newIn]
    have wire (t : List Bool) (h : t.length ≤ C.size) (w : ℕ) :
        (newIn ++ t).getD (redirect w) false = (oldIn ++ t).getD w false := by
      by_cases hp : w = 0 ∨ w = 13
      · have out : (newIn ++ t).length ≤ endWire := by
          simp only [List.length_append, newLength, endWire]
          omega
        rw [show redirect w = endWire by simp [redirect,hp]]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none out]
        have inside : w < oldIn.length := by rw [oldLength]; rcases hp with rfl | rfl <;> decide
        rw [List.getD_append _ _ _ _ inside]
        rcases hp with rfl | rfl <;> simp [oldIn,pinInput,List.getD_eq_getElem?_getD]
      · rw [show redirect w = w by simp [redirect,hp]]
        by_cases before : w < 26
        · rw [List.getD_append _ _ _ _ (by rwa [newLength]),
            List.getD_append _ _ _ _ (by rwa [oldLength])]
          simp only [newIn,oldIn,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem
            (show w < (List.ofFn x).length by simpa using before),
            List.getElem?_eq_getElem (show w < (List.ofFn (pinInput x)).length by simpa using before),
            Option.getD_some,
            List.getElem_ofFn]
          have hnot : ¬ ((⟨w,before⟩ : Fin 26) = 0 ∨ (⟨w,before⟩ : Fin 26) = 13) := by
            rintro (h | h)
            · exact hp (Or.inl (congrArg Fin.val h))
            · exact hp (Or.inr (congrArg Fin.val h))
          exact (ite_eq_right hnot).symm
        · rw [List.getD_append_right _ _ _ _ (by rw [newLength]; omega),
            List.getD_append_right _ _ _ _ (by rw [oldLength]; omega),newLength,oldLength]
    let step (acc : List Bool) (g : Gate) := acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]
    have run (gs : List Gate) (t : List Bool) (bound : t.length + gs.length ≤ C.size) : ∃ u,
        u.length = t.length + gs.length ∧
        gs.foldl step (oldIn ++ t) = oldIn ++ u ∧
        (gs.map rg).foldl step (newIn ++ t) = newIn ++ u := by
      induction gs generalizing t with
      | nil => exact ⟨t,by simp,rfl,rfl⟩
      | cons g gs ih =>
        let z := g.op.eval (g.inputs.map fun i => (oldIn ++ t).getD i false)
        have gate : (rg g).op.eval ((rg g).inputs.map fun i => (newIn ++ t).getD i false) = z := by
          unfold rg z
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact wire t (by omega) i
        obtain ⟨u,ul,ho,hn⟩ := ih (t ++ [z]) (by simp at bound ⊢; omega)
        refine ⟨u,by simp at ul ⊢; omega,?_,?_⟩
        · simpa only [List.foldl_cons,step,List.append_assoc,z] using ho
        · simpa only [List.map_cons,List.foldl_cons,step,gate,List.append_assoc] using hn
    obtain ⟨u,ul,ho,hn⟩ := run C.gates [] (by
      change 0 + C.gates.length ≤ C.gates.length
      rw [Nat.zero_add])
    simp only [List.append_nil] at ho hn
    change ((C.gates.map rg).foldl step newIn).getD (redirect C.output) false =
      (C.gates.foldl step oldIn).getD C.output false
    rw [ho,hn]
    exact wire u (by
      change u.length ≤ C.gates.length
      simpa only [List.length_nil,Nat.zero_add] using ul.le) C.output
  have computesD : circuitFun 26 D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change D.eval (List.ofFn x) = true ↔ graphFun G ∅ x = true
    rw [transfer]
    have left : pinInput x 0 = false := by simp [pinInput]
    have right : pinInput x 13 = false := by simp [pinInput]
    rw [spec _ left right]
    change _ ↔ (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Finset.notMem_empty,false_and,exists_false,decide_false,
      Bool.false_or,decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,h,hp,hl⟩
      have pn : p ≠ 0 := by rintro rfl; simp [pinInput] at hp
      have ln : l ≠ 0 := by rintro rfl; simp [pinInput] at hl
      exact ⟨_,_,(square p l).2 ⟨pn,ln,h⟩,by simpa only [pinInput,ite_eq_right (leftNotPinned pn)] using hp,
        by simpa only [pinInput,ite_eq_right (rightNotPinned ln)] using hl⟩
    · rintro ⟨u,v,e,hu,hv⟩
      obtain ⟨p,l,pn,ln,edge,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := endpoints e
      · exact ⟨p,l,edge,by simpa only [pinInput,ite_eq_right (leftNotPinned pn)] using hu,
          by simpa only [pinInput,ite_eq_right (rightNotPinned ln)] using hv⟩
      · exact ⟨p,l,edge,by simpa only [pinInput,ite_eq_right (leftNotPinned pn)] using hv,
          by simpa only [pinInput,ite_eq_right (rightNotPinned ln)] using hu⟩
  classical
  let P (k : ℕ) := ∃ E : Circuit, Monotone2 E ∧ circuitFun 26 E = graphFun G ∅ ∧ E.size = k
  have eP : ∃ k, P k := ⟨D.size,D,monoD,computesD,rfl⟩
  obtain ⟨E,monoE,computesE,minimalSize⟩ := Nat.find_spec eP
  have minimal : IsMinimalMonoCircuit 26 E := by
    refine ⟨monoE,?_⟩
    intro E' monoE' eq
    rw [minimalSize]
    exact Nat.find_min' eP ⟨E',monoE',eq.trans computesE,rfl⟩
  have sizeE := minimal.2 D monoD (computesD.trans computesE.symm)
  have smallE : E.size ≤ 55 := by omega
  exact ruled E minimal smallE computesE (forced E monoE smallE computesE)
