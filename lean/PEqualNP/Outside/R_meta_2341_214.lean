import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Rotate the omitted flag to zero. Each column records a wire on 285 tests.
-- A new column requires incomparable operands and a previously unseen result.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 20000 in
theorem PEqualNP.Outside.R_meta_2341_214
    (lastAnd :
      let codes : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
      let src := (List.range 26).map (fun v => ((List.finRange 285).filter (fun i =>
        (codes.getD ((i.val+1)/13) 0).testBit (v/13*13+(v+13-(i.val+1)%13)%13))).toFinset)
      ∀ t : List (Finset (Fin 285)), t.length≤61 →
      (∀ i : Fin t.length, let pool := src ++ t.take i.val
        ∃ u ∈ pool, ∃ v ∈ pool, ¬u⊆v ∧ ¬v⊆u ∧ t.get i ∉ pool ∧
          (t.get i=u∩v ∨ t.get i=u∪v)) →
      ∀ u ∈ src++t, ∀ v ∈ src++t, ¬u⊆v → ¬v⊆u →
        u∩v ≠ ((List.finRange 285).filter (fun i => decide (i.val<51))).toFinset)
    (lastOr :
      let codes : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
      let src := (List.range 26).map (fun v => ((List.finRange 285).filter (fun i =>
        (codes.getD ((i.val+1)/13) 0).testBit (v/13*13+(v+13-(i.val+1)%13)%13))).toFinset)
      ∀ t : List (Finset (Fin 285)), t.length≤61 →
      (∀ i : Fin t.length, let pool := src ++ t.take i.val
        ∃ u ∈ pool, ∃ v ∈ pool, ¬u⊆v ∧ ¬v⊆u ∧ t.get i ∉ pool ∧
          (t.get i=u∩v ∨ t.get i=u∪v)) →
      ∀ u ∈ src++t, ∀ v ∈ src++t, ¬u⊆v → ¬v⊆u →
        u∪v ≠ ((List.finRange 285).filter (fun i => decide (i.val<51))).toFinset)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  let E (p l : Fin 13) := p-l ∈ ({0,1,3,9} : Finset (Fin 13))
  let codes : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
  let raw (i : Fin 285) (v : ℕ) :=
    (codes.getD ((i.val+1)/13) 0).testBit (v/13*13 + (v+13-(i.val+1)%13)%13)
  let column (v : ℕ) := ((List.finRange 285).filter (fun i => raw i v)).toFinset
  let src := (List.range 26).map column
  let goal := ((List.finRange 285).filter (fun i => decide (i.val < 51))).toFinset
  have goalMem (i : Fin 285) : i∈goal ↔ i.val<51 := by simp [goal]
  have colMem (i : Fin 285) (v : ℕ) : i∈column v ↔ raw i v=true := by simp [column]
  let Q (r : Fin 285) := Finset.univ.filter fun p : Fin 13 => raw r p.val
  let quad (S : Finset (Fin 13)) := S.card=4 ∧ ∀ l : Fin 13, (S.filter fun p => E p l).card ≤ 2
  have posRows : ∀ r : Fin 285, r.val<51 →
      ∃ p l : Fin 13, E p l ∧ (p≠0 ∨ l≠0) ∧
        (∀ u : Fin 13, raw r u.val = decide (u=p)) ∧
        ∀ v : Fin 13, raw r (13+v.val) = decide (v=l) := by
    dsimp only [E,raw,codes]
    decide +kernel
  have negRows : ∀ r : Fin 285, 51 ≤ r.val → quad (Q r) ∧
      ∀ l : Fin 13, raw r (13+l.val) = decide (∀ p ∈ Q r, ¬ E p l) := by
    dsimp only [quad,Q,E,raw,codes]
    decide +kernel
  let pg : Fin 13 → Fin 13 → Fin 13 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 2, 10, 8, 1, 3, 5, 9, 11, 12, 4, 7, 6],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 2, 4, 8, 10, 11, 3, 6, 5, 12, 1, 9, 7],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 2, 1, 8, 4, 5, 11, 7, 3, 12, 10, 6, 9]]
  let lg : Fin 13 → Fin 13 → Fin 13 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![12, 1, 7, 5, 0, 2, 9, 8, 11, 3, 4, 6, 10],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![12, 1, 8, 7, 10, 2, 3, 5, 9, 11, 0, 6, 4],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
      ![12, 1, 5, 8, 4, 2, 11, 7, 3, 9, 10, 6, 0]]
  have table : ∀ t : Fin 13, E 0 t →
      Function.Injective (pg t) ∧ Function.Injective (lg t) ∧ pg t 0=0 ∧ lg t t=0 ∧
      ∀ p l, E (pg t p) (lg t l) ↔ E p l := by
    dsimp only [Function.Injective,E,pg,lg]
    decide +kernel
  have iso (m n : Fin 13) (h : E m n) : ∃ f g : Fin 13 ≃ Fin 13, f m=0 ∧ g n=0 ∧
      ∀ p l, E (f p) (g l) ↔ E p l := by
    have shift (p l : Fin 13) : E (p-m) (l-m) ↔ E p l := by simp [E]
    have on : E 0 (n-m) := by simpa using (shift m n).mpr h
    obtain ⟨pi,li,p0,l0,good⟩ := table (n-m) on
    let f := (pg (n-m)) ∘ (fun x : Fin 13 => x-m)
    let g := (lg (n-m)) ∘ (fun x : Fin 13 => x-m)
    have inj : Function.Injective (fun x : Fin 13 => x-m) := fun _ _ h => sub_left_inj.mp h
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp (pi.comp inj)),
      Equiv.ofBijective g (Finite.injective_iff_bijective.mp (li.comp inj)),?_,l0,?_⟩
    · change pg (n-m) (m-m)=0; simpa using p0
    · exact fun p l => (good _ _).trans (shift p l)
  let join (t : List (Finset (Fin 285))) (z : (Finset (Fin 285))) := ∃ u ∈ src++t, ∃ v ∈ src++t,
    ¬u⊆v ∧ ¬v⊆u ∧ z ∉ src++t ∧ (z = u∩v ∨ z = u∪v)
  let valid (t : List (Finset (Fin 285))) := ∀ i : Fin t.length, join (t.take i.val) t[i.val]
  let live (t : List (Finset (Fin 285))) (z : (Finset (Fin 285))) := z=∅ ∨ z=Finset.univ ∨ z ∈ src++t
  let project (r : Fin 285) (W : List (Finset (Fin 285))) := W.map fun z => decide (r∈z)
  let value (g : Gate) (W : List (Finset (Fin 285))) : (Finset (Fin 285)) :=
    Finset.univ.filter fun r => g.op.eval (g.inputs.map fun i => decide (r ∈ W.getD i ∅))
  let cs (W : List (Finset (Fin 285))) (g : Gate) := W ++ [value g W]
  let bs (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]
  have lookup (r : Fin 285) (W : List (Finset (Fin 285))) (i : ℕ) :
      (project r W).getD i false = decide (r ∈ W.getD i ∅) := by
    simp only [project,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases W[i]? <;> simp
  have commute (r : Fin 285) (gs : List Gate) (W : List (Finset (Fin 285))) :
      project r (gs.foldl cs W) = gs.foldl bs (project r W) := by
    induction gs generalizing W with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,List.foldl_cons,ih]
      apply congrArg (gs.foldl bs)
      have eq : decide (r ∈ value g W) = g.op.eval (g.inputs.map fun i => (project r W).getD i false) := by
        simp only [value,Finset.mem_filter,Finset.mem_univ,true_and,Bool.decide_coe,lookup]
      exact List.map_append.trans (congrArg (fun b => project r W ++ [b]) eq)
  have appendOK (t : List (Finset (Fin 285))) (ok : valid t) (z : (Finset (Fin 285))) (h : join t z) : valid (t++[z]) := by
    intro i
    by_cases lt : i.val<t.length
    · simpa only [List.take_append_of_le_length lt.le,List.getElem_append_left lt] using ok ⟨i.val,lt⟩
    · have eq : i.val=t.length := by have := i.isLt; simp at this; omega
      have atEnd : (t++[z])[i.val] = z := by
        rw [List.getElem_append_right (by omega)]
        simp [eq]
      rw [atEnd,List.take_left' eq.symm]
      exact h
  have readLive (t W : List (Finset (Fin 285))) (old : ∀ z∈W, live t z) (i : ℕ) : live t (W.getD i ∅) := by
    by_cases hi : i<W.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact old _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact Or.inl rfl
  have combine (t : List (Finset (Fin 285))) (ok : valid t) (u v z : (Finset (Fin 285)))
      (lu : live t u) (lv : live t v) (eq : z=u∩v ∨ z=u∪v) :
      ∃ t' : List (Finset (Fin 285)), valid t' ∧ t'.length ≤ t.length+1 ∧
        (∀ w, live t w → live t' w) ∧ live t' z := by
    by_cases done : live t z
    · exact ⟨t,ok,by omega,fun _ h => h,done⟩
    · have incomp : ¬u⊆v ∧ ¬v⊆u := by
        constructor
        · intro le; apply done
          rcases eq with rfl | rfl
          · simpa only [Finset.inter_eq_left.mpr le] using lu
          · simpa only [Finset.union_eq_right.mpr le] using lv
        · intro le; apply done
          rcases eq with rfl | rfl
          · simpa only [Finset.inter_eq_right.mpr le] using lv
          · simpa only [Finset.union_eq_left.mpr le] using lu
      have um : u ∈ src++t := by
        rcases lu with rfl | rfl | h
        · exact False.elim (incomp.1 (Finset.empty_subset _))
        · exact False.elim (incomp.2 (Finset.subset_univ _))
        · exact h
      have vm : v ∈ src++t := by
        rcases lv with rfl | rfl | h
        · exact False.elim (incomp.2 (Finset.empty_subset _))
        · exact False.elim (incomp.1 (Finset.subset_univ _))
        · exact h
      refine ⟨t++[z],appendOK t ok z ⟨u,um,v,vm,incomp.1,incomp.2,fun h => done (Or.inr (Or.inr h)),eq⟩,by simp,?_,?_⟩
      · intro w hw
        rcases hw with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by rw [←List.append_assoc]; exact List.mem_append_left _ h))
      · exact Or.inr (Or.inr (by simp))
  have gateStep (g : Gate) (allowed : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (t W : List (Finset (Fin 285))) (ok : valid t) (old : ∀ z ∈ W, live t z) :
      ∃ t' : List (Finset (Fin 285)), valid t' ∧ t'.length ≤ t.length+1 ∧ ∀ z ∈ cs W g, live t' z := by
    have stay (h : live t (value g W)) : ∃ t' : List (Finset (Fin 285)), valid t' ∧ t'.length ≤ t.length+1 ∧
        ∀ z ∈ cs W g, live t' z := by
      refine ⟨t,ok,by omega,?_⟩
      intro z hz
      rcases List.mem_append.mp hz with a | a
      · exact old _ a
      · simpa only [List.mem_singleton.mp a] using h
    have ae (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have oe (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have op : g.op=.and ∨ g.op=.or := allowed.1
    cases h : g.inputs with
    | nil =>
      apply stay
      rcases op with e | e
      · exact Or.inr (Or.inl (by ext r; simp [value,h,e,ae]))
      · exact Or.inl (by ext r; simp [value,h,e,oe])
    | cons i ks =>
      cases hk : ks with
      | nil =>
        apply stay
        have eq : value g W = W.getD i ∅ := by
          rcases op with e | e <;> ext r <;> simp [value,h,hk,e,ae,oe]
        exact eq ▸ readLive t W old i
      | cons j rest =>
        have tail : rest=[] := by
          have m := allowed.2
          rw [h,hk] at m
          simpa using m
        have eq : value g W = W.getD i ∅ ∩ W.getD j ∅ ∨ value g W = W.getD i ∅ ∪ W.getD j ∅ := by
          rcases op with e|e
          · left; ext r; simp [value,h,hk,tail,e,ae]
          · right; ext r; simp [value,h,hk,tail,e,oe]
        obtain ⟨t',good,sz,inc,present⟩ := combine t ok _ _ _ (readLive t W old i) (readLive t W old j) eq
        refine ⟨t',good,sz,?_⟩
        intro z hz
        rcases List.mem_append.mp hz with a | a
        · exact inc _ (old _ a)
        · simpa only [List.mem_singleton.mp a] using present
  have extract (gs : List Gate)
      (hm : ∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (t W : List (Finset (Fin 285))) (ok : valid t) (old : ∀ z ∈ W, live t z) :
      ∃ T : List (Finset (Fin 285)), valid T ∧ T.length ≤ t.length+gs.length ∧ ∀ z ∈ gs.foldl cs W, live T z := by
    induction gs generalizing t W with
    | nil => exact ⟨t,ok,by simp,old⟩
    | cons g gs ih =>
      obtain ⟨q,hq,sq,new⟩ := gateStep g (hm g List.mem_cons_self) t W ok old
      obtain ⟨T,hT,sT,all⟩ := ih (fun g hg => hm g (List.mem_cons_of_mem _ hg)) q (cs W g) hq new
      exact ⟨T,hT,by simp only [List.length_cons]; omega,all⟩
  intro C m n c hm _ offsets pair negative quadr positives negatives
  let mark := if E m n then n else m
  have marked : E m mark := by
    dsimp only [mark]; split
    · assumption
    · simp [E]
  obtain ⟨f,g,root,line0,auto⟩ := iso m mark marked
  let W0 := (List.ofFn fun p : Fin 13 => column (f p).val) ++
    (List.ofFn fun l : Fin 13 => column (13+(g l).val)) ++ [if c then Finset.univ else ∅]
  have rawOutput (r : Fin 285) :
      C.eval (project r W0) = decide (r.val<51) := by
    let inp := List.ofFn (fun p : Fin 13 => raw r (f p).val) ++
      List.ofFn (fun l : Fin 13 => raw r (13+(g l).val))
    have start : project r W0 = inp ++ [c] := by
      cases c <;> simp [project,W0,inp,column]
    rw [start]
    by_cases pos : r.val<51
    · rw [decide_eq_true pos]
      obtain ⟨p,l,h,neq,ps,ls⟩ := posRows r pos
      have hp : E (f.symm p) (g.symm l) := (auto _ _).mp (by simpa using h)
      have notBoth : f.symm p ≠ m ∨ g.symm l ≠ n := by
        by_contra! bad
        obtain ⟨mp,nl⟩ := bad
        have on : E m n := mp ▸ nl ▸ hp
        have pz : p=0 := by simp only [← root,← mp,Equiv.apply_symm_apply]
        have markEq : mark=n := ite_eq_left on
        have lz : l=0 := (g.apply_symm_apply l).symm.trans ((congrArg g nl).trans ((congrArg g markEq.symm).trans line0))
        exact neq.elim (fun h => h pz) (fun h => h lz)
      have same : inp = pair (f.symm p) (g.symm l) := by
        dsimp only [inp,pair]
        apply congrArg₂ (fun x y : List Bool => x ++ y)
        · apply congrArg List.ofFn; funext t
          exact (ps (f t)).trans (decide_eq_decide.mpr f.eq_symm_apply.symm)
        · apply congrArg List.ofFn; funext t
          exact (ls (g t)).trans (decide_eq_decide.mpr g.eq_symm_apply.symm)
      rw [same]
      exact positives _ _ hp notBoth
    · rw [decide_eq_false pos]
      obtain ⟨shape,off⟩ := negRows r (by omega)
      let S := (Q r).map f.symm.toEmbedding
      have mem (p : Fin 13) : p ∈ S ↔ f p ∈ Q r := by
        simp only [S,Finset.mem_map_equiv,Equiv.symm_symm]
      have quadS : quadr S := by
        refine ⟨by simpa only [S,Finset.card_map] using shape.1,?_⟩
        intro l
        change (S.filter (fun p => E p l)).card ≤ 2
        have eq : (S.filter (fun p => E p l)).map f.toEmbedding =
            (Q r).filter (fun p => E p (g l)) := by
          ext p
          obtain ⟨p,rfl⟩ := f.surjective p
          simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply,Finset.mem_filter,mem,auto]
        have h := congrArg Finset.card eq
        simp only [Finset.card_map] at h
        exact h ▸ shape.2 (g l)
      have same : inp = negative S := by
        dsimp only [inp,negative]
        apply congrArg₂ (fun x y : List Bool => x ++ y)
        · apply congrArg List.ofFn; funext p
          have h : p∈S ↔ raw r (f p).val = true := (mem p).trans (by simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and])
          exact (Bool.decide_coe _).symm.trans (decide_eq_decide.mpr h).symm
        · apply congrArg List.ofFn; funext l
          rw [off (g l)]
          apply decide_eq_decide.mpr
          constructor
          · intro h p hp e
            exact h (f p) ((mem p).mp hp) ((auto p l).mpr e)
          · intro h p hp e
            obtain ⟨u,rfl⟩ := f.surjective p
            exact h u ((mem u).mpr hp) ((auto u l).mp e)
      rw [same]
      exact negatives S quadS
  have old (z : Finset (Fin 285)) (hz : z ∈ W0) : live [] z := by
    rcases List.mem_append.mp hz with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨p,rfl⟩ := List.mem_ofFn.mp h
        exact Or.inr (Or.inr (by simp only [src,List.append_nil,List.mem_map]; exact ⟨_,List.mem_range.mpr (by have := (f p).isLt; omega),rfl⟩))
      · obtain ⟨l,rfl⟩ := List.mem_ofFn.mp h
        exact Or.inr (Or.inr (by simp only [src,List.append_nil,List.mem_map]; exact ⟨_,List.mem_range.mpr (by have := (g l).isLt; omega),rfl⟩))
    · have e := List.mem_singleton.mp h
      rw [e]; cases c
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  obtain ⟨T,ok,num,all⟩ := extract C.gates hm [] W0 (fun i => Fin.elim0 i) old
  let last := (C.gates.foldl cs W0).getD C.output ∅
  have equal : last = goal := by
    ext r
    have ev := commute r C.gates W0
    have see := congrArg (fun v : List Bool => v.getD C.output false) ev
    rw [lookup] at see
    change decide (r ∈ last) = C.eval (project r W0) at see
    rw [rawOutput] at see
    simpa only [goalMem,decide_eq_decide] using see
  have found := readLive T (C.gates.foldl cs W0) all C.output
  change live T last at found
  rw [equal] at found
  have negativeUse : ∀ v : Fin 26, ∃ r : Fin 285, 51 ≤ r.val ∧ raw r v.val = true := by
    dsimp only [raw,codes]
    decide +kernel
  have unique : goal ≠ ∅ ∧ goal ≠ Finset.univ ∧ goal ∉ src := by
    have hot : (0 : Fin 285) ∈ goal := (goalMem 0).mpr (by decide)
    have cold : (51 : Fin 285) ∉ goal := fun h => (by decide : ¬(51 : Fin 285).val < 51) ((goalMem 51).mp h)
    refine ⟨fun e => Finset.notMem_empty _ (e ▸ hot),fun e => cold (e ▸ Finset.mem_univ _),?_⟩
    intro h
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp h
    obtain ⟨r,neg,pos⟩ := negativeUse ⟨v,List.mem_range.mp hv⟩
    have here : r ∈ column v := (colMem r v).mpr pos
    exact (Nat.not_lt_of_ge neg) ((goalMem r).mp (eq ▸ here))
  have has : goal ∈ T := by
    rcases found with h|h|h
    · exact False.elim (unique.1 h)
    · exact False.elim (unique.2.1 h)
    · exact (List.mem_append.mp h).resolve_left unique.2.2
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem has
  let t := T.take i
  have sub : valid t := by
    intro j
    have lt : j.val < i := Nat.lt_of_lt_of_le j.isLt (List.length_take_le _ _)
    have jT : j.val < T.length := lt.trans hi
    have h := ok ⟨j.val,jT⟩
    simpa only [t,List.take_take,Nat.min_eq_left lt.le,List.getElem_take] using h
  have step := ok ⟨i,hi⟩
  change join t T[i] at step
  rw [eq] at step
  obtain ⟨u,hu,v,hv,uv,vu,_,e⟩ := step
  by_contra! small
  have bound : t.length ≤ 61 := by
    have it : t.length ≤ i := List.length_take_le i T
    change T.length ≤ 0 + C.size at num
    omega
  rcases e with e | e
  · exact lastAnd t bound sub u hu v hv uv vu e.symm
  · exact lastOr t bound sub u hu v hv uv vu e.symm
