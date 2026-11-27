import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Identify nonisolated vertices with the same open neighborhood.
-- One new OR gate splits a representative back into two inputs, preserving ownership on pairs.
-- Fixing an essential input to zero gives the reverse inequality on circuit sizes.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_5375_52
    (restrictZero : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (z : Fin n), (∃ w, G.Adj z w) → ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
        circuitFun n D = graphFun (PEqualNP.Library.Peel.delVerts G {z}) ∅)
    (core : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      (∀ y z, (∃ w, G.Adj z w) → (∀ w, G.Adj y w ↔ G.Adj z w) → y=z) →
      let r (C : Circuit) (j : Nat) (a b : Fin n) := G.Adj a b ∧ Owns n C j a b
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j a b c d, r C j a b → r C j c d → r C j a c ∨ r C j a d ∨ r C j b c ∨ r C j b d) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ) (x9 x10 x11 x12 : Fin x1), x6 x7 x8 x9 x10 → x6 x7 x8 x11 x12 → x6 x7 x8 x9 x11 ∨ x6 x7 x8 x9 x12 ∨ x6 x7 x8 x10 x11 ∨ x6 x7 x8 x10 x12 := by
  let rename {n : Nat} (y z : Fin n) (m w : Nat) : Nat :=
    if w = z.val then n+m+1 else if w = y.val then n else if w < n then w else w+1

  let gate (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

  let lift {n : Nat} (C : Circuit) (y z : Fin n) : Circuit :=
    let f := rename y z C.size
    ⟨⟨.or,[y.val,z.val]⟩ :: C.gates.map (gate f), f C.output⟩

  let merge {n : Nat} (y z : Fin n) (x : Fin n → Bool) (i : Fin n) : Bool :=
    if i = z then false else if i = y then x y || x z else x i

  let proj {n : Nat} (y z i : Fin n) := if i = z then y else i

  have pair {n : Nat} (y z : Fin n) (ne : y ≠ z) (a b : Fin n) :
      merge y z (pairInput a b) = pairInput (proj y z a) (proj y z b) := by
    clear restrictZero core
    funext i
    have sample (p q t : Fin n) : pairInput p q t = decide (t=p ∨ t=q) := rfl
    simp only [merge,proj,sample]
    split_ifs <;> simp_all <;> grind

  have snocRead {α : Type} (l : List α) (v d : α) (i : Nat) :
      (l++[v]).getD i d = if i = l.length then v else l.getD i d := by
    induction l generalizing i with
    | nil => cases i <;> simp [List.getD_eq_getElem?_getD]
    | cons a l ih =>
      cases i with
      | zero => simp [List.getD_eq_getElem?_getD]
      | succ i => simpa only [List.cons_append,List.getD_cons_succ,List.length_cons,Nat.succ.injEq] using ih i

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have gateAddr {n : Nat} (y z : Fin n) (m k : Nat) : rename y z m (n+k) = n+k+1 := by
    have a := y.isLt
    have b := z.isLt
    simp [rename,show n+k ≠ z.val by omega,show n+k ≠ y.val by omega,show ¬ n+k<n by omega]

  have newSlot {n : Nat} (y z : Fin n) (m k w : Nat) (h : k < m) :
      rename y z m w = n+k+1 ↔ w = n+k := by
    have a := y.isLt
    have b := z.isLt
    simp only [rename]
    split_ifs <;> omega

  have wiresAux {n : Nat} (y z : Fin n) (m : Nat) (x : Fin n → Bool) (gs : List Gate)
      (lim : gs.length ≤ m) :
      let base := List.ofFn (merge y z x)
      let ext := List.ofFn x ++ [x y || x z]
      let old := gs.foldl step base
      let new := (gs.map (gate (rename y z m))).foldl step ext
      old.length = n+gs.length ∧ new.length = n+gs.length+1 ∧
      ∀ i, new.getD (rename y z m i) false = old.getD i false := by
    induction gs using List.reverseRecOn with
    | nil =>
      simp only [List.map_nil,List.foldl_nil,List.length_ofFn,List.length_append,List.length_singleton,
        List.length_nil,Nat.add_zero,true_and]
      intro i
      rw [snocRead,List.length_ofFn]
      by_cases iz : i = z.val
      · subst i
        simp [rename,merge,List.getD_eq_getElem?_getD,z.isLt,show ¬n+m+1<n by omega,
          show n+m+1 ≠ n by omega]
      by_cases iy : i = y.val
      · subst i
        have ne : y ≠ z := fun eq => iz (congrArg Fin.val eq)
        simp [rename,iz,merge,ne,List.getD_eq_getElem?_getD,y.isLt]
      by_cases hi : i < n
      · have nz : (⟨i,hi⟩ : Fin n) ≠ z := fun eq => iz (congrArg Fin.val eq)
        have ny : (⟨i,hi⟩ : Fin n) ≠ y := fun eq => iy (congrArg Fin.val eq)
        simp [rename,iz,iy,hi,merge,nz,ny,List.getD_eq_getElem?_getD,hi.ne]
      · simp [rename,iz,iy,hi,List.getD_eq_getElem?_getD,show i+1 ≠ n by omega,show ¬i+1<n by omega]
    | append_singleton gs g ih =>
      have small : gs.length < m := by simpa using lim
      obtain ⟨oldLen,newLen,look⟩ := ih (by omega)
      simp only [List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil,
        List.length_append,List.length_singleton]
      have grow (ws : List Bool) (q : Gate) : (step ws q).length = ws.length+1 := by
        simp only [step,List.length_append,List.length_singleton]
      constructor
      · rw [grow,oldLen]; omega
      constructor
      · rw [grow,newLen]; omega
      intro w
      have same := List.map_congr_left (l := g.inputs) fun i _ => look i
      simp only [step,gate,List.map_map,Function.comp_def,snocRead,oldLen,newLen,newSlot y z m gs.length w small]
      split
      · exact congrArg g.op.eval same
      · exact look w

  have wires {n : Nat} (C : Circuit) (y z : Fin n) (x : Fin n → Bool) (i : Nat) :
      ((lift C y z).wires (List.ofFn x)).getD (rename y z C.size i) false =
        (C.wires (List.ofFn (merge y z x))).getD i false := by
    have first : step (List.ofFn x) ⟨.or,[y.val,z.val]⟩ = List.ofFn x ++ [x y || x z] := by
      have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
      simp [step,evalOr,List.getD_eq_getElem?_getD,y.isLt,z.isLt]
    change ((C.gates.map (gate (rename y z C.size))).foldl step (step (List.ofFn x) ⟨.or,[y.val,z.val]⟩)).getD _ _ = _
    rw [first]
    exact (wiresAux y z C.size x C.gates le_rfl).2.2 i

  have computes {n : Nat} (C : Circuit) (y z : Fin n) (x : Fin n → Bool) :
      circuitFun n (lift C y z) x = circuitFun n C (merge y z x) := wires C y z x C.output

  have costs {n : Nat} (C : Circuit) (y z : Fin n) (model : Monotone2 C) :
      Monotone2 (lift C y z) ∧ (lift C y z).size = C.size+1 := by
    constructor
    · intro g hg
      change g ∈ _ :: _ at hg
      rcases List.mem_cons.mp hg with rfl | hin
      · exact ⟨Or.inr rfl, le_rfl⟩
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hin
        exact ⟨(model a ha).1, by simpa [gate] using (model a ha).2⟩
    · change (_ :: C.gates.map (gate (rename y z C.size))).length = C.gates.length+1
      simp

  let entry (n : Nat) (cs : List (List Nat)) (g : Gate) : List Nat :=
    (g.inputs.filter fun w => decide (n ≤ w ∧ w < n+cs.length)).flatMap
      (fun w => (w-n) :: cs.getD (w-n) [])

  have entry_mem (n i : Nat) (cs : List (List Nat)) (g : Gate) :
      i ∈ entry n cs g ↔ ∃ w ∈ g.inputs, n ≤ w ∧ w < n+cs.length ∧
          (i = w-n ∨ i ∈ cs.getD (w-n) []) := by
    simp only [entry,List.mem_flatMap,List.mem_filter,decide_eq_true_eq,List.mem_cons]
    constructor
    · rintro ⟨w,⟨hw,lo,hi⟩,rest⟩
      exact ⟨w,hw,lo,hi,rest⟩
    · rintro ⟨w,hw,lo,hi,rest⟩
      exact ⟨w,⟨hw,lo,hi⟩,rest⟩

  have coneAux {n : Nat} (y z : Fin n) (m : Nat) (gs : List Gate) (lim : gs.length ≤ m) :
      let old := gs.foldl (coneStep n) []
      let new := (gs.map (gate (rename y z m))).foldl (coneStep n) [[]]
      old.length = gs.length ∧ new.length = gs.length+1 ∧ new.getD 0 [] = [] ∧
      ∀ i j, i+1 ∈ new.getD (j+1) [] ↔ i ∈ old.getD j [] := by
    induction gs using List.reverseRecOn with
    | nil => simp [List.getD_eq_getElem?_getD]
    | append_singleton gs g ih =>
      have small : gs.length < m := by simpa using lim
      obtain ⟨ol,nl,root,mem⟩ := ih (by omega)
      let old := gs.foldl (coneStep n) []
      let new := (gs.map (gate (rename y z m))).foldl (coneStep n) [[]]
      change old.length = gs.length at ol
      change new.length = gs.length+1 at nl
      change new.getD 0 [] = [] at root
      change ∀ i j, i+1 ∈ new.getD (j+1) [] ↔ i ∈ old.getD j [] at mem
      have pin (i w : Nat) :
          (n ≤ rename y z m w ∧ rename y z m w < n+new.length ∧
            (i+1 = rename y z m w-n ∨ i+1 ∈ new.getD (rename y z m w-n) [])) ↔
          (n ≤ w ∧ w < n+old.length ∧ (i = w-n ∨ i ∈ old.getD (w-n) [])) := by
        by_cases low : w < n
        · have h : ¬n ≤ w := by omega
          simp only [h,false_and,iff_false]
          by_cases wz : w = z.val
          · simp only [rename,if_pos wz,nl]
            omega
          by_cases wy : w = y.val
          · simp only [rename,ite_eq_right wz,ite_eq_left wy,Nat.sub_self,root]
            simp
          · simp [rename,wz,wy,low,h]
        · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
          have eq : n+k+1-n = k+1 := by omega
          have hi : n+k+1 < n+(gs.length+1) ↔ n+k<n+gs.length := by omega
          simp only [gateAddr,ol,nl,eq,Nat.add_sub_cancel_left,mem,Nat.add_right_cancel_iff,hi,
            show n ≤ n+k+1 by omega,show n ≤ n+k by omega]
      have eq (i : Nat) : i+1 ∈ entry n new (gate (rename y z m) g) ↔ i ∈ entry n old g := by
        rw [entry_mem,entry_mem]
        constructor
        · rintro ⟨r,hr,rest⟩
          obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
          exact ⟨w,hw,(pin i w).mp rest⟩
        · rintro ⟨w,hw,rest⟩
          exact ⟨_,List.mem_map.mpr ⟨w,hw,rfl⟩,(pin i w).mpr rest⟩
      simp only [List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil,
        List.length_append,List.length_singleton]
      change (old++[entry n old g]).length = _ ∧ (new++[entry n new _]).length = _ ∧
        (new++[entry n new _]).getD 0 [] = [] ∧ ∀ i j, _ ↔ _
      refine ⟨by simp [ol],by simp [nl],?_,?_⟩
      · rw [snocRead,if_neg (by omega),root]
      · intro i j
        change i+1 ∈ (new++[entry n new _]).getD (j+1) [] ↔ i ∈ (old++[entry n old g]).getD j []
        rw [snocRead,snocRead,nl,ol]
        by_cases endAt : j = gs.length
        · simpa only [endAt,if_true] using eq i
        · simpa only [Nat.add_right_cancel_iff,endAt,if_false] using mem i j

  have cone {n : Nat} (C : Circuit) (y z : Fin n) (i j : Nat) :
      InCone n (lift C y z) (i+1) (j+1) ↔ InCone n C i j := by
    have first : coneStep n [] ⟨.or,[y.val,z.val]⟩ = [[]] := by
      change [] ++ [entry n [] ⟨.or,[y.val,z.val]⟩] = [[]]
      simp [entry,show ¬n ≤ y.val by omega,show ¬n ≤ z.val by omega]
    change _ ∈ ((C.gates.map (gate (rename y z C.size))).foldl (coneStep n) (coneStep n [] ⟨.or,[y.val,z.val]⟩)).getD _ [] ↔ _
    rw [first]
    exact (coneAux y z C.size C.gates le_rfl).2.2.2 i j

  have owner {n : Nat} (C : Circuit) (y z : Fin n) (ne : y ≠ z) (j : Nat) (a b : Fin n) :
      Owns n (lift C y z) (j+1) a b ↔ Owns n C j (proj y z a) (proj y z b) := by
    have op (i : Nat) (hi : i < C.size) : (gateAt (lift C y z) (i+1)).op = (gateAt C i).op := by
      change (((_ :: C.gates.map (gate (rename y z C.size))).getD (i+1) _ : Gate).op) = _
      rw [List.getD_cons_succ]
      have gateDef (K : Circuit) (k : Nat) : gateAt K k = K.gates.getD k ⟨.or,[]⟩ := rfl
      simp [gateDef,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show i<C.gates.length from hi),hi,gate]
    have val (i : Nat) : gateVal n (lift C y z) (i+1) (pairInput a b) =
        gateVal n C i (pairInput (proj y z a) (proj y z b)) := by
      have ev := wires C y z (pairInput a b) (n+i)
      rw [gateAddr,pair y z ne] at ev
      exact ev
    have len : (lift C y z).gates.length = C.gates.length+1 := by simp [lift]
    constructor
    · rintro ⟨hj,kind,pos,earlier⟩
      have jl : j < C.size := by change j<C.gates.length; omega
      refine ⟨jl,(op j jl).symm.trans kind,(val j).symm.trans pos,?_⟩
      intro i ij anc kind'
      have good := earlier (i+1) (by omega) ((cone C y z i j).mpr anc) ((op i (by omega)).trans kind')
      exact (val i).symm.trans good
    · rintro ⟨hj,kind,pos,earlier⟩
      refine ⟨by omega,(op j hj).trans kind,(val j).trans pos,?_⟩
      intro k kj anc opk
      cases k with
      | zero => change GateOp.or = GateOp.and at opk; cases opk
      | succ i =>
        exact (val i).trans (earlier i (by omega) ((cone C y z i j).mp anc)
          ((op i (by change i<C.gates.length; omega)).symm.trans opk))

  let erased {n : Nat} (G : SimpleGraph (Fin n)) (z : Fin n) := PEqualNP.Library.Peel.delVerts G {z}

  have erasedAdj {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z a b : Fin n) : (erased G z).Adj a b ↔ G.Adj a b ∧ a≠z ∧ b≠z := by
    change (G.Adj a b ∧ a ∉ ({z} : Finset _) ∧ b ∉ ({z} : Finset _)) ↔ _
    simp only [Finset.mem_singleton]

  have projected {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y z : Fin n) (ne : y ≠ z) (tw : ∀ t, G.Adj y t ↔ G.Adj z t) (a b : Fin n) :
      (erased G z).Adj (proj y z a) (proj y z b) ↔ G.Adj a b := by
    have yz : ¬G.Adj y z := fun e => G.irrefl ((tw z).mp e)
    have tw' (t : Fin n) : G.Adj t y ↔ G.Adj t z := by
      simpa only [G.adj_comm t y,G.adj_comm t z] using tw t
    rw [erasedAdj]
    by_cases az : a=z <;> by_cases bz : b=z
    · subst a; subst b; simp [proj,ne]
    · subst a; simp [proj,bz,ne,tw]
    · subst b; simp [proj,az,ne,tw']
    · simp [proj,az,bz]

  have fiber {n : Nat} (y z : Fin n) (ne : y≠z) (x : Fin n → Bool) (u : Fin n) :
      merge y z x u = true ↔ ∃ i, proj y z i = u ∧ x i = true := by
    by_cases uz : u=z
    · subst u
      simp only [merge,ite_true,Bool.false_eq_true,false_iff,not_exists]
      intro i
      by_cases iz : i=z <;> simp [proj,iz,ne]
    by_cases uy : u=y
    · subst u
      simp only [merge,ite_eq_right uz,ite_true,Bool.or_eq_true]
      constructor
      · rintro (h|h)
        · exact ⟨y,by simp [proj,ne],h⟩
        · exact ⟨z,by simp [proj],h⟩
      · rintro ⟨i,eq,hi⟩
        by_cases iz : i=z
        · exact Or.inr (iz ▸ hi)
        · simp only [proj,ite_eq_right iz] at eq
          exact Or.inl (eq ▸ hi)
    · simp only [merge,ite_eq_right uz,ite_eq_right uy]
      constructor
      · exact fun hit => ⟨u,by simp [proj,uz],hit⟩
      · rintro ⟨i,eq,hi⟩
        by_cases iz : i=z
        · simp [proj,iz,Ne.symm uy] at eq
        · simp only [proj,ite_eq_right iz] at eq
          exact eq ▸ hi

  have graphTrue {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : graphFun G ∅ x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = true ↔ _
    simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]

  have liftFunction {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y z : Fin n) (ne : y≠z) (tw : ∀ t, G.Adj y t ↔ G.Adj z t) (x : Fin n → Bool) :
      graphFun (erased G z) ∅ (merge y z x) = graphFun G ∅ x := by
    apply Bool.eq_iff_iff.mpr
    rw [graphTrue,graphTrue]
    constructor
    · rintro ⟨u,v,h,hu,hv⟩
      obtain ⟨a,rfl,ha⟩ := (fiber y z ne x u).mp hu
      obtain ⟨b,rfl,hb⟩ := (fiber y z ne x v).mp hv
      exact ⟨a,b,(projected G y z ne tw a b).mp h,ha,hb⟩
    · rintro ⟨a,b,h,ha,hb⟩
      exact ⟨_,_,(projected G y z ne tw a b).mpr h,(fiber y z ne x _).mpr ⟨a,rfl,ha⟩,
        (fiber y z ne x _).mpr ⟨b,rfl,hb⟩⟩

  have crossLift {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y z : Fin n) (ne : y≠z) (tw : ∀ t, G.Adj y t ↔ G.Adj z t)
      (A : Circuit) (M : Monotone2 A) (funA : circuitFun n A = graphFun (erased G z) ∅)
      (ok : let r := fun j a b => (erased G z).Adj a b ∧ Owns n A j a b
            ∀ j a b c d, r j a b → r j c d → r j a c ∨ r j a d ∨ r j b c ∨ r j b d) :
      ∃ D : Circuit, Monotone2 D ∧ D.size = A.size+1 ∧ circuitFun n D = graphFun G ∅ ∧
        let r := fun j a b => G.Adj a b ∧ Owns n D j a b
        ∀ j a b c d, r j a b → r j c d → r j a c ∨ r j a d ∨ r j b c ∨ r j b d := by
    refine ⟨lift A y z,(costs A y z M).1,(costs A y z M).2,?_,?_⟩
    · funext x
      rw [computes,funA,liftFunction G y z ne tw]
    · dsimp only at ok ⊢
      intro k a b c d hab hcd
      cases k with
      | zero =>
        have f := hab.2.2.1
        change GateOp.or = GateOp.and at f
        cases f
      | succ j =>
        have eq (u v : Fin n) :
            (G.Adj u v ∧ Owns n (lift A y z) (j+1) u v) ↔
            ((erased G z).Adj (proj y z u) (proj y z v) ∧ Owns n A j (proj y z u) (proj y z v)) :=
          and_congr (projected G y z ne tw u v).symm (owner A y z ne j u v)
        rcases ok j _ _ _ _ ((eq a b).mp hab) ((eq c d).mp hcd) with h|h|h|h
        · exact Or.inl ((eq a c).mpr h)
        · exact Or.inr (Or.inl ((eq a d).mpr h))
        · exact Or.inr (Or.inr (Or.inl ((eq b c).mpr h)))
        · exact Or.inr (Or.inr (Or.inr ((eq b d).mpr h)))
  intro n G inst tri four
  let answer (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] :=
    let r (C : Circuit) (j : Nat) (a b : Fin n) := K.Adj a b ∧ Owns n C j a b
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun K ∅ ∧
      ∀ j a b c d, r C j a b → r C j c d → r C j a c ∨ r C j a d ∨ r C j b c ∨ r C j b d
  have solve (k : Nat) : ∀ (K : SimpleGraph (Fin n)) [DecidableRel K.Adj], K.edgeFinset.card = k →
      (∀ a b c, K.Adj a b → K.Adj b c → ¬K.Adj c a) → NoFourCycle K → answer K := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro K dec size ht hf
      by_cases sep : ∀ y z, (∃ w, K.Adj z w) → (∀ w, K.Adj y w ↔ K.Adj z w) → y=z
      · exact core n K ht hf sep
      obtain ⟨y,hy⟩ := Classical.not_forall.mp sep
      obtain ⟨z,hz⟩ := Classical.not_forall.mp hy
      obtain ⟨neigh,hpair⟩ := Classical.not_imp.mp hz
      obtain ⟨tw,ne⟩ := Classical.not_imp.mp hpair
      let H := erased K z
      have sub : H ≤ K := fun a b e => ((erasedAdj K z a b).mp e).1
      have smaller : H < K := by
        apply lt_of_le_of_ne sub
        intro h
        obtain ⟨w,edge⟩ := neigh
        have bad : H.Adj z w := h ▸ edge
        exact ((erasedAdj K z z w).mp bad).2.1 rfl
      have fewer : H.edgeFinset.card < k := by
        rw [← size]
        exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono smaller)
      have no4 : NoFourCycle H := by
        intro a b ab
        apply le_trans _ (hf a b ab)
        apply Finset.card_le_card
        intro w hw
        obtain ⟨h,aw,bw⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨h,sub aw,sub bw⟩
      obtain ⟨A,minA,funA,goodA⟩ := ih _ fewer H rfl (fun a b c p q r => ht a b c (sub p) (sub q) (sub r)) no4
      obtain ⟨D,md,sz,fd,gd⟩ := crossLift K y z ne tw A minA.1 funA goodA
      refine ⟨D,⟨md,?_⟩,fd,gd⟩
      intro E me fe
      obtain ⟨B,mb,lt,fb⟩ := restrictZero n K z neigh E me (fe.trans fd)
      have ale := minA.2 B mb (fb.trans funA.symm)
      omega
  exact solve _ G rfl tri four
