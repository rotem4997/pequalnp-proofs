import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm (NoFourCycle readers)

-- Normalize the gates in order. When an AND has one reader and that reader
-- conjoins its value with an earlier wire, move that wire to the first AND.
-- If the wire is true only on graph edges incident to one vertex, every
-- edge the first gate now owns contains that vertex. A primary input always
-- has this property. An earlier AND wire makes the first gate own no edge,
-- as that wire must fire in its strict cone. All earlier gates keep the edges they owned.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5375_2
    (swap : ∀ (n : ℕ) (P M S : List Gate) (s t : List ℕ) (v o : ℕ),
      let m := n + P.length
      let w (p q : List ℕ) : Circuit := ⟨P ++ ⟨.and,p⟩ :: (M ++ ⟨.and,q⟩ :: S),o⟩
      t.Perm [m,v] → v < m → (∀ i ∈ s, i < m) → o ≠ m → (∀ g ∈ M ++ S, m ∉ g.inputs) →
      circuitFun n (w (s.take 1 ++ [v]) (m :: s.drop 1)) = circuitFun n (w s t))
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      let r C j a b := G.Adj a b ∧ Owns n C j a b
      let ok C k := ∀ j < k, ∀ a b c d, r C j a b → r C j c d →
        r C j a c ∨ r C j a d ∨ r C j b c ∨ r C j b d
      let confined C i := (∃ t, i = n+t ∧ (gateAt C t).op = GateOp.and) ∨
        ∃ z : Fin n, ∀ a b, G.Adj a b →
        PEqualNP.CleanedNonEdge.wireVal n C i (pairInput a b) = true → a = z ∨ b = z
      ∀ (C : Circuit) (j : ℕ), IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        ok C j → (C.output = n+j ∨ ∀ k > j, readers n C j = {k} →
          (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i < n+j → ¬confined C i) →
        ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = circuitFun n C ∧ ok D (j+1)) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ) (x9 x10 x11 x12 : Fin x1), x6 x7 x8 x9 x10 → x6 x7 x8 x11 x12 → x6 x7 x8 x9 x11 ∨ x6 x7 x8 x9 x12 ∨ x6 x7 x8 x10 x11 ∨ x6 x7 x8 x10 x12 := by
  classical
  let run (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run_len (gs : List Gate) (w : List Bool) : (gs.foldl run w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [run]; omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl run w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (run w g) (by simp [run]; omega)]
      simp [run, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have conePieces (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      ∃ r, gs.foldl (coneStep n) cs = cs ++ r ∧ r.length = gs.length := by
    induction gs generalizing cs with
    | nil => exact ⟨[],by simp,rfl⟩
    | cons g gs ih =>
      obtain ⟨r,hr,hl⟩ := ih (coneStep n cs g)
      have eq : ∃ e, coneStep n cs g = cs ++ [e] := ⟨_,rfl⟩
      obtain ⟨e,he⟩ := eq
      exact ⟨e :: r,by rw [List.foldl_cons,hr,he,List.append_assoc]; rfl,by simp [hl]⟩
  have prefix_owns (n : ℕ) (P U V : List Gate) (o o' j : ℕ) (hj : j < P.length) (u v : Fin n) :
      Owns n ⟨P ++ U,o⟩ j u v ↔ Owns n ⟨P ++ V,o'⟩ j u v := by
    have readGate (T : List Gate) (o i : ℕ) (hi : i < P.length) :
        gateAt ⟨P ++ T,o⟩ i = P.getD i ⟨.or,[]⟩ := by
      change (P ++ T).getD i _ = _
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have readVal (T : List Gate) (o i : ℕ) (hi : i < P.length) (x : Fin n → Bool) :
        gateVal n ⟨P ++ T,o⟩ i x = (P.foldl run (List.ofFn x)).getD (n+i) false := by
      change ((P ++ T).foldl run (List.ofFn x)).getD (n+i) false = _
      rw [List.foldl_append, keep T _ _ (by simp [run_len]; omega)]
    have coneRead (T : List Gate) (o i : ℕ) :
        InCone n ⟨P ++ T,o⟩ i j ↔ i ∈ (P.foldl (coneStep n) []).getD j [] := by
      change i ∈ ((P ++ T).foldl (coneStep n) []).getD j [] ↔ _
      obtain ⟨s,hp,hl⟩ := conePieces n P []
      have bound : j < (P.foldl (coneStep n) []).length := by simpa [hp,hl] using hj
      obtain ⟨tail,he,_⟩ := conePieces n T (P.foldl (coneStep n) [])
      rw [List.foldl_append,he]
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left bound]
    have transport (S T : List Gate) (o₁ o₂ : ℕ) (h : Owns n ⟨P ++ S,o₁⟩ j u v) :
        Owns n ⟨P ++ T,o₂⟩ j u v := by
      obtain ⟨_,hop,val,anc⟩ := h
      refine ⟨by change j < (P ++ T).length; simp; omega, ?_, ?_, ?_⟩
      · simpa only [readGate T o₂ j hj,readGate S o₁ j hj] using hop
      · simpa only [readVal T o₂ j hj,readVal S o₁ j hj] using val
      · intro i hij hcone hOp
        have hi := hij.trans hj
        have inOld := (coneRead S o₁ i).2 ((coneRead T o₂ i).1 hcone)
        have andOld : (gateAt ⟨P ++ S,o₁⟩ i).op = GateOp.and := by
          simpa only [readGate T o₂ i hi,readGate S o₁ i hi] using hOp
        simpa only [readVal T o₂ i hi,readVal S o₁ i hi] using anc i hij inOld andOld
    exact ⟨transport U V o o',transport V U o' o⟩
  have direct (n : ℕ) (P T : List Gate) (g : Gate) (o t : ℕ) (h : t < P.length)
      (member : n+t ∈ g.inputs) : InCone n ⟨P ++ g :: T,o⟩ t P.length := by
    let cs := P.foldl (coneStep n) []
    obtain ⟨r,hr,hl⟩ := conePieces n P []
    have len : cs.length = P.length := by simp [cs,hr,hl]
    let new := (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n+cs.length))).flatMap
      (fun w => (w-n) :: cs.getD (w-n) [])
    have he : coneStep n cs g = cs ++ [new] := rfl
    have next : P.length < (coneStep n cs g).length := by simp [he,len]
    have contain : t ∈ new := by
      apply List.mem_flatMap.mpr
      refine ⟨n+t,List.mem_filter.mpr ⟨member,decide_eq_true ⟨by omega,by omega⟩⟩,?_⟩
      simp
    change t ∈ ((P ++ g :: T).foldl (coneStep n) []).getD P.length []
    rw [List.foldl_append,List.foldl_cons]
    change t ∈ (T.foldl (coneStep n) (coneStep n cs g)).getD P.length []
    obtain ⟨tail,et,_⟩ := conePieces n T (coneStep n cs g)
    rw [et,List.getD_eq_getElem?_getD,List.getElem?_append_left next,he,← len,List.getElem?_concat_length]
    exact contain
  have twoReads (xs : List ℕ) (a b : ℕ) (hab : a ≠ b)
      (hm : a ∈ xs) (hn : b ∈ xs) (hl : xs.length ≤ 2) : xs.Perm [a,b] := by
    cases xs with
    | nil => simp at hm
    | cons p xs => cases xs with
      | nil => simp only [List.mem_singleton] at hm hn; exact (hab (hm.trans hn.symm)).elim
      | cons q xs => cases xs with
        | nil =>
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm hn
          rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
          · contradiction
          · exact .refl _
          · exact .swap _ _ _
          · contradiction
        | cons a xs => simp at hl
  have splitTwo (C : Circuit) (j k : ℕ) (hjk : j < k) (hk : k < C.gates.length) :
      ∃ P M S : List Gate, P.length = j ∧ k = j + 1 + M.length ∧
        C.gates = P ++ gateAt C j :: (M ++ gateAt C k :: S) := by
    have split (gs : List Gate) (i : ℕ) (hi : i < gs.length) :
        ∃ L R t, gs = L ++ t :: R ∧ L.length = i := by
      exact ⟨gs.take i,gs.drop (i+1),gs[i],by rw [List.cons_getElem_drop_succ,List.take_append_drop],by simp;omega⟩
    obtain ⟨P,R,g,hP,hj⟩ := split C.gates j (hjk.trans hk)
    have hkr : k - (j+1) < R.length := by have := congrArg List.length hP; simp [hj] at this; omega
    obtain ⟨M,S,t,hM,hm⟩ := split R (k-(j+1)) hkr
    have hga : gateAt C j = g := by
      change C.gates.getD j _ = _
      rw [hP,← hj]
      simp [List.getD_eq_getElem?_getD]
    have hka : gateAt C k = t := by
      change C.gates.getD k _ = _
      have pos : k = (P ++ g :: M).length := by simp [hj,hm]; omega
      have he : C.gates = (P ++ g :: M) ++ t :: S := by rw [hP,hM]; simp
      rw [he,pos]
      simp [List.getD_eq_getElem?_getD]
    exact ⟨P,M,S,hj,by omega,by rw [hga,hka,← hM,← hP]⟩
  have othersDontRead (n : ℕ) (C : Circuit) (j k : ℕ) (P M S : List Gate) (s t : Gate)
      (hj : P.length = j) (hk : k = j+1+M.length) (layout : C.gates = P ++ s :: (M ++ t :: S))
      (onlyReader : PEqualNP.TopForm.readers n C j = {k}) :
      ∀ g ∈ M ++ S, n+j ∉ g.inputs := by
    have onlyK (i : ℕ) (hi : i < C.gates.length) (hread : n+j ∈ (gateAt C i).inputs) : i = k := by
      have h : i ∈ PEqualNP.TopForm.readers n C j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hread⟩
      simpa [onlyReader] using h
    intro g hg hread
    rcases List.mem_append.mp hg with hm | hs
    · obtain ⟨A,B,eq⟩ := List.append_of_mem hm
      let i := (P ++ s :: A).length
      have he : C.gates = (P ++ s :: A) ++ g :: (B ++ t :: S) := by rw [layout,eq]; simp
      have hi : i < C.gates.length := by rw [he]; simp [i]
      have gi : gateAt C i = g := by change C.gates.getD i _ = g; rw [he]; simp [i,List.getD_eq_getElem?_getD]
      have hEq := onlyK i hi (gi ▸ hread)
      have hlen := congrArg List.length eq
      simp [i,hj] at hEq
      simp at hlen
      omega
    · obtain ⟨A,B,eq⟩ := List.append_of_mem hs
      let i := (P ++ s :: (M ++ t :: A)).length
      have he : C.gates = (P ++ s :: (M ++ t :: A)) ++ g :: B := by rw [layout,eq]; simp
      have hi : i < C.gates.length := by rw [he]; simp [i]
      have gi : gateAt C i = g := by change C.gates.getD i _ = g; rw [he]; simp [i,List.getD_eq_getElem?_getD]
      have hEq := onlyK i hi (gi ▸ hread)
      simp [i,hj] at hEq
      omega
  -- Build an edge circuit and minimize its size. This includes the empty graph.
  have seed (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ := by
    classical
    let realizes (edges : List (Fin n × Fin n)) := ∃ C : Circuit,
      Monotone2 C ∧ C.output < n+C.gates.length ∧ ∀ x : Fin n → Bool,
        circuitFun n C x = edges.any (fun e => x e.1 && x e.2)
    have andVal (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
    have orVal (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    have build (edges : List (Fin n × Fin n)) : realizes edges := by
      induction edges with
      | nil =>
        refine ⟨⟨[⟨.or,[]⟩],n⟩,?_,by simp,?_⟩
        · intro g hg; simp only [List.mem_singleton] at hg; subst g; exact ⟨Or.inr rfl,by decide⟩
        · intro x
          change ((List.ofFn x) ++ [false]).getD n false = false
          simp [List.getD_eq_getElem?_getD]
      | cons e es ih =>
        obtain ⟨C,mon,hout,old⟩ := ih
        let j := n+C.gates.length
        let g : Gate := ⟨.and,[e.1.val,e.2.val]⟩
        let k : Gate := ⟨.or,[j,C.output]⟩
        refine ⟨⟨C.gates ++ [g,k],j+1⟩,?_,by simp [j]; omega,?_⟩
        · intro z hz
          change z ∈ C.gates ++ [g,k] at hz
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with h|rfl|rfl
          · exact mon z h
          · exact ⟨Or.inl rfl,Nat.le_refl 2⟩
          · exact ⟨Or.inr rfl,Nat.le_refl 2⟩
        · intro x
          let w := C.gates.foldl run (List.ofFn x)
          have len : w.length = j := by simp [w,j,run_len]
          have primary (v : Fin n) : w.getD v.val false = x v := by
            change (C.gates.foldl run (List.ofFn x)).getD _ false = _
            rw [keep _ _ _ (by simp)]
            simp [List.getD_eq_getElem?_getD]
          have cg : run w g = w ++ [x e.1 && x e.2] := by
            change w ++ [GateOp.and.eval [w.getD e.1.val false,w.getD e.2.val false]] = _
            rw [andVal,primary,primary]
          let y := run w g
          have ylen : y.length = j+1 := by simp [y,cg,len]
          have yj : y.getD j false = (x e.1 && x e.2) := by
            simp [y,cg,← len,List.getD_eq_getElem?_getD]
          have oldOut : y.getD C.output false = es.any (fun e => x e.1 && x e.2) := by
            have h : C.output < w.length := by omega
            have ho := old x
            change w.getD C.output false = _ at ho
            simpa only [y,cg,List.getD_eq_getElem?_getD,List.getElem?_append_left h] using ho
          have ck : run y k = y ++ [(x e.1 && x e.2) || es.any (fun e => x e.1 && x e.2)] := by
            change y ++ [GateOp.or.eval [y.getD j false,y.getD C.output false]] = _
            rw [orVal,yj,oldOut]
          change ((C.gates ++ [g,k]).foldl run (List.ofFn x)).getD (j+1) false = _
          rw [List.foldl_append]
          change (run y k).getD (j+1) false = _
          rw [ck,← ylen]
          simp [List.getD_eq_getElem?_getD]
    let es := ((Finset.univ : Finset (Fin n × Fin n)).filter fun e => G.Adj e.1 e.2).toList
    obtain ⟨C,mon,_,hc⟩ := build es
    have computes : circuitFun n C = graphFun G ∅ := by
      funext x
      rw [hc]
      apply Bool.eq_iff_iff.mpr
      change es.any _ = true ↔ (decide (∃ i ∈ (∅ : Finset (Fin n)), x i = true) || decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = true
      have empty : decide (∃ i ∈ (∅ : Finset (Fin n)), x i = true) = false := by simp
      simp only [es,List.any_eq_true,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,
        Bool.and_eq_true_iff,empty,Bool.false_or,decide_eq_true_eq]
      constructor
      · rintro ⟨⟨a,b⟩,hab,ha,hb⟩; exact ⟨a,b,hab,ha,hb⟩
      · rintro ⟨a,b,hab,ha,hb⟩; exact ⟨(a,b),hab,ha,hb⟩
    let cost (k : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = k
    have nonempty : ∃ k, cost k := ⟨_,C,mon,computes,rfl⟩
    obtain ⟨D,hm,hf,hs⟩ := Nat.find_spec nonempty
    exact ⟨D,⟨hm,fun E hE he => hs ▸ Nat.find_min' nonempty ⟨E,hE,he.trans hf,rfl⟩⟩,hf⟩
  intro n G _ tri square
  let r (C : Circuit) (j : ℕ) (a b : Fin n) := G.Adj a b ∧ Owns n C j a b
  let good (C : Circuit) (j : ℕ) := ∀ a b c d, r C j a b → r C j c d →
    r C j a c ∨ r C j a d ∨ r C j b c ∨ r C j b d
  let ok (C : Circuit) (k : ℕ) := ∀ j < k, good C j
  let confined (C : Circuit) (i : ℕ) := (∃ t, i = n+t ∧ (gateAt C t).op = GateOp.and) ∨
    ∃ z : Fin n, ∀ a b, G.Adj a b →
    PEqualNP.CleanedNonEdge.wireVal n C i (pairInput a b) = true → a = z ∨ b = z
  have atAnd (P T : List Gate) (args : List ℕ) (o : ℕ) (x : Fin n → Bool) :
      gateVal n ⟨P ++ ⟨.and,args⟩ :: T,o⟩ P.length x =
      args.all (fun i => (P.foldl run (List.ofFn x)).getD i false) := by
    let w := P.foldl run (List.ofFn x)
    have len : w.length = n + P.length := by simp [w,run_len]
    change ((P ++ ⟨.and,args⟩ :: T).foldl run (List.ofFn x)).getD _ false = _
    rw [List.foldl_append,List.foldl_cons]
    change (T.foldl run (w ++ [(args.map (fun i => w.getD i false)).all id])).getD _ false = _
    rw [keep T _ _ (by simp [len]),← len]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_concat_length,Option.getD_some,List.all_map]
    rfl
  have reverse {C : Circuit} {j : ℕ} {u v : Fin n} (h : r C j u v) : r C j v u := by
    have e : pairInput v u = pairInput u v := by
      funext i
      exact decide_eq_decide.mpr or_comm
    rcases h with ⟨adj,hj,hop,hval,hcone⟩
    exact ⟨adj.symm,hj,hop,e ▸ hval,fun i hi hc hand => e ▸ hcone i hi hc hand⟩
  have sizeEq (D : Circuit) : D.size = D.gates.length := rfl
  have extend (C : Circuit) (j : ℕ) (hm : IsMinimalMonoCircuit n C)
      (hf : circuitFun n C = graphFun G ∅) (hp : ok C j) :
      ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧ ok D (j+1) := by
    by_cases safe : good C j
    · exact ⟨C,hm,hf,fun i hi => if e : i=j then e ▸ safe else hp i (by omega)⟩
    by_cases other : C.output = n+j ∨ ∀ k > j, readers n C j = {k} →
        (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i < n+j → ¬confined C i
    · obtain ⟨D,hd,he,okD⟩ := repair n G tri square C j hm hf hp other
      exact ⟨D,hd,he.trans hf,okD⟩
    push Not at other
    obtain ⟨ho,k,hjk,onlyK,opK,i,iread,hi,hguard⟩ := other
    have kr : k ∈ readers n C j := onlyK ▸ Finset.mem_singleton.mpr rfl
    have hk := Finset.mem_range.mp (Finset.mem_filter.mp kr).1
    have mark := (Finset.mem_filter.mp kr).2
    have real (l : ℕ) (hl : l < C.gates.length) : gateAt C l ∈ C.gates := by
      change C.gates.getD l _ ∈ C.gates
      simp [List.getD_eq_getElem?_getD,hl]
    have klegal := hm.1 (gateAt C k) (real k hk)
    have readerArgs := twoReads (gateAt C k).inputs (n+j) i (by omega) mark iread klegal.2
    change ¬ ∀ a b c d, r C j a b → r C j c d → _ at safe
    push Not at safe
    obtain ⟨a,b,_,_,ab,_,_⟩ := safe
    have opJ := ab.2.2.1
    have jlegal := hm.1 (gateAt C j) (real j ab.2.1)
    obtain ⟨P,M,S,hj,pos,shape⟩ := splitTwo C j k hjk hk
    let s := (gateAt C j).inputs
    let t := (gateAt C k).inputs
    have oldJ : gateAt C j = ⟨.and,s⟩ := by exact congrArg (fun op => Gate.mk op s) opJ
    have oldK : gateAt C k = ⟨.and,t⟩ := by exact congrArg (fun op => Gate.mk op t) opK
    rw [oldJ,oldK] at shape
    let w (p q : List ℕ) : Circuit := ⟨P ++ ⟨.and,p⟩ :: (M ++ ⟨.and,q⟩ :: S),C.output⟩
    have eqC : C = w s t := by exact congrArg (fun gs => Circuit.mk gs C.output) shape
    let newS := s.take 1 ++ [i]
    let newT := (n+j) :: s.drop 1
    let D := w newS newT
    -- Only the two displayed gates change. The moved operands existed before both.
    have unread := othersDontRead n C j k P M S _ _ hj pos shape onlyK
    have row := ab.2.2.2.1
    rw [eqC,← hj] at row
    change gateVal n ⟨P ++ _ :: _,_⟩ P.length (pairInput a b) = true at row
    rw [atAnd] at row
    have edges : ∀ m ∈ s, m < n+P.length := by
      intro m mm
      have on := List.all_eq_true.mp row m mm
      by_contra! off
      have len : (P.foldl run (List.ofFn (pairInput a b))).length ≤ m := by simpa [run_len] using off
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none len] at on
    have same : circuitFun n D = circuitFun n C := by
      have perm : t.Perm [n+P.length,i] := by simpa only [hj] using readerArgs
      have hsw := swap n P M S s t i C.output perm (hj.symm ▸ hi) edges (hj.symm ▸ ho) (hj.symm ▸ unread)
      simpa only [hj,eqC] using hsw
    have legal : Monotone2 D := by
      intro g hg
      change g ∈ P ++ _ :: (M ++ _ :: S) at hg
      simp only [List.mem_append,List.mem_cons] at hg
      rcases hg with h|rfl|h|rfl|h
      · exact hm.1 g (shape ▸ List.mem_append_left _ h)
      · refine ⟨Or.inl rfl,?_⟩
        change (s.take 1 ++ [i]).length ≤ 2
        simp
      · exact hm.1 g (shape ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
      · refine ⟨Or.inl rfl,?_⟩
        change ((n+j) :: s.drop 1).length ≤ 2
        have bound : s.length ≤ 2 := jlegal.2
        simp; omega
      · exact hm.1 g (shape ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ h))))
    have sizeD : D.size = C.size := by
      rw [sizeEq,sizeEq,shape]
      change (P ++ _ :: (M ++ _ :: S)).length = _
      simp
    have minimal : IsMinimalMonoCircuit n D := ⟨legal,fun E he ef => sizeD ▸ hm.2 E he (ef.trans same)⟩
    refine ⟨D,minimal,same.trans hf,?_⟩
    have transfer (l : ℕ) (hl : l < j) (u v : Fin n) : r D l u v ↔ r C l u v := by
      refine and_congr_right fun _ => ?_
      rw [eqC]
      apply prefix_owns n P
      omega
    have lit (u z : Fin n) (edge : r D j u z) :
        (P.foldl run (List.ofFn (pairInput u z))).getD i false = true := by
      have val := edge.2.2.2.1
      rw [← hj] at val
      change gateVal n ⟨P ++ ⟨.and,newS⟩ :: _,_⟩ P.length (pairInput u z) = true at val
      rw [atAnd] at val
      exact List.all_eq_true.mp val i (by simp [newS])
    -- A direct AND ancestor precludes ownership. Otherwise the new guard gives a center.
    have star : ∃ v : Fin n, ∀ u z, r D j u z → u = v ∨ z = v := by
      rcases hguard with ⟨l,wire,opL⟩ | ⟨v,guard⟩
      · refine ⟨a,fun u z edge => False.elim ?_⟩
        have lt : l < P.length := by omega
        have ancestry : InCone n D l j := by
          rw [← hj]
          exact direct n P _ _ _ l lt (by change n+l ∈ newS; simp [newS,wire])
        have opNew : (gateAt D l).op = GateOp.and := by
          change ((P ++ _).getD l _).op = _
          change (C.gates.getD l _).op = _ at opL
          rw [shape] at opL
          simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt] using opL
        have off := edge.2.2.2.2 l (by omega) ancestry opNew
        change ((P ++ _).foldl run (List.ofFn (pairInput u z))).getD (n+l) false = false at off
        rw [List.foldl_append,keep _ _ _ (by simp [run_len]; omega),← wire] at off
        exact Bool.noConfusion (off.symm.trans (lit u z edge))
      · refine ⟨v,fun u z edge => guard u z edge.1 ?_⟩
        change (C.gates.foldl run (List.ofFn (pairInput u z))).getD i false = true
        rw [shape,List.foldl_append,keep _ _ _ (by simp [run_len,hj]; exact hi)]
        exact lit u z edge
    obtain ⟨v,center⟩ := star
    intro l hl u z p q uz pq
    by_cases e : l = j
    · subst l
      rcases center u z uz with rfl | rfl <;> rcases center p q pq with h | h
      · exact Or.inr (Or.inl (h ▸ pq))
      · exact Or.inl (h ▸ reverse pq)
      · exact Or.inl (h ▸ uz)
      · exact Or.inr (Or.inl (h ▸ uz))
    · have lt : l < j := by omega
      have cross := hp l lt u z p q ((transfer _ lt _ _).mp uz) ((transfer _ lt _ _).mp pq)
      exact cross.imp ((transfer _ lt _ _).mpr) (Or.imp ((transfer _ lt _ _).mpr)
        (Or.imp ((transfer _ lt _ _).mpr) ((transfer _ lt _ _).mpr)))
  obtain ⟨C₀,min₀,hfun₀⟩ := seed n G
  have all (k : ℕ) : ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧ ok C k := by
    induction k with
    | zero => exact ⟨C₀,min₀,hfun₀,fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ j ih => obtain ⟨C,hm,hf,hp⟩ := ih; exact extend C j hm hf hp
  obtain ⟨D,hm,hf,hp⟩ := all C₀.size
  refine ⟨D,hm,hf,?_⟩
  intro j a b c d ab cd
  have bd := hm.2 C₀ min₀.1 (hfun₀.trans hf.symm)
  exact hp j (lt_of_lt_of_le ab.2.1 bd) a b c d ab cd
