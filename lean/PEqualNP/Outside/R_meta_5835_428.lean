import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Bit-vector simulation adapts the checked compiler in R_meta_2928_1.
-- Bits 0 through 16 in the monotone instance are minimal true inputs. Its ten
-- remaining bits are maximal false inputs. The signed instance contains three
-- blocks of 256 inputs, one block per permitted setting of vertices zero and one.
set_option maxRecDepth 60000 in
set_option maxHeartbeats 15000000 in
theorem PEqualNP.Outside.R_meta_5835_428
    (mono : let bank := ([78959277, 55258451, 67371142, 26740244, 4333592, 16910624, 1331264, 7963008, 106962432, 125952000] : List (BitVec 27))
      let step := fun (s : List (BitVec 27)) (t : Fin 3 × BitVec 27 × BitVec 27) =>
      let a := t.2.1
      let b := t.2.2
      let z := if t.1=0 then a &&& b else if t.1=1 then a ||| b else ~~~a
      if a∈s ∧ b∈s ∧ z∉s then z::s else s
      ∀ ts : List (Fin 3 × BitVec 27 × BitVec 27), ts.length ≤ 17 →
        (∀ t∈ts, t.1≠2) → (131071 : BitVec 27) ∉ ts.foldl step (0::(~~~0)::bank))
    (signed : let col := fun (i : ℕ) =>
      let q : ℕ := 2^256
      BitVec.ofNat 768 (if i=0 then (q-1)*(1+q*q) else if i=1 then (q-1)*(q+q*q)
        else (1+q+q*q)*((q-1)/(2^(2^(i-2))+1))*2^(2^(i-2)))
      let bank := (List.range 10).map col
      let target := ~~~(BitVec.ofNat 768 (([1407396358848519, 4294967299, 7, 3, 90194318613, 73014444049, 1285, 1] : List ℕ).foldr (fun b acc => b+(acc<<<64)) 0))
      let step := fun (s : List (BitVec 768)) (t : Fin 3 × BitVec 768 × BitVec 768) =>
      let a := t.2.1
      let b := t.2.2
      let z := if t.1=0 then a &&& b else if t.1=1 then a ||| b else ~~~a
      if a∈s ∧ b∈s ∧ z∉s then z::s else s
      ∀ ts : List (Fin 3 × BitVec 768 × BitVec 768), ts.length ≤ 17 →
        (∃ t∈ts, t.1=2) → target ∉ ts.foldl step (0::(~~~0)::bank)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ))) = Bool.true ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C fan sz
  let graph (x : Fin 10 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  by_contra noBad
  have agrees (x : Fin 10 → Bool) (hp : (x 0 || x 1)=true) : C.eval (List.ofFn x)=graph x := by
    by_contra hn
    exact noBad ⟨x,hp,hn⟩
  let A (g : Gate) : Fin 3 := if g.op.eval [] then (if g.op.eval [true] then 0 else 2) else 1
  let step {w : ℕ} := fun (s : List (BitVec w)) (t : Fin 3 × BitVec w × BitVec w) =>
      let a := t.2.1
      let b := t.2.2
      let z := if t.1=0 then a &&& b else if t.1=1 then a ||| b else ~~~a
      if a∈s ∧ b∈s ∧ z∉s then z::s else s
  have compile (wth : ℕ) (raw : List (BitVec wth)) (target : BitVec wth)
      (row : Fin wth → Fin 10 → Bool)
      (bits : ∀ r : Fin wth, raw.map (fun u => u.getLsbD r.val) = List.ofFn (row r))
      (spec : ∀ r : Fin wth, (row r 0 || row r 1)=true ∧ target.getLsbD r.val=graph (row r)) :
      ∃ ts : List (Fin 3 × BitVec wth × BitVec wth), ts.map Prod.fst = C.gates.map A ∧
        ts.length ≤ 17 ∧ target ∈ ts.foldl step (0::(~~~0)::raw) := by
    let arg (g : Gate) (w : List (BitVec wth)) (l : ℕ) :=
      if l<g.inputs.length then w.getD (g.inputs.getD l 0) 0
      else if A g=0 then ~~~(0 : BitVec wth) else 0
    let value (g : Gate) (w : List (BitVec wth)) :=
      let u := arg g w 0
      let v := arg g w 1
      if A g=0 then u &&& v else if A g=1 then u ||| v else ~~~u
    let ev (gs : List Gate) (w : List (BitVec wth)) :=
      gs.foldl (fun s g => s++[value g s]) w
    let good (g : Gate) := g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2
    let actual (gs : List Gate) (w : List Bool) := gs.foldl
      (fun s g => s++[g.op.eval (g.inputs.map fun a => s.getD a false)]) w
    have read (w : List (BitVec wth)) (r : Fin wth) (l : ℕ) :
        (w.map (fun a => a.getLsbD r.val)).getD l false=(w.getD l 0).getLsbD r.val := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
      cases w[l]? <;> simp
    have andEval (l : List Bool) : GateOp.and.eval l=l.all id := rfl
    have orEval (l : List Bool) : GateOp.or.eval l=l.any id := rfl
    have notEval (l : List Bool) : GateOp.not.eval l= !(l.headD false) := rfl
    have gateBit (g : Gate) (w : List (BitVec wth)) (r : Fin wth) (ok : good g) :
        (value g w).getLsbD r.val=g.op.eval (g.inputs.map fun a => (w.getD a 0).getLsbD r.val) := by
      obtain ⟨o,ins⟩ := g
      obtain ⟨op,sz⟩ := ok
      change o∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) at op
      change ins.length≤2 at sz
      rcases op with h|h|h <;> obtain rfl := h
      all_goals
        have oneB : (~~~(0 : BitVec wth))[r.val] = true := by
          rw [← BitVec.getLsbD_eq_getElem]; simp only [BitVec.getLsbD_not]; simp [r.isLt]
        rcases ins with _|⟨u,_|⟨v,_|⟨z,zs⟩⟩⟩ <;>
          simp [value,arg,A,andEval,orEval,notEval,BitVec.getLsbD_and,BitVec.getLsbD_or,
            BitVec.getLsbD_not,r.isLt,oneB] at * <;> first | omega | exact fun _ => oneB
    have evalBit (gs : List Gate) (ok : ∀ g∈gs, good g) (w : List (BitVec wth)) (r : Fin wth) :
        (ev gs w).map (fun v => v.getLsbD r.val) = actual gs (w.map (fun v => v.getLsbD r.val)) := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (ev gs (w++[value g w])).map _=actual gs ((w.map _)++[_])
        rw [ih (fun z hz => ok z (List.mem_cons_of_mem _ hz))]
        simp only [List.map_append,List.map_singleton,gateBit _ _ _ (ok _ List.mem_cons_self),read]
    have member (w : List (BitVec wth)) (n : ℕ) : w.getD n 0 ∈ (0 : BitVec wth)::(~~~0)::w := by
      rw [List.getD_eq_getElem?_getD]
      generalize h : w[n]? = opt
      cases opt with
      | none => exact List.mem_cons_self
      | some v =>
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_getElem? h))
    have sim (gs : List Gate) (w s : List (BitVec wth)) (hw : ∀ z∈(0 : BitVec wth)::(~~~0)::w,z∈s) :
        ∃ ts : List (Fin 3 × BitVec wth × BitVec wth), ts.map Prod.fst = gs.map A ∧ ts.length ≤ gs.length ∧
          ∀ z∈(0 : BitVec wth)::(~~~0)::ev gs w, z∈ts.foldl step s := by
      induction gs generalizing w s with
      | nil => exact ⟨[],rfl,le_rfl,hw⟩
      | cons g gs ih =>
        let t : Fin 3 × BitVec wth × BitVec wth := (A g,arg g w 0,arg g w 1)
        have pin (l : ℕ) : arg g w l ∈ s := by
          apply hw
          dsimp only [arg]
          split
          · exact member w _
          · split <;> simp
        have keeps (z : BitVec wth) (hz : z∈s) : z∈step s t := by
          change z∈(if arg g w 0∈s ∧ arg g w 1∈s ∧ value g w∉s then value g w::s else s)
          split
          · exact List.mem_cons_of_mem _ hz
          · exact hz
        have put : value g w∈step s t := by
          change value g w ∈ (if arg g w 0∈s ∧ arg g w 1∈s ∧ value g w∉s then value g w::s else s)
          by_cases h : value g w∈s <;> simp [pin,h]
        have next (z : BitVec wth) (hz : z∈(0 : BitVec wth)::(~~~0)::(w++[value g w])) : z∈step s t := by
          simp only [List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false] at hz
          rcases hz with h|h|h|h
          · exact keeps _ (hw _ (List.mem_cons.mpr (Or.inl h)))
          · exact keeps _ (hw _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h)))))
          · exact keeps _ (hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
          · exact h ▸ put
        obtain ⟨ts,tags,len,res⟩ := ih (w++[value g w]) (step s t) next
        exact ⟨t::ts,by simp [t,tags],Nat.succ_le_succ len,res⟩

    have out : (ev C.gates raw).getD C.output 0=target := by
      apply BitVec.eq_of_getLsbD_eq
      intro n hn
      let r : Fin wth := ⟨n,hn⟩
      change ((ev C.gates raw).getD C.output 0).getLsbD r.val=target.getLsbD r.val
      rw [←read,evalBit C.gates fan,bits,(spec r).2]
      exact agrees (row r) (spec r).1
    obtain ⟨ts,tags,len,all⟩ := sim C.gates raw (0::(~~~0)::raw) (fun _ h => h)
    have found := all _ (member (ev C.gates raw) C.output)
    exact ⟨ts,tags,len.trans sz,out ▸ found⟩
  by_cases negated : (2 : Fin 3) ∈ C.gates.map A
  · let col := fun (i : ℕ) =>
      let q : ℕ := 2^256
      BitVec.ofNat 768 (if i=0 then (q-1)*(1+q*q) else if i=1 then (q-1)*(q+q*q)
        else (1+q+q*q)*((q-1)/(2^(2^(i-2))+1))*2^(2^(i-2)))
    let raw := (List.range 10).map col
    let target := ~~~(BitVec.ofNat 768 (([1407396358848519, 4294967299, 7, 3, 90194318613, 73014444049, 1285, 1] : List ℕ).foldr (fun b acc => b+(acc<<<64)) 0))
    let row (r : Fin 768) (j : Fin 10) := (raw.getD j.val 0).getLsbD r.val
    have bits : ∀ r : Fin 768, raw.map (fun u => u.getLsbD r.val) = List.ofFn (row r) := by
      decide +kernel
    have spec : ∀ r : Fin 768, (row r 0 || row r 1)=true ∧ target.getLsbD r.val=graph (row r) := by
      decide +kernel
    obtain ⟨ts,tags,len,found⟩ := compile 768 raw target row bits spec
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp (tags ▸ negated : (2 : Fin 3) ∈ ts.map Prod.fst)
    exact signed ts len ⟨t,ht,eq⟩ found
  · let raw := ([78959277, 55258451, 67371142, 26740244, 4333592, 16910624, 1331264, 7963008, 106962432, 125952000] : List (BitVec 27))
    let target := (131071 : BitVec 27)
    let row (r : Fin 27) (j : Fin 10) := (raw.getD j.val 0).getLsbD r.val
    have bits : ∀ r : Fin 27, raw.map (fun u => u.getLsbD r.val) = List.ofFn (row r) := by
      decide +kernel
    have spec : ∀ r : Fin 27, (row r 0 || row r 1)=true ∧ target.getLsbD r.val=graph (row r) := by
      decide +kernel
    obtain ⟨ts,tags,len,found⟩ := compile 27 raw target row bits spec
    apply mono ts len _ found
    intro t ht eq
    exact negated (tags ▸ List.mem_map.mpr ⟨t,ht,eq⟩)
