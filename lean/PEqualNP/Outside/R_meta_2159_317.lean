import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each pair encodes one input column on twelve edges and twelve independent sets.
-- The final column is given by the specified first OR gate.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2159_317
    (compile : ∀ (col : Fin 9 → BitVec 24) (h t : BitVec 24) (C : Circuit)
    , Monotone2 C → t≠0 → t≠-1 →
    (∀ i : Fin 24, let x := fun u => (col u).getLsbD i.val
      (C.wires (List.ofFn x)).getD 9 false = h.getLsbD i.val ∧
        C.eval (List.ofFn x) = t.getLsbD i.val) →
    let p := List.ofFn col ++ [h]
    ∃ fs : List (BitVec 24), fs.length ≤ C.size-1 ∧ t ∈ p ++ fs ∧
      ∀ j : Fin fs.length, let old := p ++ fs.take j.val
        fs.get j ∉ old ∧ fs.get j ≠ 0 ∧ fs.get j ≠ -1 ∧
          ∃ a ∈ old, ∃ b ∈ old, fs.get j = a &&& b ∨ fs.get j = a ||| b)
    (finite : let raw (u : Fin 9) : BitVec 24 := let p := ([(49,1348),(67,2083),(134,788),(268,105),(24,2706),(2592,27),(1088,220),(640,3296),(3328,3840)] : List (ℕ × ℕ)).getD u.val (0,0)
      BitVec.ofNat 24 (4096 * p.1 + p.2)
      let p := List.ofFn raw ++ [raw 0 ||| raw 2]
      ∀ fs : List (BitVec 24), (BitVec.ofNat 24 (4095 * 4096)) ∈ p ++ fs → (∀ j : Fin fs.length, let old := p ++ fs.take j.val
      fs.get j ∉ old ∧ fs.get j ≠ 0 ∧ fs.get j ≠ -1 ∧ ∃ a ∈ old, ∃ b ∈ old,
      fs.get j = a &&& b ∨ fs.get j = a ||| b) → 15 ≤ fs.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan noNot first correct
  let raw (u : Fin 9) : BitVec 24 := let p := ([(49,1348),(67,2083),(134,788),(268,105),(24,2706),(2592,27),(1088,220),(640,3296),(3328,3840)] : List (ℕ × ℕ)).getD u.val (0,0)
    BitVec.ofNat 24 (4096 * p.1 + p.2)
  let h := raw 0 ||| raw 2
  let t := BitVec.ofNat 24 (4095 * 4096)
  let x (i : Fin 24) (u : Fin 9) := (raw u).getLsbD i.val
  have hm : Monotone2 C := by
    intro g hg
    obtain ⟨hgop,hl⟩ := fan g hg
    exact ⟨by simpa [noNot g hg] using hgop,hl⟩
  have hits : ∀ i : Fin 24, (fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) (x i) = t.getLsbD i.val := by decide +kernel
  have helper : ∀ i : Fin 24, (C.wires (List.ofFn (x i))).getD 9 false = h.getLsbD i.val := by
    intro i
    exact (first (x i)).trans (by simp [h,x])
  have values (i : Fin 24) : C.eval (List.ofFn (x i)) = t.getLsbD i.val :=
    (congrFun correct (x i)).trans (hits i)
  obtain ⟨fs,len,output,legal⟩ := compile raw h t C hm (by decide) (by decide) (fun i => ⟨helper i,values i⟩)
  have lb := finite fs output legal
  omega
