import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4085_317
    (deleted : ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      ∃ x : Fin 10 → Bool, x 0 = false ∧ D.eval (List.ofFn x ++ [!x 0]) ≠ (fun (x : Fin 10 → Bool) => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val = true)) x)
    (few : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      C.gates.countP (fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some 0 || g.inputs.head? == some 10 else g.inputs.contains 0 || g.inputs.contains 10) ≤ 3 → (∀ (x4 : Finset (Fin (10 : ℕ))) (x5 x6 : Finset ℕ), (∀ (x7 : Fin (10 : ℕ)), ↑x7 ∈ x5 ↔ x7 ∈ x4) → ((10 : ℕ) ∈ x5 ↔ (0 : Fin (10 : ℕ)) ∈ x4) → (∀ (x9 : Fin C.size), ∀ x10 ∈ (C.gates.get x9).inputs, ((11 : ℕ) + ↑x9 ∈ x5 → x10 ∈ x5) ∧ ((11 : ℕ) + ↑x9 ∉ x5 → x10 ∈ x5 → x10 ∈ x6)) → (C.output ∈ x5 → C.output ∈ x6) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x4.card (0 : ℕ) ≤ (Finset.image (fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ↥x6) => (C.wires (List.ofFn x11 ++ [!x11 (0 : Fin (10 : ℕ))])).getD (↑x12) Bool.false) Finset.univ).card) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ (fun (x : Fin 10 → Bool) => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val = true)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Finset (Fin (10 : ℕ))) (x5 x6 : Finset ℕ), (∀ (x7 : Fin (10 : ℕ)), ↑x7 ∈ x5 ↔ x7 ∈ x4) → ((10 : ℕ) ∈ x5 ↔ (0 : Fin (10 : ℕ)) ∈ x4) → (∀ (x9 : Fin x1.size), ∀ x10 ∈ (x1.gates.get x9).inputs, ((11 : ℕ) + ↑x9 ∈ x5 → x10 ∈ x5) ∧ ((11 : ℕ) + ↑x9 ∉ x5 → x10 ∈ x5 → x10 ∈ x6)) → (x1.output ∈ x5 → x1.output ∈ x6) → [(1 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (12 : ℕ), (9 : ℕ), (9 : ℕ), (5 : ℕ), (3 : ℕ), (2 : ℕ)].getD x4.card (0 : ℕ) ≤ (Finset.image (fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ↥x6) => (x1.wires (List.ofFn x11 ++ [!x11 (0 : Fin (10 : ℕ))])).getD (↑x12) Bool.false) Finset.univ).card) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5 := by
  intro C fan budget topo
  let charged := (fun (g : Gate) => if g.op.eval [false] then g.inputs.head? == some 0 || g.inputs.head? == some 10 else g.inputs.contains 0 || g.inputs.contains 10)
  by_cases fewUses : C.gates.countP charged ≤ 3
  · exact few C fan budget fewUses topo
  let pick := fun (g : Gate) =>
    if g.op.eval [false] then (if g.inputs.head? == some 0 then 10 else 0)
    else if g.op.eval [] then
      (if g.inputs.contains 0 then 0 else (g.inputs.filter (· != 10)).headD 10)
    else (if g.inputs.contains 10 then 10 else (g.inputs.filter (· != 0)).headD 0)
  let good := fun (g : Gate) =>
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
  have redirect (g : Gate) (ok : good g) (hc : charged g = true) (v : Nat → Bool)
      (z : v 0 = false) (o : v 10 = true) : v (pick g) = g.op.eval (g.inputs.map v) := by
    clear C fan budget topo deleted few fewUses
    obtain ⟨op, xs⟩ := g
    obtain ⟨hop,hlen⟩ := ok
    change op = .and ∨ op = .or ∨ op = .not at hop
    change xs.length ≤ 2 at hlen
    have hand (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have hor (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have hnot (l : List Bool) : GateOp.not.eval l = !l.headD false := rfl
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · rcases hop with rfl | rfl | rfl <;> simp [charged,hand,hor,hnot] at hc
    · rcases hop with rfl | rfl | rfl <;>
        by_cases a0 : a = 0 <;> by_cases a10 : a = 10 <;>
        simp [charged,pick,hand,hor,hnot, a0,a10,z,o, List.contains_iff_mem] at hc ⊢ <;> grind
    · rcases hop with rfl | rfl | rfl <;>
        by_cases a0 : a = 0 <;> by_cases a10 : a = 10 <;>
        by_cases b0 : b = 0 <;> by_cases b10 : b = 10 <;>
        simp [charged,pick,hand,hor,hnot, a0,a10,b0,b10,z,o, List.contains_iff_mem] at hc ⊢ <;> grind
    · simp at hlen
  let step := fun (u : List Bool) (g : Gate) => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  let buf := fun (x : Fin 10 → Bool) => List.ofFn x ++ [!x 0]
  let run := fun (gs : List Gate) (x : Fin 10 → Bool) => gs.foldl step (buf x)
  have runLen (gs : List Gate) (x : Fin 10 → Bool) : (run gs x).length = 11 + gs.length := by
    have len (ls : List Gate) (u : List Bool) : (ls.foldl step u).length = u.length + ls.length := by
      induction ls generalizing u with
      | nil => simp
      | cons g ls ih => rw [List.foldl_cons,ih]; simp [step]; omega
    simp only [run,len,buf,List.length_append,List.length_ofFn,List.length_singleton]
  have keep (ls : List Gate) (u : List Bool) {i : Nat} (hi : i < u.length) :
      (ls.foldl step u).getD i false = u.getD i false := by
    induction ls generalizing u with
    | nil => rfl
    | cons g ls ih => rw [List.foldl_cons,ih _ (by simp [step]; omega)]; exact List.getD_append _ _ _ _ hi
  have pin (ls : List Gate) (x : Fin 10 → Bool) (hx : x 0 = false) :
      (run ls x).getD 0 false = false ∧ (run ls x).getD 10 false = true := by
    unfold run
    rw [keep ls _ (show 0 < (buf x).length by simp [buf]),keep ls _ (show 10 < (buf x).length by simp [buf])]
    constructor
    · change (List.ofFn x ++ [_]).getD 0 false = _
      rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
      exact hx
    · change (List.ofFn x ++ [_]).getD 10 false = _
      rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
      simp [hx]
  have decode (m : List Nat) (u v : List Bool) (eqn : m.map (fun i => u.getD i false) = v)
      (zero : u.getD 0 false = false) (i : Nat) : u.getD (m.getD i 0) false = v.getD i false := by
    have e := List.getD_map (l := m) (d := 0) (n := i) (fun k => u.getD k false)
    rw [eqn, zero] at e
    exact e.symm
  have compress (ls : List Gate) (ok : ∀ g ∈ ls, good g) :
      ∃ (ts : List Gate) (m : List Nat), (∀ g ∈ ts, good g) ∧
        ts.length + ls.countP charged = ls.length ∧ (∀ i ∈ m, i < 11+ts.length) ∧
        ∀ (x : Fin 10 → Bool), x 0 = false → m.map (fun i => (run ts x).getD i false) = run ls x := by
    induction ls using List.reverseRecOn with
    | nil =>
      refine ⟨[],List.range 11,by simp,by simp,by simp,?_⟩
      intro x _
      change (List.range 11).map (fun i => (buf x).getD i false) = buf x
      apply List.ext_getElem
      · simp [buf]
      · intro i hi hj
        rw [List.getElem_map,List.getElem_range,List.getD_eq_getElem _ _ hj]
    | append_singleton ls g ih =>
      obtain ⟨ts,m,ht,size,bound,sem⟩ := ih (fun a ha => ok _ (by simp [ha]))
      have okg := ok g (by simp)
      by_cases hc : charged g = true
      · let j := m.getD (pick g) 0
        refine ⟨ts,m++[j],ht,?_,?_,?_⟩
        · simp [List.countP_append,hc]; omega
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact bound a ha
          · obtain rfl := List.mem_singleton.mp ha
            by_cases h : pick g < m.length
            · exact bound _ (by unfold j; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _)
            · unfold j; rw [List.getD_eq_default _ _ (by omega : m.length ≤ pick g)]; omega
        · intro x hx
          have key := decode m _ _ (sem x hx) (pin ts x hx).1 (pick g)
          have p := pin ls x hx
          have val := key.trans (redirect g okg hc (fun i => (run ls x).getD i false) p.1 p.2)
          simpa only [List.map_append,List.map_cons,List.map_nil,sem x hx,run,List.foldl_append,
            List.foldl_cons,List.foldl_nil,step] using congrArg (fun b => run ls x ++ [b]) val
      · let g' : Gate := ⟨g.op,g.inputs.map fun i => m.getD i 0⟩
        let j := 11+ts.length
        refine ⟨ts++[g'],m++[j],?_,?_,?_,?_⟩
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact ht a ha
          · obtain rfl := List.mem_singleton.mp ha
            simpa [good,g'] using okg
        · simp [List.countP_append,hc]; omega
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · have := bound a ha; simp; omega
          · obtain rfl := List.mem_singleton.mp ha; simp [j]
        · intro x hx
          let u := run ts x
          let v := run ls x
          have eqn : m.map (fun i => u.getD i false) = v := sem x hx
          have hreads : g'.inputs.map (fun i => u.getD i false) = g.inputs.map (fun i => v.getD i false) := by
            change (g.inputs.map _).map _ = _
            rw [List.map_map]
            apply List.map_congr_left
            exact fun i _ => decode m u v eqn (pin ts x hx).1 i
          have old : m.map (fun i => (step u g').getD i false) = v := by
            rw [← eqn]
            apply List.map_congr_left
            intro i hi
            exact List.getD_append _ _ _ _ ((runLen _ _).symm ▸ bound i hi)
          have last : (step u g').getD j false = g.op.eval (g.inputs.map fun i => v.getD i false) := by
            have len : j = u.length := (runLen _ _).symm
            simp only [step, len, List.getD_append_right _ _ _ _ (Nat.le_refl _),
              Nat.sub_self, List.getD_cons_zero, hreads, g']
          simp only [List.map_append,List.map_cons,List.map_nil,run,List.foldl_append,
            List.foldl_cons,List.foldl_nil]
          change m.map (fun i => (step u g').getD i false) ++ [(step u g').getD j false] = step v g
          rw [old,last]
  obtain ⟨ts,m,ht,size,_,sem⟩ := compress C.gates fan
  let D : Circuit := ⟨ts,m.getD C.output 0⟩
  have hD : FanInTwo D := ht
  have small : D.size ≤ 14 := by change ts.length ≤ 14; change C.gates.length ≤ 18 at budget; omega
  obtain ⟨x,hx,mismatch⟩ := deleted D hD small
  refine ⟨x,?_⟩
  have evaluation := decode m _ _ (sem x hx) (pin ts x hx).1 C.output
  change D.eval (buf x) = C.eval (buf x) at evaluation
  exact fun eqn => mismatch (evaluation.trans eqn)
