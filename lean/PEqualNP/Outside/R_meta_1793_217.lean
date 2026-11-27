import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pair codes give the two vertex labels in decimal, with an implicit leading zero.
-- The promised bound is the same hypothesis used in the cut R_meta_1667_3.
theorem PEqualNP.Outside.R_meta_1793_217
    (promised : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (x 0 && x 1) = false →
        D.eval (List.ofFn x ++ [false]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 14 ≤ D.size)
    (pairs :
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ e ∈ ([1,2,3,4,5,6,7,8,23,24,25,26,27,28,34,36,37,38,46,47] : List ℕ), ∀ D : Circuit,
        FanInTwo D → D.size ≤ 13 → D.output ≤ 24 →
        (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
        ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 && x 1,
          x (Fin.ofNat 9 (e / 10)) || x (Fin.ofNat 9 (e % 10))]) ≠ f x) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) ||
    (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
    (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  let edge (x : Fin 9 → Bool) := x 0 && x 1
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [edge x]
  let pin (k : Fin 11) (x : Fin 9 → Bool) := (seed x).getD k.val false
  let left (e : ℕ) := Fin.ofNat 9 (e / 10)
  let right (e : ℕ) := Fin.ofNat 9 (e % 10)
  let codes : List ℕ := [1,2,3,4,5,6,7,8,23,24,25,26,27,28,34,36,37,38,46,47]
  let perm (flip : Bool) (i : Fin 9) : Fin 9 :=
    if flip then (![1,0,5,8,6,2,4,7,3] : Fin 9 → Fin 9) i else i
  let row (flip : Bool) (x : Fin 9 → Bool) := fun i => x (perm flip i)
  have invariant : ∀ flip x, F (row flip x) =
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (left e) && x (right e)) := by decide +kernel
  have fixedEdge (flip : Bool) (x) : edge (row flip x) = edge x := by
    cases flip
    · rfl
    · exact Bool.and_comm ..
  have orbit : ∀ a b : Fin 9, a ≠ b → ∃ flip : Bool, ∃ e ∈ codes,
      (perm flip a = left e ∧ perm flip b = right e) ∨
      (perm flip a = right e ∧ perm flip b = left e) := by decide +kernel
  have raw (x : Fin 9 → Bool) (tail : List Bool) (v : Fin 9) :
      (List.ofFn x ++ tail).getD v.val false = x v := by
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have at9 (x : Fin 9 → Bool) (b : Bool) (bs : List Bool) :
      (List.ofFn x ++ b :: bs).getD 9 false = b := by
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have at10 (x : Fin 9 → Bool) (a b : Bool) :
      (List.ofFn x ++ [a,b]).getD 10 false = b := by
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have seedLen (x) : (seed x).length = 10 := by simp [seed]
  have dummy (x) : pin 10 x = false := List.getD_eq_default _ _ (by rw [seedLen]; decide)
  let bound (i : ℕ) : Fin 11 := ⟨min i 10, by omega⟩
  have clipped (i : ℕ) (x) : pin (bound i) x = (seed x).getD i false := by
    change (seed x).getD (min i 10) false = _
    by_cases hi : i ≤ 10
    · rw [Nat.min_eq_left hi]
    · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by rw [seedLen]),
        List.getD_eq_default _ _ (by rw [seedLen]; omega)]
  intro pins arity C fan small
  have padded : ∃ p q : Fin 11, ∀ x, GateOp.or.eval (pins.map fun i => (seed x).getD i false) =
      (pin p x || pin q x) := by
    rcases pins with _ | ⟨a, _ | ⟨b,_ | ⟨v,vs⟩⟩⟩
    · exact ⟨10,10,fun x => by rw [dummy]; rfl⟩
    · refine ⟨bound a,10,fun x => ?_⟩
      rw [clipped, dummy]
      rfl
    · refine ⟨bound a,bound b,fun x => ?_⟩
      rw [clipped, clipped]
      change (_ || (_ || false)) = _
      simp
    · simp at arity
  obtain ⟨p,q,padded⟩ := padded
  let old (x : Fin 9 → Bool) := List.ofFn x ++ [edge x, pin p x || pin q x]
  have normalize (n : ℕ) (hn : n ≤ 11) (label : Fin 11 → Fin n) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output ≤ 24 ∧
        (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) ∧
        ∀ (v w : List Bool), v.length = 11 → w.length = n →
        (∀ k : Fin 11, v.getD k.val false = w.getD (label k).val false) →
        C.eval v = D.eval w := by
    let addr (i : ℕ) := if h : i < 11 then (label ⟨i,h⟩).val else min 24 (n + (i - 11))
    let mapped (g : Gate) : Gate := ⟨g.op, g.inputs.map addr⟩
    let D : Circuit := ⟨C.gates.map mapped, addr C.output⟩
    have bounded (i : ℕ) : addr i ≤ 24 := by
      dsimp only [addr]
      split
      next h => have := (label ⟨i,h⟩).isLt; omega
      next => omega
    refine ⟨D, ?_, ?_, bounded _, ?_, ?_⟩
    · intro g hg
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,arity⟩ := fan v hv
      exact ⟨op, by simpa only [mapped, List.length_map] using arity⟩
    · exact List.length_map mapped
    · intro g hg i hi
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hg
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
      exact bounded _
    intro v w hv hw hinputs
    have lookup (t : List Bool) (size : 11 + t.length ≤ 24) (i : ℕ) :
        (v ++ t).getD i false = (w ++ t).getD (addr i) false := by
      by_cases hi : i < 11
      · rw [List.getD_append _ _ _ _ (by omega),
          show addr i = (label ⟨i,hi⟩).val by simp [addr, hi],
          List.getD_append _ _ _ _ (by rw [hw]; exact (label _).isLt)]
        exact hinputs ⟨i,hi⟩
      · rw [show addr i = min 24 (n + (i - 11)) by simp [addr, hi]]
        by_cases h : n + (i - 11) ≤ 24
        · rw [Nat.min_eq_right h, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), hv, hw,
            show n + (i - 11) - n = i - 11 by omega]
        · rw [Nat.min_eq_left (by omega),
            List.getD_eq_default _ _ (by rw [List.length_append,hv]; omega),
            List.getD_eq_default _ _ (by rw [List.length_append,hw]; omega)]
    let step (bits : List Bool) (g : Gate) :=
      bits ++ [g.op.eval (g.inputs.map fun i => bits.getD i false)]
    have simulate (gs : List Gate) (t : List Bool) (size : 11 + t.length + gs.length ≤ 24) :
        ∃ u, gs.foldl step (v ++ t) = v ++ u ∧
          (gs.map mapped).foldl step (w ++ t) = w ++ u ∧ 11 + u.length ≤ 24 := by
      induction gs generalizing t with
      | nil => exact ⟨t,rfl,rfl,by simpa using size⟩
      | cons g gs ih =>
        simp only [List.length_cons] at size
        let b := g.op.eval (g.inputs.map fun i => (v ++ t).getD i false)
        have oldStep : step (v ++ t) g = v ++ (t ++ [b]) := List.append_assoc ..
        have values : ((mapped g).inputs.map fun i => (w ++ t).getD i false) =
            g.inputs.map fun i => (v ++ t).getD i false := by
          simp only [mapped,List.map_map]
          exact List.map_congr_left fun i _ => (lookup t (by omega) i).symm
        have newStep : step (w ++ t) (mapped g) = w ++ (t ++ [b]) := by
          simp only [step, values, mapped, b, List.append_assoc]
        simp only [List.map_cons, List.foldl_cons, oldStep, newStep]
        exact ih (t ++ [b]) (by simp only [List.length_append, List.length_singleton]; omega)
    have cap : C.gates.length ≤ 13 := small
    obtain ⟨u, leftRun, rightRun, hu⟩ := simulate C.gates [] (by simp; omega)
    simp only [List.append_nil] at leftRun rightRun
    change (C.gates.foldl step v).getD C.output false =
      ((C.gates.map mapped).foldl step w).getD (addr C.output) false
    rw [leftRun, rightRun, lookup u hu]
  by_contra! counter
  have correct (x) : C.eval (old x) = F x := by
    have h : C.eval (seed x ++ [GateOp.or.eval (pins.map fun i => (seed x).getD i false)]) = F x :=
      Classical.not_not.mp (counter x)
    rw [padded] at h
    simpa only [old, seed, List.append_assoc, List.singleton_append] using h
  have oldLen (x) : (old x).length = 11 := by simp [old]
  by_cases proper : p.val < 9 ∧ q.val < 9 ∧ p ≠ q
  · obtain ⟨hp,hq,ne⟩ := proper
    let a : Fin 9 := ⟨p.val,hp⟩
    let b : Fin 9 := ⟨q.val,hq⟩
    have ab : a ≠ b := fun h => ne (Fin.ext (congrArg (fun i : Fin 9 => i.val) h))
    obtain ⟨flip,e,he,matchPair⟩ := orbit a b ab
    let label (k : Fin 11) : Fin 11 :=
      if h : k.val < 9 then ⟨(perm flip ⟨k.val,h⟩).val, by have := (perm flip ⟨k.val,h⟩).isLt; omega⟩
      else k
    let start (x : Fin 9 → Bool) := List.ofFn x ++ [edge x, x (left e) || x (right e)]
    have gate (x) : (pin p (row flip x) || pin q (row flip x)) = (x (left e) || x (right e)) := by
      change ((List.ofFn _ ++ [_]).getD a.val false || (List.ofFn _ ++ [_]).getD b.val false) = _
      rw [raw, raw]
      change (x (perm flip a) || x (perm flip b)) = _
      rcases matchPair with ⟨h,k⟩ | ⟨h,k⟩
      · rw [h,k]
      · rw [h,k,Bool.or_comm]
    obtain ⟨D,dfan,ds,dout,dpins,run⟩ := normalize 11 (by decide) label
    obtain ⟨x,hx⟩ := pairs e he D dfan (ds ▸ small) dout dpins
    apply hx
    have eq := run (old (row flip x)) (start x) (oldLen _) (by simp [start]) (by
      intro k
      by_cases hk : k.val < 9
      · let j : Fin 9 := ⟨k.val,hk⟩
        have lhs := raw (row flip x) [edge (row flip x), pin p (row flip x) || pin q (row flip x)] j
        have rhs := raw x [edge x,x (left e) || x (right e)] (perm flip j)
        simpa only [old, start, label, dite_eq_left hk, row] using lhs.trans rhs.symm
      · have casesK : k = 9 ∨ k = 10 := by
          have := k.isLt
          rcases (show k.val = 9 ∨ k.val = 10 by omega) with h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Fin.ext h)
        rcases casesK with rfl | rfl
        · change (List.ofFn _ ++ [_,_]).getD 9 false = (List.ofFn _ ++ [_,_]).getD 9 false
          rw [at9,at9,fixedEdge]
        · change (List.ofFn _ ++ [_,_]).getD 10 false = (List.ofFn _ ++ [_,_]).getD 10 false
          rw [at10,at10,gate])
    exact eq.symm.trans ((correct (row flip x)).trans (invariant flip x))
  · let base (x : Fin 9 → Bool) := List.ofFn x ++ [false]
    have inactive (t : Fin 11) (ht : 9 ≤ t.val) (x) (h : edge x = false) : pin t x = false := by
      by_cases h9 : t.val = 9
      · change (List.ofFn x ++ [edge x]).getD t.val false = _
        rw [h9, at9, h]
      · exact List.getD_eq_default _ _ (by rw [seedLen]; omega)
    have choosePin : ∃ k : Fin 10, ∀ x, edge x = false →
        (pin p x || pin q x) = (base x).getD k.val false := by
      by_cases hp : p.val < 9
      · let a : Fin 9 := ⟨p.val,hp⟩
        refine ⟨⟨p.val, by omega⟩, fun x h => ?_⟩
        have pa : pin p x = x a := raw x [edge x] a
        have dst := raw x [false] a
        by_cases hq : q.val < 9
        · have same : p = q := Classical.not_not.mp (fun ne => proper ⟨hp,hq,ne⟩)
          rw [← same, Bool.or_self, pa]
          exact dst.symm
        · rw [inactive q (by omega) x h, Bool.or_false, pa]
          exact dst.symm
      · by_cases hq : q.val < 9
        · let b : Fin 9 := ⟨q.val,hq⟩
          refine ⟨⟨q.val, by omega⟩, fun x h => ?_⟩
          rw [inactive p (by omega) x h, Bool.false_or]
          exact (raw x [edge x] b).trans (raw x [false] b).symm
        · refine ⟨9, fun x h => ?_⟩
          rw [inactive p (by omega) x h, inactive q (by omega) x h]
          exact (at9 x false []).symm
    obtain ⟨k,hk⟩ := choosePin
    let label (z : Fin 11) : Fin 10 := if h : z.val < 10 then ⟨z.val,h⟩ else k
    obtain ⟨D,dfan,ds,_,_,run⟩ := normalize 10 (by decide) label
    have lower := promised D dfan (by
      intro x h
      have eq := run (old x) (base x) (oldLen x) (by simp [base]) (by
        intro z
        by_cases hz : z.val < 9
        · let j : Fin 9 := ⟨z.val,hz⟩
          have src := raw x [edge x,pin p x || pin q x] j
          have dst := raw x [false] j
          simpa only [label, dite_eq_left (show z.val < 10 by omega), old, base] using src.trans dst.symm
        · have zz := z.isLt
          rcases (show z = 9 ∨ z = 10 from
            (show z.val = 9 ∨ z.val = 10 by omega).imp (fun e => Fin.ext e) (fun e => Fin.ext e)) with rfl | rfl
          · change (List.ofFn x ++ [_,_]).getD 9 false = (List.ofFn x ++ [false]).getD 9 false
            rw [at9, at9]; exact h
          · change (List.ofFn x ++ [_,_]).getD 10 false = (base x).getD k.val false
            rw [at10]; exact hk x h)
      exact eq.symm.trans (correct x))
    omega
