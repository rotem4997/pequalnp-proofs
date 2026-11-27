import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4877_206
    (base : have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (62 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧         (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧           (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧ x4.output < 26+x4.size ∧ ∀ b : Bool, x4.eval (List.ofFn (fun i : Fin 26 => decide (i.val = if b = true then 13 else 0))) = false)
    (propagate : ∀ (n : ℕ) (C : Circuit) (s : ℕ) (x : List Bool), IsAO2 n C →
      ∃ d : ℕ → Bool, (∀ i < n, d i = decide (i=s)) ∧
        ∀ (j : ℕ) (g : Gate) (u v : ℕ), C.gates[j]? = some g → g.inputs=[u,v] →
        (g.op = .and → d (n+j) = ((C.wires x).getD u false && d v || d u && (C.wires x).getD v false)) ∧
        (g.op = .or → d (n+j) = (d u || d v))) :
    have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧         (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧           (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧             ∀ (x5 : Bool),               ∃ (x6 : ℕ → Bool),                 (∀ x7 < (26 : ℕ), x6 x7 = Decidable.decide (x7 = if x5 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ),                       x4.gates[x7]? = Option.some x8 →                         x8.inputs = [x9, x10] →                           have x13 : List Bool := x4.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ((26 : ℕ) + x7) = (x13.getD x9 Bool.false && x6 x10 || x6 x9 && x13.getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 ((26 : ℕ) + x7) = (x6 x9 || x6 x10))) ∧                     x6 x4.output = Bool.false := by
  intro miss pack unit
  obtain ⟨C,budget,ao,nd,pos,neg,valid,zeros⟩ := base
  let m := 26+C.size
  let z : ℕ := if C.output=1 then 2 else 1
  let A : Gate := ⟨.or,[C.output,z]⟩
  let B : Gate := ⟨.and,[C.output,m]⟩
  let D : Circuit := ⟨C.gates++[A,B],m+1⟩
  have lt : C.output < m := valid
  have small : z=1 ∨ z=2 := by by_cases h : C.output=1 <;> simp [z,h]
  have diff : C.output ≠ z := by by_cases h : C.output=1 <;> simp [z,h]
  have lg : C.gates.length = C.size := rfl
  have lm : 26 ≤ m := by dsimp [m]; omega
  have gate0 : gateAt D C.size = A := by
    change (C.gates++[A,B]).getD C.gates.length _=A
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp
  have gate1 : gateAt D (C.size+1) = B := by
    change (C.gates++[A,B]).getD (C.gates.length+1) _=B
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp
  have all (g : Gate) (hg : g∈D.gates) : g∈C.gates ∨ g=A ∨ g=B := by
    simpa [D] using hg
  have dao : IsAO2 26 D := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      rcases all g hg with old|rfl|rfl
      · exact ao.1 _ old
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro j hj i hi
      have jb : j < C.size+2 := by simpa [D,lg] using hj
      by_cases old : j < C.size
      · have same : gateAt D j = gateAt C j := List.getD_append _ _ _ _ old
        rw [same] at hi
        exact ao.2.1 _ old _ hi
      · rcases (show j=C.size ∨ j=C.size+1 by omega) with rfl|rfl
        · rw [gate0] at hi
          have h : i=C.output ∨ i=z := by simpa [A] using hi
          change i<m
          omega
        · rw [gate1] at hi
          have h : i=C.output ∨ i=m := by simpa [B] using hi
          dsimp [m] at lt ⊢
          dsimp [m] at h
          omega
    · intro g hg
      rcases all g hg with old|rfl|rfl
      · exact ao.2.2 _ old
      · rfl
      · rfl
  have dnd (g : Gate) (hg : g∈D.gates) : g.inputs.Nodup := by
    rcases all g hg with old|rfl|rfl
    · exact nd _ old
    · simp [A,diff]
    · simp [B,ne_of_lt lt]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons,List.length_cons,ih,step,List.length_append,
        List.length_cons,List.length_nil]; omega
  have wires (x : List Bool) (hx : x.length=26) :
      D.wires x = C.wires x ++ [C.eval x || (C.wires x).getD z false,C.eval x] := by
    let W := C.wires x
    let a := C.eval x || W.getD z false
    have wl : W.length = m := (len C.gates x).trans (by rw [hx,lg])
    have first : A.op.eval (A.inputs.map fun i => W.getD i false) = a := by
      change (W.getD C.output false || (W.getD z false || false)) = _
      change (W.getD C.output false || (W.getD z false || false)) =
        (W.getD C.output false || W.getD z false)
      simp
    have old : (W++[a]).getD C.output false = C.eval x := List.getD_append _ _ _ _ (by omega)
    have newg : (W++[a]).getD m false = a := by
      rw [List.getD_append_right _ _ _ _ (by omega),wl,Nat.sub_self]; rfl
    have last : B.op.eval (B.inputs.map fun i => (W++[a]).getD i false) = C.eval x := by
      change ((W++[a]).getD C.output false && ((W++[a]).getD m false && true)) = _
      rw [old,newg]
      cases c : C.eval x <;> simp [a,c]
    change (C.gates++[A,B]).foldl step x = W++[a,C.eval x]
    rw [List.foldl_append]
    change step (step W A) B = _
    have stepA : step W A = W++[a] := congrArg (fun t => W++[t]) first
    rw [stepA]
    change (W++[a])++[B.op.eval (B.inputs.map fun i => (W++[a]).getD i false)] = _
    rw [last]; simp
  have wl (x : List Bool) (hx : x.length=26) : (C.wires x).length = m :=
    (len C.gates x).trans (by rw [hx,lg])
  have ev (x : List Bool) (hx : x.length=26) : D.eval x = C.eval x := by
    change (D.wires x).getD (m+1) false=_
    rw [wires x hx,List.getD_append_right _ _ _ _ (by rw [wl x hx]; omega),wl x hx]
    simp
  have prefixW (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i<x.length) :
      (gs.foldl step x).getD i false = x.getD i false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have ds : D.size ≤ 64 := by
    change (C.gates++[A,B]).length ≤ 64
    simp only [List.length_append,List.length_cons,List.length_nil,lg]
    omega
  refine ⟨D,ds,dao,dnd,?_,?_,?_⟩
  · intro p l inc
    rw [ev _ (List.length_ofFn ..)]
    exact pos _ _ inc
  · intro x h
    rw [ev _ (List.length_ofFn ..),ev _ (List.length_ofFn ..)]
    exact neg x h
  · intro b
    let x := List.ofFn fun i : Fin 26 => decide (i.val = if b=true then 13 else 0)
    have hx : x.length=26 := List.length_ofFn ..
    obtain ⟨d,init,eqs⟩ := propagate 26 D (if b=true then 0 else 13) x dao
    refine ⟨d,init,eqs,?_⟩
    have zz : x.getD z false = false := by
      rcases small with h|h <;> rw [h] <;> cases b <;> decide
    have off : C.eval x=false := zeros b
    have offz : (C.wires x).getD z false=false := (prefixW C.gates x z (by omega)).trans zz
    have off0 : (D.wires x).getD C.output false=false := by
      rw [wires x hx,List.getD_append _ _ _ _ (by rw [wl x hx]; omega)]
      exact off
    have off1 : (D.wires x).getD m false=false := by
      rw [wires x hx,List.getD_append_right _ _ _ _ (by rw [wl x hx]),wl x hx,Nat.sub_self]
      change (C.eval x || (C.wires x).getD z false)=false
      rw [off,offz]; rfl
    have getB : D.gates[C.size+1]? = some B := by
      change (C.gates++[A,B])[C.gates.length+1]? = _
      rw [List.getElem?_append_right (by omega)]; simp
    have eq := (eqs _ B C.output m getB rfl).1 rfl
    rw [off0,off1] at eq
    simpa [D,m,Nat.add_assoc] using eq

