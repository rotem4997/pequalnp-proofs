import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Normalize repeated marked inputs into a formula while preserving both degree lower bounds.
-- Formula rigidity is purely combinatorial. Sensitivity is a separate statement about arbitrary binary gates.
theorem PEqualNP.Outside.R_meta_1480_873
    (normalize : let inc := fun p l : Fin 7 => p=l ∨ p=l+1 ∨ p=l+3
      let valid := fun C : Circuit => C.size ≤ 27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 7, inc p l ∧
          x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
      let tree := fun C : Circuit => ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup
      ∀ (C : Circuit) (p l : Fin 7), valid C → inc p l →
        2≤C.lineDeg 14 {p.val} → 2≤C.lineDeg 14 {7+l.val} →
        ∃ D : Circuit, valid D ∧ tree D ∧ 2≤D.lineDeg 14 {p.val} ∧ 2≤D.lineDeg 14 {7+l.val})
    (rigidity : let inc := fun p l : Fin 7 => p=l ∨ p=l+1 ∨ p=l+3
      let valid := fun C : Circuit => C.size ≤ 27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 7, inc p l ∧
          x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
      let tree := fun C : Circuit => ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup
      ∀ (C : Circuit) (p l : Fin 7), valid C → tree C → inc p l →
        HasLineDegree 14 {p.val} C 1 ∨ HasLineDegree 14 {7+l.val} C 1)
    (sensitivity : ∀ (C : Circuit) (i : Fin 14) (x : Fin 14 → Bool) (d : ℕ → Bool),
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) →
      (∀ j : Fin 14, d j.val = decide (i=j)) →
      (∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]?=some g → g.inputs=[a,b] →
        (g.op=GateOp.and → d (14+k) = ((((C.wires (List.ofFn x)).getD a false) && d b) ||
          (d a && ((C.wires (List.ofFn x)).getD b false)))) ∧
        (g.op=GateOp.or → d (14+k)=(d a || d b))) →
      C.eval (List.ofFn x)=false →
      C.eval (List.ofFn (fun j => if i=j then true else x j))=true →
      d C.output=false → 2≤C.lineDeg 14 {i.val})
    : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  rintro ⟨C,small,shape,correct,p,l,incident,⟨v,vi,vg,vo⟩,⟨w,wi,wg,wo⟩⟩
  let a := Fin.castAdd 7 p
  let b := Fin.natAdd 7 l
  let one := fun k j : Fin 14 => decide (j=k)
  have table : ∀ p l u : Fin 7,
      decide (Fin.castAdd 7 p=Fin.castAdd 7 u)=decide (u=p) ∧
      decide (Fin.natAdd 7 l=Fin.natAdd 7 u)=decide (u=l) ∧
      decide (Fin.castAdd 7 p=Fin.natAdd 7 u)=false ∧
      decide (Fin.natAdd 7 l=Fin.castAdd 7 u)=false := by decide +kernel
  have v0 (j : Fin 14) : v j.val=decide (b=j) := by
    apply Fin.addCases (motive:=fun j => v j.val=decide (b=j)) _ _ j
    · intro u; exact (vi u).1.trans (table p l u).2.2.2.symm
    · intro u; exact (vi u).2.trans (table p l u).2.1.symm
  have w0 (j : Fin 14) : w j.val=decide (a=j) := by
    apply Fin.addCases (motive:=fun j => w j.val=decide (a=j)) _ _ j
    · intro u; exact (wi u).1.trans (table p l u).1.symm
    · intro u; exact (wi u).2.trans (table p l u).2.2.1.symm
  have off (i : Fin 14) : C.eval (List.ofFn (one i))=false := by
    cases h : C.eval (List.ofFn (one i)) with
    | false => rfl
    | true =>
      obtain ⟨u,t,_,hu,ht⟩ := (correct _).mp h
      have eq := (of_decide_eq_true hu).trans (of_decide_eq_true ht).symm
      have abs : ∀ u t : Fin 7, Fin.castAdd 7 u ≠ Fin.natAdd 7 t := by decide
      exact False.elim (abs u t eq)
  have on1 : C.eval (List.ofFn (fun j => if a=j then true else one b j))=true := by
    apply (correct _).mpr
    exact ⟨p,l,incident,by simp [a],by simp [b,one]⟩
  have on2 : C.eval (List.ofFn (fun j => if b=j then true else one a j))=true := by
    apply (correct _).mpr
    exact ⟨p,l,incident,by simp [a,one],by simp [b]⟩
  have da := sensitivity C a (one b) w shape w0 wg (off b) on1 wo
  have db := sensitivity C b (one a) v shape v0 vg (off a) on2 vo
  obtain ⟨D,valid,unshared,dp,dl⟩ := normalize C p l ⟨small,shape,correct⟩ incident da db
  obtain h|h := rigidity D p l valid unshared incident
  · change D.lineDeg 14 {p.val}≤1 at h
    omega
  · change D.lineDeg 14 {7+l.val}≤1 at h
    omega
