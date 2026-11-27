import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2071_1
    (htrack :
    let step := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 26) (u v : ℕ) =>
      ∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (q : ℕ),
        v = 26 + k ∧ C.gates[k]? = some g ∧
        (g.inputs = [u, q] ∨ g.inputs = [q, u]) ∧
        (g.op = .or ∨ g.op = .and ∧
          (C.wires (List.ofFn fun i : Fin 26 => decide (i = a))).getD q false = true)
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 26) (s : ℕ) (d : ℕ → Bool),
      let w := C.wires (List.ofFn fun i : Fin 26 => decide (i = a))
      d s = true →
      (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (u v : ℕ),
        C.gates[k]? = some g → g.inputs = [u, v] →
        (g.op = .and → d (26 + k) = (w.getD u false && d v || d u && w.getD v false)) ∧
        (g.op = .or → d (26 + k) = (d u || d v))) →
      Relation.ReflTransGen (step C a) s C.output → d C.output = true)
    (hnormalize :
    let step := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 26) (u v : ℕ) =>
      ∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (q : ℕ),
        v = 26 + k ∧ C.gates[k]? = some g ∧
        (g.inputs = [u, q] ∨ g.inputs = [q, u]) ∧
        (g.op = .or ∨ g.op = .and ∧
          (C.wires (List.ofFn fun i : Fin 26 => decide (i = a))).getD q false = true)
    let shifts : Finset (Fin 13) := {0, 1, 3, 9}
    let good := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.size ≤ 64 ∧
      PEqualNP.TopForm.IsAO2 26 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ shifts ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
      0 < PEqualNP.TopForm.andPairs 26 C ∧
      (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = .and ∧
        ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧
          C.eval (List.ofFn x) = false)
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (p l : Fin 13), good C →
      p - l ∈ shifts →
      ¬ Relation.ReflTransGen (step C (Fin.castAdd 13 p)) (13 + l.val) C.output →
      ¬ Relation.ReflTransGen (step C (Fin.natAdd 13 l)) p.val C.output →
      ∃ D, good D ∧
        ¬ Relation.ReflTransGen (step D 0) 13 D.output ∧
        ¬ Relation.ReflTransGen (step D 13) 0 D.output)
    (hcanonical :
    let step := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 26) (u v : ℕ) =>
      ∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (q : ℕ),
        v = 26 + k ∧ C.gates[k]? = some g ∧
        (g.inputs = [u, q] ∨ g.inputs = [q, u]) ∧
        (g.op = .or ∨ g.op = .and ∧
          (C.wires (List.ofFn fun i : Fin 26 => decide (i = a))).getD q false = true)
    let shifts : Finset (Fin 13) := {0, 1, 3, 9}
    let good := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.size ≤ 64 ∧
      PEqualNP.TopForm.IsAO2 26 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p - l ∈ shifts ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
      0 < PEqualNP.TopForm.andPairs 26 C ∧
      (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = .and ∧
        ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = true ∧
          C.eval (List.ofFn x) = false)
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), good C →
      Relation.ReflTransGen (step C 0) 13 C.output ∨
      Relation.ReflTransGen (step C 13) 0 C.output) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∃ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 ∧ ∃ (x15 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x15)).getD ((26 : ℕ) + x14) Bool.false = Bool.true ∧ x4.eval (List.ofFn x15) = Bool.false) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  let step := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 26) (u v : ℕ) =>
    ∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (q : ℕ),
      v = 26 + k ∧ C.gates[k]? = some g ∧
      (g.inputs = [u, q] ∨ g.inputs = [q, u]) ∧
      (g.op = .or ∨ g.op = .and ∧
        (C.wires (List.ofFn fun i : Fin 26 => decide (i = a))).getD q false = true)
  intro C p l left right hsize hgates heval hnested hdirty hinc hleft hright
  by_cases hl : Relation.ReflTransGen (step C (Fin.castAdd 13 p)) (13 + l.val) C.output
  · left
    apply htrack C (Fin.castAdd 13 p) (13 + l.val) left ?_ hleft.2 hl
    have hlt : 13 + l.val < 26 := by have := l.isLt; omega
    simpa using hleft.1 (13 + l.val) hlt
  by_cases hr : Relation.ReflTransGen (step C (Fin.natAdd 13 l)) p.val C.output
  · right
    apply htrack C (Fin.natAdd 13 l) p.val right ?_ hright.2 hr
    simpa using hright.1 p.val (by have := p.isLt; omega)
  have hgateFacts (g : PEqualNP.CircuitLowerBounds.Gate) (hm : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    obtain ⟨hop, u, v, hargs, hne, _, _⟩ := hgates k g hk
    exact ⟨hop, by simp [hargs], by simp [hargs, hne]⟩
  have hshape : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨fun g hm => (hgateFacts g hm).1, ?_, fun g hm => (hgateFacts g hm).2.1⟩
    intro k hk w hw
    have hgate : C.gates[k]? = some C.gates[k] := by simp [hk]
    obtain ⟨_, u, v, hargs, _, hu, hv⟩ := hgates k C.gates[k] hgate
    change w ∈ (C.gates.getD k ⟨.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem _ _ hk, hargs] at hw
    simp at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  have hdistinct : ∀ g ∈ C.gates, g.inputs.Nodup := fun g hm => (hgateFacts g hm).2.2
  obtain ⟨D, hgood, hnl, hnr⟩ :=
    hnormalize C p l ⟨hsize, hshape, hdistinct, heval, hnested, hdirty⟩ hinc hl hr
  exact False.elim ((hcanonical D hgood).elim hnl hnr)
