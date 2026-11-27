import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8207_aux

open PEqualNP.CircuitLowerBounds

def G (n o : ℕ) : List Gate := [
    ⟨GateOp.or, [7, 8]⟩,
  ⟨GateOp.or, [n + 0, 10]⟩,
  ⟨GateOp.or, [n + 1, 3]⟩,
  ⟨GateOp.and, [n + 2, 20]⟩,
  ⟨GateOp.or, [8, 9]⟩,
  ⟨GateOp.or, [n + 4, 11]⟩,
  ⟨GateOp.or, [n + 5, 4]⟩,
  ⟨GateOp.and, [n + 6, 21]⟩,
  ⟨GateOp.or, [9, 10]⟩,
  ⟨GateOp.or, [n + 8, 12]⟩,
  ⟨GateOp.or, [n + 9, 5]⟩,
  ⟨GateOp.and, [n + 10, 22]⟩,
  ⟨GateOp.or, [10, 11]⟩,
  ⟨GateOp.or, [n + 12, 0]⟩,
  ⟨GateOp.or, [n + 13, 6]⟩,
  ⟨GateOp.and, [n + 14, 23]⟩,
  ⟨GateOp.or, [11, 12]⟩,
  ⟨GateOp.or, [n + 16, 1]⟩,
  ⟨GateOp.or, [n + 17, 7]⟩,
  ⟨GateOp.and, [n + 18, 24]⟩,
  ⟨GateOp.or, [12, 0]⟩,
  ⟨GateOp.or, [n + 20, 2]⟩,
  ⟨GateOp.or, [n + 21, 8]⟩,
  ⟨GateOp.and, [n + 22, 25]⟩,
  ⟨GateOp.or, [o, n + 3]⟩,
  ⟨GateOp.or, [n + 24, n + 7]⟩,
  ⟨GateOp.or, [n + 25, n + 11]⟩,
  ⟨GateOp.or, [n + 26, n + 15]⟩,
  ⟨GateOp.or, [n + 27, n + 19]⟩,
  ⟨GateOp.or, [n + 28, n + 23]⟩]

theorem gmono (n o : ℕ) : ∀ g ∈ G n o, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [G]

theorem glen (n o : ℕ) : (G n o).length = 30 := by simp [G]

theorem gread (n o : ℕ) (ho : o < n) (h26 : 26 ≤ n) : ∀ k < (G n o).length, ∀ i ∈ ((G n o).getD k ⟨GateOp.or, []⟩).inputs, i < n + k := by
  intro k hk i hi
  rw [glen] at hk
  interval_cases k <;> simp [G] at hi <;> omega

theorem fold_pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by simp only [List.foldl]; rw [ht, List.append_assoc]⟩

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl]; rw [ih]; simp; omega

theorem pre (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD i false = W.getD i false := by
  obtain ⟨t, ht⟩ := fold_pre gs W
  rw [ht, List.getD_append _ _ _ _ hi]

theorem fget (gs : List Gate) : ∀ W : List Bool, (∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, i < W.length + k) →
    ∀ k < gs.length, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD (W.length + k) false =
      (gs.getD k ⟨GateOp.or, []⟩).op.eval ((gs.getD k ⟨GateOp.or, []⟩).inputs.map fun i =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD i false) := by
  induction gs with
  | nil => intro W _ k hk; simp at hk
  | cons g gs ih =>
    intro W hR k hk
    simp only [List.foldl]
    cases k with
    | zero =>
      rw [Nat.add_zero, pre gs _ W.length (by simp)]
      simp only [List.getD_cons_zero]
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp only [List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      have := hR 0 (by simp) i (by simpa using hi)
      rw [pre gs _ i (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    | succ k =>
      simp only [List.getD_cons_succ]
      have h := ih (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) (by
        intro k' hk' i hi
        have := hR (k' + 1) (by simp; omega) i (by simpa using hi)
        simp; omega) k (by simp at hk; omega)
      have hl : (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).length + k = W.length + (k + 1) := by simp; omega
      rw [hl] at h
      exact h

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size := by
  unfold Circuit.wires Circuit.size; exact fold_len _ _

theorem wires_in (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  unfold Circuit.wires
  obtain ⟨t, ht⟩ := fold_pre C.gates (List.ofFn x)
  rw [ht, List.getD_append _ _ _ _ (by simp)]
  simp

theorem inp (C : Circuit) (x9 : Fin 26 → Bool) (i : Fin 26) :
    (C.wires (List.ofFn (fun j : Fin (26 + 1) => Fin.lastCases (x9 0 || x9 1) x9 j))).getD i.val false = x9 i := by
  rw [show i.val = (Fin.castSucc i).val from rfl, wires_in]
  simp

theorem key (W : List Bool) (o : ℕ) (ho : o < W.length) (h26 : 26 ≤ W.length) :
    ((G W.length o).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD (W.length + 29) false =
      (W.getD o false || ((W.getD 7 false || W.getD 8 false || W.getD 10 false || W.getD 3 false) && W.getD 20 false) || ((W.getD 8 false || W.getD 9 false || W.getD 11 false || W.getD 4 false) && W.getD 21 false) || ((W.getD 9 false || W.getD 10 false || W.getD 12 false || W.getD 5 false) && W.getD 22 false) || ((W.getD 10 false || W.getD 11 false || W.getD 0 false || W.getD 6 false) && W.getD 23 false) || ((W.getD 11 false || W.getD 12 false || W.getD 1 false || W.getD 7 false) && W.getD 24 false) || ((W.getD 12 false || W.getD 0 false || W.getD 2 false || W.getD 8 false) && W.getD 25 false)) := by
  have e := fget (G W.length o) W (gread W.length o ho h26)
  have hp := pre (G W.length o) W
  generalize (G W.length o).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W = F at e hp ⊢
  have e0 : F.getD (W.length + 0) false = (F.getD 7 false || (F.getD 8 false || false)) := e 0 (by simp [G])
  have e1 : F.getD (W.length + 1) false = (F.getD (W.length + 0) false || (F.getD 10 false || false)) := e 1 (by simp [G])
  have e2 : F.getD (W.length + 2) false = (F.getD (W.length + 1) false || (F.getD 3 false || false)) := e 2 (by simp [G])
  have e3 : F.getD (W.length + 3) false = (F.getD (W.length + 2) false && (F.getD 20 false && true)) := e 3 (by simp [G])
  have e4 : F.getD (W.length + 4) false = (F.getD 8 false || (F.getD 9 false || false)) := e 4 (by simp [G])
  have e5 : F.getD (W.length + 5) false = (F.getD (W.length + 4) false || (F.getD 11 false || false)) := e 5 (by simp [G])
  have e6 : F.getD (W.length + 6) false = (F.getD (W.length + 5) false || (F.getD 4 false || false)) := e 6 (by simp [G])
  have e7 : F.getD (W.length + 7) false = (F.getD (W.length + 6) false && (F.getD 21 false && true)) := e 7 (by simp [G])
  have e8 : F.getD (W.length + 8) false = (F.getD 9 false || (F.getD 10 false || false)) := e 8 (by simp [G])
  have e9 : F.getD (W.length + 9) false = (F.getD (W.length + 8) false || (F.getD 12 false || false)) := e 9 (by simp [G])
  have e10 : F.getD (W.length + 10) false = (F.getD (W.length + 9) false || (F.getD 5 false || false)) := e 10 (by simp [G])
  have e11 : F.getD (W.length + 11) false = (F.getD (W.length + 10) false && (F.getD 22 false && true)) := e 11 (by simp [G])
  have e12 : F.getD (W.length + 12) false = (F.getD 10 false || (F.getD 11 false || false)) := e 12 (by simp [G])
  have e13 : F.getD (W.length + 13) false = (F.getD (W.length + 12) false || (F.getD 0 false || false)) := e 13 (by simp [G])
  have e14 : F.getD (W.length + 14) false = (F.getD (W.length + 13) false || (F.getD 6 false || false)) := e 14 (by simp [G])
  have e15 : F.getD (W.length + 15) false = (F.getD (W.length + 14) false && (F.getD 23 false && true)) := e 15 (by simp [G])
  have e16 : F.getD (W.length + 16) false = (F.getD 11 false || (F.getD 12 false || false)) := e 16 (by simp [G])
  have e17 : F.getD (W.length + 17) false = (F.getD (W.length + 16) false || (F.getD 1 false || false)) := e 17 (by simp [G])
  have e18 : F.getD (W.length + 18) false = (F.getD (W.length + 17) false || (F.getD 7 false || false)) := e 18 (by simp [G])
  have e19 : F.getD (W.length + 19) false = (F.getD (W.length + 18) false && (F.getD 24 false && true)) := e 19 (by simp [G])
  have e20 : F.getD (W.length + 20) false = (F.getD 12 false || (F.getD 0 false || false)) := e 20 (by simp [G])
  have e21 : F.getD (W.length + 21) false = (F.getD (W.length + 20) false || (F.getD 2 false || false)) := e 21 (by simp [G])
  have e22 : F.getD (W.length + 22) false = (F.getD (W.length + 21) false || (F.getD 8 false || false)) := e 22 (by simp [G])
  have e23 : F.getD (W.length + 23) false = (F.getD (W.length + 22) false && (F.getD 25 false && true)) := e 23 (by simp [G])
  have e24 : F.getD (W.length + 24) false = (F.getD o false || (F.getD (W.length + 3) false || false)) := e 24 (by simp [G])
  have e25 : F.getD (W.length + 25) false = (F.getD (W.length + 24) false || (F.getD (W.length + 7) false || false)) := e 25 (by simp [G])
  have e26 : F.getD (W.length + 26) false = (F.getD (W.length + 25) false || (F.getD (W.length + 11) false || false)) := e 26 (by simp [G])
  have e27 : F.getD (W.length + 27) false = (F.getD (W.length + 26) false || (F.getD (W.length + 15) false || false)) := e 27 (by simp [G])
  have e28 : F.getD (W.length + 28) false = (F.getD (W.length + 27) false || (F.getD (W.length + 19) false || false)) := e 28 (by simp [G])
  have e29 : F.getD (W.length + 29) false = (F.getD (W.length + 28) false || (F.getD (W.length + 23) false || false)) := e 29 (by simp [G])
  have p0 : F.getD 0 false = W.getD 0 false := hp 0 (by omega)
  have p1 : F.getD 1 false = W.getD 1 false := hp 1 (by omega)
  have p2 : F.getD 2 false = W.getD 2 false := hp 2 (by omega)
  have p3 : F.getD 3 false = W.getD 3 false := hp 3 (by omega)
  have p4 : F.getD 4 false = W.getD 4 false := hp 4 (by omega)
  have p5 : F.getD 5 false = W.getD 5 false := hp 5 (by omega)
  have p6 : F.getD 6 false = W.getD 6 false := hp 6 (by omega)
  have p7 : F.getD 7 false = W.getD 7 false := hp 7 (by omega)
  have p8 : F.getD 8 false = W.getD 8 false := hp 8 (by omega)
  have p9 : F.getD 9 false = W.getD 9 false := hp 9 (by omega)
  have p10 : F.getD 10 false = W.getD 10 false := hp 10 (by omega)
  have p11 : F.getD 11 false = W.getD 11 false := hp 11 (by omega)
  have p12 : F.getD 12 false = W.getD 12 false := hp 12 (by omega)
  have p20 : F.getD 20 false = W.getD 20 false := hp 20 (by omega)
  have p21 : F.getD 21 false = W.getD 21 false := hp 21 (by omega)
  have p22 : F.getD 22 false = W.getD 22 false := hp 22 (by omega)
  have p23 : F.getD 23 false = W.getD 23 false := hp 23 (by omega)
  have p24 : F.getD 24 false = W.getD 24 false := hp 24 (by omega)
  have p25 : F.getD 25 false = W.getD 25 false := hp 25 (by omega)
  rw [e29, e28, e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p20, p21, p22, p23, p24, p25, hp o ho]
  simp only [Bool.or_false, Bool.and_true]

theorem sem (o : Bool) (x9 : Fin 26 → Bool) :
    (o || ((x9 7 || x9 8 || x9 10 || x9 3) && x9 20) || ((x9 8 || x9 9 || x9 11 || x9 4) && x9 21) || ((x9 9 || x9 10 || x9 12 || x9 5) && x9 22) || ((x9 10 || x9 11 || x9 0 || x9 6) && x9 23) || ((x9 11 || x9 12 || x9 1 || x9 7) && x9 24) || ((x9 12 || x9 0 || x9 2 || x9 8) && x9 25)) = true ↔ o = true ∨ ∃ (x10 : Fin 13) (x11 : Fin 13), (7 : ℕ) ≤ ↑x11 ∧ (∃ x4 ∈ ({(0 : Fin 13), (1 : Fin 13), (3 : Fin 13), (9 : Fin 13)} : Finset (Fin 13)), x10 = x11 + x4) ∧ x9 (Fin.castAdd 13 x10) = true ∧ x9 (Fin.natAdd 13 x11) = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    rcases h with ((((((h | ⟨(((h | h) | h) | h), h'⟩) | ⟨(((h | h) | h) | h), h'⟩) | ⟨(((h | h) | h) | h), h'⟩) | ⟨(((h | h) | h) | h), h'⟩) | ⟨(((h | h) | h) | h), h'⟩) | ⟨(((h | h) | h) | h), h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(7 : Fin 13), (7 : Fin 13), by decide, ⟨0, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(8 : Fin 13), (7 : Fin 13), by decide, ⟨1, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(10 : Fin 13), (7 : Fin 13), by decide, ⟨3, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(3 : Fin 13), (7 : Fin 13), by decide, ⟨9, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(8 : Fin 13), (8 : Fin 13), by decide, ⟨0, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(9 : Fin 13), (8 : Fin 13), by decide, ⟨1, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(11 : Fin 13), (8 : Fin 13), by decide, ⟨3, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(4 : Fin 13), (8 : Fin 13), by decide, ⟨9, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(9 : Fin 13), (9 : Fin 13), by decide, ⟨0, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(10 : Fin 13), (9 : Fin 13), by decide, ⟨1, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(12 : Fin 13), (9 : Fin 13), by decide, ⟨3, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(5 : Fin 13), (9 : Fin 13), by decide, ⟨9, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(10 : Fin 13), (10 : Fin 13), by decide, ⟨0, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(11 : Fin 13), (10 : Fin 13), by decide, ⟨1, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(0 : Fin 13), (10 : Fin 13), by decide, ⟨3, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(6 : Fin 13), (10 : Fin 13), by decide, ⟨9, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(11 : Fin 13), (11 : Fin 13), by decide, ⟨0, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(12 : Fin 13), (11 : Fin 13), by decide, ⟨1, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(1 : Fin 13), (11 : Fin 13), by decide, ⟨3, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(7 : Fin 13), (11 : Fin 13), by decide, ⟨9, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(12 : Fin 13), (12 : Fin 13), by decide, ⟨0, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(0 : Fin 13), (12 : Fin 13), by decide, ⟨1, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(2 : Fin 13), (12 : Fin 13), by decide, ⟨3, by decide, by decide⟩, h, h'⟩
    · exact Or.inr ⟨(8 : Fin 13), (12 : Fin 13), by decide, ⟨9, by decide, by decide⟩, h, h'⟩
  · rintro (h | ⟨x10, x11, h7, ⟨d, hd, rfl⟩, ha, hb⟩)
    · simp [h]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      fin_cases x11 <;> simp at h7 <;> rcases hd with rfl | rfl | rfl | rfl <;> simp_all

end PEqualNP.Outside.L_meta_8207_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_8207_aux in
theorem PEqualNP.Outside.L_meta_8207 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) (x4 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))) x3 x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x4 → x4.output < (27 : ℕ) + x4.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x8 ∧ x8.size ≤ x4.size + (30 : ℕ) ∧ ∀ (x9 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x8 (x3 x9) = Bool.true ↔ PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x4 (x3 x9) = Bool.true ∨ ∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), (7 : ℕ) ≤ ↑x11 ∧ x2 x10 x11 ∧ x9 (Fin.castAdd (13 : ℕ) x10) = Bool.true ∧ x9 (Fin.natAdd (13 : ℕ) x11) = Bool.true := by
  dsimp only
  intro x4 hm hr ho
  have hs : x4.size = x4.gates.length := rfl
  refine ⟨⟨x4.gates ++ G (27 + x4.size) x4.output, 27 + x4.size + 29⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hm g hg
    · exact gmono _ _ g hg
  · intro j hj i hi
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    simp only [List.length_append, glen] at hj
    by_cases hjl : j < x4.gates.length
    · rw [List.getD_append _ _ _ _ hjl] at hi
      have := hr j hjl i hi
      omega
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have := gread (27 + x4.size) x4.output ho (by omega) (j - x4.gates.length) (by rw [glen]; omega) i hi
      omega
  · simp [Circuit.size, glen]
  · intro x9
    unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
    generalize hX : List.ofFn (fun j : Fin (26 + 1) => Fin.lastCases (motive := fun _ => Bool) (x9 0 || x9 1) x9 j) = X
    have hw : Circuit.wires ⟨x4.gates ++ G (27 + x4.size) x4.output, 27 + x4.size + 29⟩ X =
        (G (27 + x4.size) x4.output).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (x4.wires X) := by
      unfold Circuit.wires; rw [List.foldl_append]
    have hl : (x4.wires X).length = 27 + x4.size := by rw [wires_len, ← hX]; simp
    simp only [hw]
    rw [← hl, key _ _ (by omega) (by omega)]
    have i0 : (x4.wires X).getD 0 false = x9 0 := by rw [← hX]; exact inp x4 x9 0
    have i1 : (x4.wires X).getD 1 false = x9 1 := by rw [← hX]; exact inp x4 x9 1
    have i2 : (x4.wires X).getD 2 false = x9 2 := by rw [← hX]; exact inp x4 x9 2
    have i3 : (x4.wires X).getD 3 false = x9 3 := by rw [← hX]; exact inp x4 x9 3
    have i4 : (x4.wires X).getD 4 false = x9 4 := by rw [← hX]; exact inp x4 x9 4
    have i5 : (x4.wires X).getD 5 false = x9 5 := by rw [← hX]; exact inp x4 x9 5
    have i6 : (x4.wires X).getD 6 false = x9 6 := by rw [← hX]; exact inp x4 x9 6
    have i7 : (x4.wires X).getD 7 false = x9 7 := by rw [← hX]; exact inp x4 x9 7
    have i8 : (x4.wires X).getD 8 false = x9 8 := by rw [← hX]; exact inp x4 x9 8
    have i9 : (x4.wires X).getD 9 false = x9 9 := by rw [← hX]; exact inp x4 x9 9
    have i10 : (x4.wires X).getD 10 false = x9 10 := by rw [← hX]; exact inp x4 x9 10
    have i11 : (x4.wires X).getD 11 false = x9 11 := by rw [← hX]; exact inp x4 x9 11
    have i12 : (x4.wires X).getD 12 false = x9 12 := by rw [← hX]; exact inp x4 x9 12
    have i20 : (x4.wires X).getD 20 false = x9 20 := by rw [← hX]; exact inp x4 x9 20
    have i21 : (x4.wires X).getD 21 false = x9 21 := by rw [← hX]; exact inp x4 x9 21
    have i22 : (x4.wires X).getD 22 false = x9 22 := by rw [← hX]; exact inp x4 x9 22
    have i23 : (x4.wires X).getD 23 false = x9 23 := by rw [← hX]; exact inp x4 x9 23
    have i24 : (x4.wires X).getD 24 false = x9 24 := by rw [← hX]; exact inp x4 x9 24
    have i25 : (x4.wires X).getD 25 false = x9 25 := by rw [← hX]; exact inp x4 x9 25
    rw [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i20, i21, i22, i23, i24, i25]
    exact sem _ x9
