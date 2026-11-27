import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4671

def wire {n m : ℕ} (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else m + (i - n)

lemma wire_lt {n m i s : ℕ} (f : Fin n → Fin m) (hi : i < n + s) :
    wire f i < m + s := by
  unfold wire
  split
  · exact lt_of_lt_of_le (f _).isLt (Nat.le_add_right _ _)
  · omega

def renameGate {n m : ℕ} (f : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire f)⟩

abbrev step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma read_wire {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool)
    (tail : List Bool) (i : ℕ) :
    (List.ofFn x ++ tail).getD (wire f i) false =
      (List.ofFn (x ∘ f) ++ tail).getD i false := by
  by_cases h : i < n
  · rw [wire, dite_eq_left h,
        List.getD_append _ _ _ _ (by simp),
        List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h, Function.comp_def]
  · rw [wire, dite_eq_right h,
        List.getD_append_right _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt h)]
    simp

lemma fold_read {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool)
    (gs : List Gate) (tail : List Bool) (i : ℕ) :
    ((gs.map (renameGate f)).foldl step (List.ofFn x ++ tail)).getD (wire f i) false =
      (gs.foldl step (List.ofFn (x ∘ f) ++ tail)).getD i false := by
  induction gs generalizing tail with
  | nil => exact read_wire f x tail i
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun j => (List.ofFn (x ∘ f) ++ tail).getD j false)
    have value : (renameGate f g).op.eval ((renameGate f g).inputs.map
        fun j => (List.ofFn x ++ tail).getD j false) = b := by
      simp only [renameGate, List.map_map, b]
      congr 1
      exact List.map_congr_left (fun j _ => read_wire f x tail j)
    simp only [List.map_cons, List.foldl_cons, step, value, List.append_assoc]
    exact ih (tail ++ [b])

end PEqualNP.Outside.L_meta_4671

open PEqualNP.Outside.L_meta_4671

theorem PEqualNP.Outside.L_meta_4671 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size = x4.size ∧ x9.output < x2 + x9.size ∧ x10 < x2 + x9.size ∧ ∀ (x11 : Fin x2 → Bool), x9.eval (List.ofFn x11) = x4.eval (List.ofFn (x11 ∘ x3)) ∧ (x9.wires (List.ofFn x11)).getD x10 Bool.false = (x4.wires (List.ofFn (x11 ∘ x3))).getD x5 Bool.false := by
  intro n m f C u mono hout hu
  let D : Circuit := ⟨C.gates.map (renameGate f), wire f C.output⟩
  have size_eq : D.size = C.size := by simp [D, Circuit.size]
  refine ⟨D, wire f u, ?_, size_eq, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp (show g ∈ C.gates.map (renameGate f) from hg)
    simpa [renameGate] using mono g' hg'
  · rw [size_eq]
    exact wire_lt f hout
  · rw [size_eq]
    exact wire_lt f hu
  · intro x
    have reads (i : ℕ) : (D.wires (List.ofFn x)).getD (wire f i) false =
        (C.wires (List.ofFn (x ∘ f))).getD i false := by
      simpa only [D, Circuit.wires, List.append_nil] using fold_read f x C.gates [] i
    exact ⟨reads C.output, reads u⟩
