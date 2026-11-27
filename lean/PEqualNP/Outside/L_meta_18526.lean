import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18526

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def address {n : ℕ} (f : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else i

private def remap {n : ℕ} (f : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (address f)⟩

private def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem agrees {n : ℕ} (f : Fin n → Fin n) (x : Fin n → Bool)
    (bank : List Bool) (i : ℕ) :
    (List.ofFn x ++ bank).getD (address f i) false =
      (List.ofFn (x ∘ f) ++ bank).getD i false := by
  unfold address
  split
  · rename_i hi
    have hleft : (f ⟨i, hi⟩).val < (List.ofFn x).length := by simp
    have hright : i < (List.ofFn (x ∘ f)).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_append _ _ _ _ hleft, List.getD_append _ _ _ _ hright,
      List.getD_eq_getElem _ _ hleft, List.getD_eq_getElem _ _ hright]
    simp only [List.getElem_ofFn, Fin.eta, Function.comp_apply]
  · rename_i hi
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi)]
    simp

private theorem simulate {n : ℕ} (f : Fin n → Fin n) (x : Fin n → Bool)
    (gs : List Gate) (bank : List Bool) (i : ℕ) :
    ((gs.map (remap f)).foldl advance (List.ofFn x ++ bank)).getD (address f i) false =
      (gs.foldl advance (List.ofFn (x ∘ f) ++ bank)).getD i false := by
  induction gs generalizing bank with
  | nil => exact agrees f x bank i
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun k => (List.ofFn (x ∘ f) ++ bank).getD k false)
    have he :
        (remap f g).op.eval
          ((remap f g).inputs.map fun k => (List.ofFn x ++ bank).getD k false) = b := by
      simp only [remap, b, List.map_map]
      congr 1
      exact List.map_congr_left (fun k _ => agrees f x bank k)
    simpa only [List.map_cons, List.foldl_cons, advance, he, List.append_assoc, b] using ih (bank ++ [b])

theorem result (n : ℕ) (f : Fin n → Fin n) (C : Circuit) (hC : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ f)) := by
  refine ⟨⟨C.gates.map (remap f), address f C.output⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    simpa only [remap, List.length_map] using hC q hq
  · intro x
    change ((C.gates.map (remap f)).foldl advance (List.ofFn x)).getD (address f C.output) false =
      (C.gates.foldl advance (List.ofFn (x ∘ f))).getD C.output false
    simpa only [List.append_nil] using simulate f x C.gates [] C.output

end PEqualNP.Outside.L_meta_18526

theorem PEqualNP.Outside.L_meta_18526 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool), x5.eval (List.ofFn x6) = x3.eval (List.ofFn (x6 ∘ x2)) := PEqualNP.Outside.L_meta_18526.result
