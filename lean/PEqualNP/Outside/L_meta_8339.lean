import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8339_aux

open PEqualNP.CircuitLowerBounds

def cg (N : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i N)⟩

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

theorem key {α : Type} (N : ℕ) (w : List α) (z : α) (h : w.length ≤ N) (i : ℕ) :
    w.getD (min i N) z = w.getD i z := by
  by_cases hi : i ≤ N
  · rw [Nat.min_eq_left hi]
  · have h1 : w.length ≤ min i N := by omega
    have h2 : w.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]

theorem fold (N : ℕ) (gs : List Gate) :
    ∀ w : List Bool, w.length + gs.length ≤ N →
      (gs.map (cg N)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
        = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w h; rfl
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    have e : (cg N g).op.eval ((cg N g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [cg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact key N w false (by omega) i
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e]
    exact ih _ (by simp; omega)

theorem gate_eq (g : Gate) (h1 : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (h2 : g.inputs.length ≤ 2) :
    ({ op := if isAnd g.op = true then GateOp.and else GateOp.or,
       inputs := List.map Fin.val
         ((g.inputs[0]?.map (fun i => (⟨min i 39, by omega⟩ : Fin 40))).toList ++
          (g.inputs[1]?.map (fun i => (⟨min i 39, by omega⟩ : Fin 40))).toList) } : Gate)
      = cg 39 g := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  simp only at h2
  simp only [cg]
  congr 1
  · rcases h1 with h | h <;> subst h <;> rfl
  · match ins, h2 with
    | [], _ => rfl
    | [a], _ => rfl
    | [a, b], _ => rfl
    | a :: b :: c :: l, h => simp at h

end PEqualNP.Outside.L_meta_8339_aux

open PEqualNP.Outside.L_meta_8339_aux in
theorem PEqualNP.Outside.L_meta_8339 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (25 : ℕ) →       ∃ (x4 : Fin (26 : ℕ)) (x5 : Fin ↑x4 → Bool) (x6 : Fin ↑x4 → Option (Fin (40 : ℕ)) × Option (Fin (40 : ℕ))),         have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin ↑x4) => { op := if x5 x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val ((x6 x7).1.toList ++ (x6 x7).2.toList) : PEqualNP.CircuitLowerBounds.Gate }, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };         ∀ (x8 : Fin (14 : ℕ) → Bool), x7.wires (List.ofFn x8) = x1.wires (List.ofFn x8) := by
  intro C hM hs
  have hs2 : C.gates.length ≤ 25 := hs
  refine ⟨⟨C.gates.length, by omega⟩,
    fun j => isAnd (C.gates[j.1]'j.2).op,
    fun j => ((C.gates[j.1]'j.2).inputs[0]?.map (fun i => (⟨min i 39, by omega⟩ : Fin 40)),
      (C.gates[j.1]'j.2).inputs[1]?.map (fun i => (⟨min i 39, by omega⟩ : Fin 40))), ?_⟩
  have hg : (List.ofFn fun (j : Fin C.gates.length) =>
      ({ op := if isAnd (C.gates[j.1]'j.2).op = true then PEqualNP.CircuitLowerBounds.GateOp.and
              else PEqualNP.CircuitLowerBounds.GateOp.or,
         inputs := List.map Fin.val
           (((C.gates[j.1]'j.2).inputs[0]?.map (fun i => (⟨min i 39, by omega⟩ : Fin 40))).toList ++
            ((C.gates[j.1]'j.2).inputs[1]?.map (fun i => (⟨min i 39, by omega⟩ : Fin 40))).toList) }
        : PEqualNP.CircuitLowerBounds.Gate)) = C.gates.map (cg 39) := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      have hm := hM _ (List.getElem_mem (l := C.gates) (n := n) (by simpa using h1))
      exact gate_eq _ hm.1 hm.2
  simp only []
  intro x
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  simp only []
  rw [hg]
  exact fold 39 C.gates (List.ofFn x) (by simp; omega)
