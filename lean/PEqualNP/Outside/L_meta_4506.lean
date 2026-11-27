import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4506

private def readIndex (offset limit i : ℕ) : ℕ :=
  if i < offset then i else if i = offset then limit else i - 1

private def rewire (offset limit : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (readIndex offset limit)⟩

private def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem redirected_read (front tail : List Bool) (limit i : ℕ)
    (hsize : front.length + tail.length ≤ limit) :
    (front ++ tail).getD (readIndex front.length limit i) false =
      (front ++ (false :: tail)).getD i false := by
  by_cases hlt : i < front.length
  · simp only [readIndex, ite_eq_left hlt]
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · by_cases heq : i = front.length
    · subst i
      have hz : (front ++ tail).getD limit false = false :=
        List.getD_eq_default (front ++ tail) false
        (by simpa only [List.length_append] using hsize)
      rw [readIndex, ite_eq_right hlt, ite_eq_left rfl, hz,
        List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · rw [readIndex, ite_eq_right hlt, ite_eq_right heq,
        List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      have hs : i - front.length = (i - 1 - front.length) + 1 := by omega
      rw [hs]
      rfl

private theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl appendGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, appendGate, List.length_append, List.length_cons, List.length_nil]
    omega

-- The two runs share the same tail. The original run keeps a false wire before that tail.
private theorem run_pair (front : List Bool) (limit : ℕ) (gs : List Gate) (tail : List Bool)
    (hsize : front.length + tail.length + gs.length ≤ limit) :
    ∃ ys : List Bool,
      (gs.map (rewire front.length limit)).foldl appendGate (front ++ tail) = front ++ ys ∧
      gs.foldl appendGate (front ++ (false :: tail)) = front ++ (false :: ys) ∧
      ys.length = tail.length + gs.length := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, rfl, rfl, by simp⟩
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => (front ++ (false :: tail)).getD i false)
    have hvalues : (g.inputs.map fun i =>
        (front ++ tail).getD (readIndex front.length limit i) false) =
        (g.inputs.map fun i => (front ++ (false :: tail)).getD i false) := by
      apply List.map_congr_left
      intro i _
      exact redirected_read front tail limit i (by omega)
    have h1 : appendGate (front ++ tail) (rewire front.length limit g) =
        front ++ (tail ++ [value]) := by
      simp only [appendGate, rewire, List.map_map, Function.comp_def, hvalues, List.append_assoc, value]
    have h2 : appendGate (front ++ (false :: tail)) g =
        front ++ (false :: (tail ++ [value])) := by
      simp only [appendGate, List.append_assoc, List.cons_append]
      rfl
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, h1, h2]
    obtain ⟨ys, hmap, horig, hlen⟩ := ih (tail ++ [value]) (by simp at *; omega)
    refine ⟨ys, hmap, horig, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
    omega

private theorem compose_with_false {n : ℕ} (A B : Circuit)
    (hA : FanInTwo A) (hB : FanInTwo B) (f : (Fin n → Bool) → Bool)
    (h : ∀ z : Fin n → Bool, B.eval (A.wires (List.ofFn z) ++ [false]) = f z) :
    HasCircuitSize n f (A.size + B.size) := by
  let offset := n + A.size
  let limit := offset + B.size
  let C : Circuit :=
    ⟨A.gates ++ B.gates.map (rewire offset limit), readIndex offset limit B.output⟩
  refine ⟨C, ?_, by simp [C, Circuit.size], ?_⟩
  · intro g hg
    change g ∈ A.gates ++ B.gates.map (rewire offset limit) at hg
    rcases List.mem_append.mp hg with ha | hb
    · exact hA g ha
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hb
      simpa [rewire] using hB old hold
  · intro z
    let front := A.wires (List.ofFn z)
    have hfront : front.length = offset := by
      change (A.gates.foldl appendGate (List.ofFn z)).length = n + A.size
      simp [run_length, Circuit.size]
    obtain ⟨ys, hmap, horig, hlen⟩ := run_pair front limit B.gates [] (by
      simp [hfront, limit, Circuit.size])
    simp only [List.append_nil, hfront] at hmap
    have hleft : C.wires (List.ofFn z) = front ++ ys := by
      change ((A.gates ++ B.gates.map (rewire offset limit)).foldl appendGate (List.ofFn z)) = _
      rw [List.foldl_append]
      exact hmap
    have hright : B.wires (front ++ [false]) = front ++ (false :: ys) := horig
    have hbound : front.length + ys.length ≤ limit := by
      simp [hfront, hlen, limit, Circuit.size]
    rw [← h z]
    change (C.wires (List.ofFn z)).getD (readIndex offset limit B.output) false =
      (B.wires (front ++ [false])).getD B.output false
    rw [hleft, hright, ← hfront]
    exact redirected_read front ys limit B.output hbound

end PEqualNP.Outside.L_meta_4506

theorem PEqualNP.Outside.L_meta_4506 :
    ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
    PEqualNP.MetaComplexity.FanInTwo x2 →
    (∀ (x5 : Fin (8 : ℕ) →
    Bool), x2.eval (x1.wires (List.ofFn x5) ++ [Bool.false]) = (x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)))) →
    PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x6 : Fin (8 : ℕ) →
    Bool) => x6 (0 : Fin (8 : ℕ)) && x6 (1 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (2 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (3 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (5 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (4 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (5 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (7 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ))) (x1.size + x2.size) := by
  intro A B hA hB h
  exact PEqualNP.Outside.L_meta_4506.compose_with_false A B hA hB _ h
