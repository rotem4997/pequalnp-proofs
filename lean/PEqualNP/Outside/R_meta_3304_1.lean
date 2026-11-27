import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3304_1
    (lowerBound : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (optimalGates : ∀ C : Circuit, FanInTwo C → C.size = 13 →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) x) →
      ∀ g ∈ C.gates, g.op ≠ GateOp.not) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (5 : ℕ) ≤ x2.size →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  classical
  dsimp only
  intro pre post sourceWire preFan postFan _ budget _ aliasLt _ correct
  let boundary := 8 + pre.size
  let index (i : ℕ) := if i < boundary then i else if i = boundary then sourceWire else i - 1
  let remap (g : Gate) : Gate := ⟨g.op, g.inputs.map index⟩
  let merged : Circuit := ⟨pre.gates ++ post.gates.map remap, index post.output⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have appendRead (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi, ite_eq_right (Nat.ne_of_lt hi)]
    · by_cases he : i = w.length
      · subst i
        simp
      · rw [ite_eq_right he, List.getD_eq_default, List.getD_eq_default]
        · omega
        · simp only [List.length_append, List.length_singleton]; omega
  have wireLen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
                                 List.length_cons, List.length_nil]; omega
  have run (gs : List Gate) (l r : List Bool) (hsize : l.length + 1 = r.length)
      (base : boundary ≤ l.length) (rel : ∀ i, l.getD (index i) false = r.getD i false) :
      ∀ i, ((gs.map remap).foldl step l).getD (index i) false = (gs.foldl step r).getD i false := by
    induction gs generalizing l r with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp only [step, List.length_append, List.length_singleton]; omega
      · simp only [step, List.length_append, List.length_singleton]; omega
      · intro i
        simp only [step, appendRead, remap, List.map_map]
        have endAt : index i = l.length ↔ i = r.length := by
          dsimp [index]; split <;> (try split) <;> omega
        simp only [Function.comp_def, endAt, rel]
  have mergedFan : FanInTwo merged := by
    intro g hg
    rcases List.mem_append.mp hg with hp | hs
    · exact preFan g hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
      simpa [remap] using postFan q hq
  have sameEval (x : Fin 8 → Bool) : merged.eval (List.ofFn x) =
      post.eval (pre.wires (List.ofFn x) ++ [(pre.wires (List.ofFn x)).getD sourceWire false]) := by
    let w := pre.wires (List.ofFn x)
    have len : w.length = boundary := by
      change (pre.gates.foldl step (List.ofFn x)).length = _
      rw [wireLen, List.length_ofFn]; rfl
    change ((pre.gates ++ post.gates.map remap).foldl step (List.ofFn x)).getD _ false = _
    rw [List.foldl_append]
    apply run post.gates w (w ++ [w.getD sourceWire false]) (by simp) (by omega)
    intro i
    rw [appendRead, len]
    dsimp [index]
    split_ifs <;> first | rfl | (exfalso; omega) | (rw [List.getD_eq_default, List.getD_eq_default] <;> omega)
  have correctMerged (x : Fin 8 → Bool) := (sameEval x).trans (correct x)
  have size : merged.size = pre.size + post.size := by
    change (pre.gates ++ post.gates.map remap).length = pre.gates.length + post.gates.length
    simp
  have exactSize : merged.size = 13 := by
    by_contra h
    exact lowerBound ⟨merged, mergedFan, by omega, correctMerged⟩
  have positive (g : Gate) (hg : g ∈ post.gates) : g.op = .and ∨ g.op = .or := by
    have hn := optimalGates merged mergedFan exactSize correctMerged (remap g)
      (List.mem_append_right _ (List.mem_map_of_mem hg))
    have allowed : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using (postFan g hg).1
    exact allowed.elim Or.inl (fun h => h.elim Or.inr (fun hnot => False.elim (hn hnot)))
  have propagate (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (l r : List Bool) (lengths : l.length = r.length)
      (rel : ∀ i, l.getD i false = true → r.getD i false = true) :
      ∀ i, (gs.foldl step l).getD i false = true → (gs.foldl step r).getD i false = true := by
    induction gs generalizing l r with
    | nil => exact rel
    | cons g gs ih =>
      apply ih (fun q hq => ops q (List.mem_cons_of_mem _ hq))
      · simp [step, lengths]
      · intro i
        simp only [step, appendRead, lengths]
        split
        · rcases ops g List.mem_cons_self with hop | hop
          · rw [hop]
            change (g.inputs.map fun j => l.getD j false).all id = true →
              (g.inputs.map fun j => r.getD j false).all id = true
            simp only [List.all_eq_true, List.forall_mem_map, id_eq]
            exact fun h j hj => rel j (h j hj)
          · rw [hop]
            change (g.inputs.map fun j => l.getD j false).any id = true →
              (g.inputs.map fun j => r.getD j false).any id = true
            simp only [List.any_eq_true, id_eq]
            rintro ⟨b, hb, h⟩
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
            exact ⟨_, List.mem_map_of_mem hj, rel j h⟩
        · exact rel i
  let single (v : Fin 8) := decide (v = 0)
  let w := pre.wires (List.ofFn single)
  refine ⟨single, ?_⟩
  have normal : post.eval (w ++ [w.getD sourceWire false]) = false := correct single
  have ordered : ∀ i, (w ++ [false]).getD i false = true →
      (w ++ [w.getD sourceWire false]).getD i false = true := by
    intro i
    simp only [appendRead]; split <;> simp
  intro bad
  have yes : post.eval (w ++ [false]) = true := bad
  exact Bool.noConfusion ((propagate post.gates positive _ _ (by simp) ordered post.output yes).symm.trans normal)
