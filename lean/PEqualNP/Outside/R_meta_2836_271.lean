import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2836_271
    (noFirst : let f := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 0 false) ++
          [x 0 || x 4, x 0 || x 3]) = f x) → False)
    (noSecond : let f := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 4 false) ++
          [x 0 || x 4, x 4 || x 1]) = f x) → False)
    (noTriple : let f := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (k : Fin 9), (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) →
        ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false, x 0 || x 4 || x k]) = f x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : (Fin (9 : ℕ) → Bool) → Bool := fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ));   PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ((∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ))]) = x2 x5) ∨ ∃ (x5 : Fin (9 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) ∧ x5 ≠ (4 : Fin (9 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [Bool.false, x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x5]) = x2 x6) → False := by
  intro C f hfan hsize cases
  apply cases.elim (noFirst C hfan hsize)
  intro rest
  apply rest.elim (noSecond C hfan hsize)
  intro remain
  let σ : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  let ρ (i : ℕ) : ℕ := if h : i < 9 then (σ ⟨i,h⟩).val else i
  have ρ_small (i : ℕ) (hi : i < 9) : ρ i < 9 := by simp [ρ, hi]
  have ρ_fix (i : ℕ) (hi : 9 ≤ i) : ρ i = i := by simp [ρ, Nat.not_lt.mpr hi]
  have sym (x : Fin 9 → Bool) : f (x ∘ σ) = f x := by
    change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 1 || x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 || x 7 && x 2 || x 2 && x 1) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    simp only [Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  have upd (x : Fin 9 → Bool) :
      Function.update (x ∘ σ) 4 false = Function.update x 4 false ∘ σ := by
    funext i
    fin_cases i <;> rfl
  let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
  let D : Circuit := ⟨C.gates.map renameGate, ρ C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ C.gates.map renameGate at hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop,hlen⟩ := hfan h hh
    exact ⟨hop, by simpa only [renameGate, List.length_map] using hlen⟩
  have sizeD : D.size ≤ 13 := by
    change (C.gates.map renameGate).length ≤ 13
    rw [List.length_map]
    exact hsize
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have last (w : List Bool) (a : Bool) : (w ++ [a]).getD w.length false = a := by
    simp [List.getD_eq_getElem?_getD]
  have old (w : List Bool) (a : Bool) (i : ℕ) (h : i ≠ w.length) :
      (w ++ [a]).getD i false = w.getD i false := by
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have simulate (gs : List Gate) (w z : List Bool) (len : w.length = z.length)
      (enough : 9 ≤ w.length) (eq : ∀ i, w.getD i false = z.getD (ρ i) false) :
      ∀ i, (gs.foldl step w).getD i false =
        ((gs.map renameGate).foldl step z).getD (ρ i) false := by
    induction gs generalizing w z with
    | nil => exact eq
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp only [step, List.length_append, List.length_cons, List.length_nil, len]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      intro i
      have pins : g.inputs.map (fun j => w.getD j false) =
          (g.inputs.map ρ).map (fun j => z.getD j false) := by
        rw [List.map_map]
        exact List.map_congr_left (fun j _ => eq j)
      by_cases hi : i = w.length
      · rw [hi, ρ_fix _ enough]
        conv_rhs => rw [len]
        simp only [step, renameGate, last]
        rw [pins]
      · have hj : ρ i ≠ z.length := by
          intro he
          by_cases small : i < 9
          · have lt := ρ_small i small
            omega
          · rw [ρ_fix i (by omega)] at he
            omega
        simp only [step, renameGate]
        rw [old _ _ _ hi, old _ _ _ hj, eq]
  have transfer (x : Fin 9 → Bool) (a b : Bool) :
      C.eval (List.ofFn (x ∘ σ) ++ [a,b]) = D.eval (List.ofFn x ++ [a,b]) := by
    apply simulate
    · simp
    · simp
    intro i
    by_cases hi : i < 9
    · have hr := ρ_small i hi
      rw [List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_append _ _ _ _ (by simpa using hr)]
      rw [List.getD_eq_getElem _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using hr)]
      simp only [List.getElem_ofFn, ρ, dif_pos hi, Function.comp_apply]
    · rw [ρ_fix i (by omega),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi)]
      simp only [List.length_ofFn]
  rcases remain with third | fourth
  · apply noSecond D fanD sizeD
    intro x
    rw [← transfer (Function.update x 4 false)]
    have h := third (x ∘ σ)
    rw [upd x] at h
    exact h.trans (sym x)
  · obtain ⟨k,h0,h4,h⟩ := fourth
    have reps : (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) ∨
        (σ k = 1 ∨ σ k = 2 ∨ σ k = 3 ∨ σ k = 6) := by
      fin_cases k <;> first | exact (h0 rfl).elim | exact (h4 rfl).elim | decide
    rcases reps with own | swapped
    · exact noTriple k own C hfan hsize h
    · apply noTriple (σ k) swapped D fanD sizeD
      intro x
      rw [← transfer x]
      exact (h (x ∘ σ)).trans (sym x)
