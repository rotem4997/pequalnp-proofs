import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Collapse each AND-only stretch into a conjunction of earlier signals.
-- In this form the only choices are two subsets at each OR and one at the output.
theorem PEqualNP.Outside.R_meta_2377_2
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      ∃ (R : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ),
        R.length = {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard ∧
        (∀ j (hj : j < R.length) i, i ∈ R[j].1 ∪ R[j].2 → i < n + 1 + j) ∧
        (∀ i ∈ out, i < n + 1 + R.length) ∧
        (∀ x : Fin n → Bool,
          C.eval (List.ofFn x) =
            let w := R.foldl (fun w r => w ++ [
              decide (∀ i ∈ r.1, w.getD i false = true) ||
              decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
            decide (∀ i ∈ out, w.getD i false = true)))
    (finite : ∀ (R : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ),
      let adj := fun p l : Fin 21 =>
        ([(p.val + 20) % 21, p.val, (p.val + 5) % 21, (p.val + 7) % 21,
          (p.val + 17) % 21] : List ℕ).contains l.val
      let eval := fun x : Fin 42 → Bool =>
        let w := R.foldl (fun w r => w ++ [
          decide (∀ i ∈ r.1, w.getD i false = true) ||
          decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
        decide (∀ i ∈ out, w.getD i false = true)
      let independent := fun x : Fin 42 → Bool =>
        ∀ p l, adj p l = true → x (Fin.castAdd 21 p) = false ∨ x (Fin.natAdd 21 l) = false
      (∀ j (hj : j < R.length) i, i ∈ R[j].1 ∪ R[j].2 → i < 43 + j) →
      (∀ i ∈ out, i < 43 + R.length) →
      (∀ p l, adj p l = true →
        eval (fun i => decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l)) = true) →
      (∀ x, independent x →
        (∀ y, independent y → (∀ i, x i = true → y i = true) → y = x) →
        eval x = false) →
      104 ≤ R.length) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C basis computes
  obtain ⟨R, out, length, ruleRefs, outRefs, same⟩ := normalize 42 C basis
  rw [← length]
  let nbr (i : ℕ) : List ℕ := [(i + 20) % 21, i, (i + 5) % 21, (i + 7) % 21, (i + 17) % 21]
  let table := (List.range 21).flatMap (fun i => (nbr i).map (fun j => (i, 21 + j)))
  let adj (p l : Fin 21) := (nbr p.val).contains l.val
  let eval (x : Fin 42 → Bool) : Bool :=
    let w := R.foldl (fun w r => w ++ [
      decide (∀ i ∈ r.1, w.getD i false = true) ||
      decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
    decide (∀ i ∈ out, w.getD i false = true)
  have correct (x : Fin 42 → Bool) : eval x = true ↔
      ∃ u v : Fin 42, (u.val, v.val) ∈ table ∧ x u = true ∧ x v = true := by
    have h := same x
    change C.eval (List.ofFn x) = eval x at h
    rw [← h]
    exact computes x
  have table_of_adj (p l : Fin 21) (h : adj p l = true) :
      (p.val, 21 + l.val) ∈ table := by
    have member : l.val ∈ nbr p.val := List.contains_iff_mem.mp h
    exact List.mem_flatMap.mpr ⟨p.val, List.mem_range.mpr p.isLt,
      List.mem_map.mpr ⟨l.val, member, rfl⟩⟩
  have adj_of_table (u v : Fin 42) (h : (u.val, v.val) ∈ table) :
      ∃ p l : Fin 21, u = Fin.castAdd 21 p ∧ v = Fin.natAdd 21 l ∧ adj p l = true := by
    obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj, eq⟩ := List.mem_map.mp h
    have point : i = u.val := congrArg Prod.fst eq
    have line : 21 + j = v.val := congrArg Prod.snd eq
    let p : Fin 21 := ⟨i, List.mem_range.mp hi⟩
    let l : Fin 21 := ⟨j, by omega⟩
    exact ⟨p, l, Fin.ext point.symm, Fin.ext line.symm, List.contains_iff_mem.mpr hj⟩
  have testedPositive (p l : Fin 21) (h : adj p l = true) :
      eval (fun i => decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l)) = true := by
    apply (correct _).mpr
    exact ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, table_of_adj p l h,
      by simp, by simp⟩
  have testedNegative (x : Fin 42 → Bool)
      (none : ∀ p l, adj p l = true → x (Fin.castAdd 21 p) = false ∨ x (Fin.natAdd 21 l) = false) :
      eval x = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨u, v, edge, hu, hv⟩ := (correct x).mp yes
    obtain ⟨p, l, rfl, rfl, adj_true⟩ := adj_of_table u v edge
    rcases none p l adj_true with off | off
    · rw [off] at hu
      contradiction
    · rw [off] at hv
      contradiction
  exact finite R out ruleRefs outRefs testedPositive (fun x h _ => testedNegative x h)
