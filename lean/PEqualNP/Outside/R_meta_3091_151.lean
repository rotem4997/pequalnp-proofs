import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3091_151
    (forcing :
      let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let seed := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 3]
      let exc := fun (op : GateOp) => if op.eval [] then ([3,9,30,39,49] : List ℕ) else [2,4,8,31,34,35]
      ∀ C : Circuit, (∀ x, C.eval (seed x) = f x) →
        (∀ g ∈ C.gates, ∀ (a : Fin 9) (b : Fin 10),
        (g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val]) →
        (g.op = .and ∨ g.op = .or) → 10*a.val+b.val ∉ exc g.op → 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count a.val) ∧
        ((⟨.and,[0,3]⟩ : Gate) ∈ C.gates ∨ (⟨.and,[3,0]⟩ : Gate) ∈ C.gates → 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count 0 ∨ 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count 3))
    (search :
      let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let seed := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 3]
      let exc := fun (op : GateOp) => if op.eval [] then ([3,9,30,39,49] : List ℕ) else [2,4,8,31,34,35]
      ∀ C : Circuit, let u := C.output :: C.gates.flatMap Gate.inputs
      let neg := (C.gates.filter fun g => g.op.eval [false] && !g.op.eval [true]).length
      FanInTwo C → C.size = 14 → (∀ i ∈ u, i ≤ 24) → (∀ i < 24, i ∈ u) →
      9+neg+∑ i ∈ Finset.range 24, (u.count i-1) ≤ 14 → 2 ≤ u.count 9 →
      (∀ i : Fin 9, ∃ x, C.eval (List.ofFn x ++ [x i]) ≠ f x) →
      ∀ R : Finset ℕ, R.card+neg ≤ 4 →
      (∀ g ∈ C.gates, ∀ (a : Fin 9) (b : Fin 10),
        (g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val]) →
        (g.op = .and ∨ g.op = .or) → 10*a.val+b.val ∉ exc g.op → a.val ∈ R) →
      ((⟨.and,[0,3]⟩ : Gate) ∈ C.gates ∨ (⟨.and,[3,0]⟩ : Gate) ∈ C.gates → 0 ∈ R ∨ 3 ∈ R) →
      ∃ x, C.eval (seed x) ≠ f x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → (2 : ℕ) ≤ List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  dsimp only
  intro C fan sz within refs budget double copies
  let u := C.output :: C.gates.flatMap Gate.inputs
  let neg := (C.gates.filter fun g => g.op.eval [false] && !g.op.eval [true]).length
  let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let seed := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 3]
  let exc := fun (op : GateOp) => if op.eval [] then ([3,9,30,39,49] : List ℕ) else [2,4,8,31,34,35]
  let R := (Finset.range 9).filter fun i => 2 ≤ u.count i
  have eqf (x : Fin 9 → Bool) : f x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    simp [f, List.any, Bool.or_assoc]
    rfl
  by_contra! computes
  have ev (x : Fin 9 → Bool) : C.eval (seed x) = f x := by rw [eqf]; exact computes x
  have budget' : 9+neg+∑ i ∈ Finset.range 24, (u.count i-1) ≤ 14 := by simpa [sz, neg, u] using budget
  have aggregate : ∀ (u : List ℕ) (z : ℕ), 2 ≤ u.count 9 →
      9+z+∑ i ∈ Finset.range 24, (u.count i-1) ≤ 14 →
      ((Finset.range 9).filter fun i => 2 ≤ u.count i).card+z ≤ 4 := by
    intro u z h9 bound
    let R := (Finset.range 9).filter fun i => 2 ≤ u.count i
    have h9R : 9 ∉ R := by simp [R]
    have sub : insert 9 R ⊆ Finset.range 24 := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | h
      · decide
      · have := Finset.mem_range.mp (Finset.mem_filter.mp h).1
        exact Finset.mem_range.mpr (by omega)
    have card : R.card+1 ≤ ∑ i ∈ Finset.range 24, (u.count i-1) := by
      calc
        R.card+1 = ∑ _i ∈ insert 9 R, 1 := by simp [h9R]
        _ ≤ ∑ i ∈ insert 9 R, (u.count i-1) := by
          apply Finset.sum_le_sum
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | h
          · omega
          · have := (Finset.mem_filter.mp h).2
            omega
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; omega)
    change R.card+z ≤ 4
    omega
  have hR := aggregate u neg double budget'
  obtain ⟨forc, special⟩ := forcing C ev
  have hc : ∀ i : Fin 9, ∃ x, C.eval (List.ofFn x ++ [x i]) ≠ f x := by
    intro i
    obtain ⟨x,h⟩ := copies i
    exact ⟨x, by rwa [eqf]⟩
  obtain ⟨x, hx⟩ := search C fan sz (by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | h
    · simpa [sz] using within.1
    · obtain ⟨g, hg, hi⟩ := List.mem_flatMap.mp h
      simpa [sz] using within.2 g hg i hi) (by simpa [sz] using refs)
    budget' double hc R hR (by
      intro g hg a b inputs op except
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, forc g hg a b inputs op except⟩) (by
      intro gate
      rcases special gate with z | z
      · exact Or.inl (Finset.mem_filter.mpr ⟨by decide,z⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨by decide,z⟩))
  exact hx (ev x)
