import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3268_625
    (clamp : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (X : List Bool), X.length = n →
      (⟨C.gates.map (fun g => ⟨g.op, g.inputs.map fun i => min i (n+C.size)⟩), 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires X = C.wires X)
    (finiteCore : let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size = 8 → C.output = 0 →
      (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 17) →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      ∀ S : Finset ℕ, S ⊆ Finset.range 17 → S.card ≤ 6 → ∃ x y : Fin 9 → Bool,
        (∀ i ∈ S, (C.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn y)).getD i false) ∧ F x ≠ F y) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size = (8 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∀ (x6 : Finset ℕ), x6.card ≤ (6 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool) (x9 : Fin (9 : ℕ) → Bool), (∀ x10 ∈ x6, (x2.wires (List.ofFn x8)).getD x10 Bool.false = (x2.wires (List.ofFn x9)).getD x10 Bool.false) ∧ x1 x8 ≠ x1 x9 := by
  intro F C mono size first S budget
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map fun i => min i (9+C.size)⟩),0⟩
  have wires (x : Fin 9 → Bool) : D.wires (List.ofFn x) = C.wires (List.ofFn x) := clamp 9 C _ (by simp)
  have dsize : D.size = 8 := by
    change (C.gates.map _).length = 8
    rw [List.length_map]
    exact size
  have dmono : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono a ha).1, by simpa using (mono a ha).2⟩
  have dbound : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 17 := by
    intro g hg i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have h := Nat.min_le_right j (9+C.size)
    omega
  let T := S.filter (fun i => i < 17)
  have sub : T ⊆ Finset.range 17 := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have bound : T.card ≤ 6 := (Finset.card_filter_le S _).trans budget
  obtain ⟨x,y,agree,unequal⟩ := finiteCore D dmono dsize rfl dbound (by intro x; rw [wires]; exact first x) T sub bound
  refine ⟨x,y,?_,unequal⟩
  intro i hi
  by_cases small : i < 17
  · have h := agree i (Finset.mem_filter.mpr ⟨hi,small⟩)
    simpa only [wires] using h
  · have len (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).length = 17 := by
      let step := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have runlen (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
        induction gs generalizing w with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons,ih]
          simp [step]
          omega
      change (C.gates.foldl step (List.ofFn x)).length = 17
      rw [runlen,List.length_ofFn]
      change 9+C.size=17
      omega
    rw [List.getD_eq_default _ _ (by rw [len]; omega),List.getD_eq_default _ _ (by rw [len]; omega)]
