import PEqualNP.Defs

-- Uses the twenty-four sample inputs from R_meta_2159_317.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3640_509
    (project : ∀ (C : Circuit), FanInTwo C →
      ∀ (ins : Fin 24 → List Bool), (∀ i, (ins i).length = 11) →
      let p := (List.ofFn fun j : Fin 11 => fun i : Fin 24 => (ins i).getD j.val false) ++ [fun _ => false, fun _ => true]
      ∃ fs : List (Fin 24 → Bool), fs.length ≤ C.size ∧
        (fun i => C.eval (ins i)) ∈ p ++ fs ∧
        (∀ j : Fin fs.length, let w := p ++ fs.take j.val
          (∃ a ∈ w, fs.get j = (fun i => !(a i))) ∨
          ∃ a ∈ w, ∃ b ∈ w, fs.get j = (fun i => a i && b i) ∨ fs.get j = (fun i => a i || b i)))
    (finite : ∀ k ∈ ([12,13,15,18,23,28] : List ℕ),
      let row := fun i : Fin 24 => fun j : Fin 9 =>
        ([3,6,12,24,17,33,66,132,264,160,320,288,42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ).getD i.val 0 |>.testBit j.val
      let ins := fun i : Fin 24 => List.ofFn (row i) ++ [!row i 0,
        row i (Fin.ofNat 9 (k / 10)) || row i (Fin.ofNat 9 (k % 10))]
      let p := (List.ofFn fun j : Fin 11 => fun i : Fin 24 => (ins i).getD j.val false) ++ [fun _ => false, fun _ => true]
      ∀ fs : List (Fin 24 → Bool), fs.length ≤ 13 →
        (∀ j : Fin fs.length, let w := p ++ fs.take j.val
          (∃ a ∈ w, fs.get j = (fun i => !(a i))) ∨
          ∃ a ∈ w, ∃ b ∈ w, fs.get j = (fun i => a i && b i) ∨ fs.get j = (fun i => a i || b i)) →
        (fun i : Fin 24 => decide (i.val < 12)) ∉ p ++ fs) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (18 : ℕ), (23 : ℕ), (28 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), x7 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) || x7 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))]) ≠ x1 x7 := by
  intro F k hk C hfan hsize
  by_contra! hall
  let row := fun i : Fin 24 => fun j : Fin 9 =>
        ([3,6,12,24,17,33,66,132,264,160,320,288,42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ).getD i.val 0 |>.testBit j.val
  let ins := fun i : Fin 24 => List.ofFn (row i) ++ [!row i 0,
        row i (Fin.ofNat 9 (k / 10)) || row i (Fin.ofNat 9 (k % 10))]
  have ht : ∀ i : Fin 24, F (row i) = decide (i.val < 12) := by decide +kernel
  obtain ⟨fs, hfs, hmem, legal⟩ := project C hfan ins (by intro i; simp [ins])
  have heq : (fun i => C.eval (ins i)) = (fun i : Fin 24 => decide (i.val < 12)) := by
    funext i
    exact (hall (row i)).trans (ht i)
  rw [heq] at hmem
  exact (finite k hk fs (hfs.trans hsize) legal) hmem
