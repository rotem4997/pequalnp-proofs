import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5361_317
    (sound : ∀ (a : Fin 42) (b c : Fin 43) (C : Circuit)
      (R : Fin 42 → Fin 42 → Prop),
      Monotone2 C →
      let F := fun (x : Fin 42 → Bool) => let y : Fin 43 → Bool := Fin.lastCases (x 0 || x a) x; C.eval (List.ofFn (Fin.lastCases (y b || y c) y))
      (∀ u v, R u v → F (fun k => decide (k = u ∨ k = v)) = true) ∧
      (∀ s t : Fin 21 → Bool,
        let e (i j : Fin 21) := R (i.castAdd 21) (Fin.natAdd 21 j)
        (∀ i, s i = true ↔ ∀ j, t j = true → ¬ e i j) →
        (∀ j, t j = true ↔ ∀ i, s i = true → ¬ e i j) →
        F (fun k => Fin.addCases (motive := fun _ => Bool) s t k) = false) →
      ∀ x, F x = true ↔ ∃ u v, R u v ∧ x u = true ∧ x v = true)
    (search : ∃ (a : Fin 42) (b c : Fin 43) (C : Circuit),
      (6291458 : ℕ).testBit a.val = true ∧
      (let row : List ℕ := if a = 1 then [81788948,0,4398145077304,0,4398077984768,4398059094016,4398256226304,4406653222912]
        else if a = 21 then [71303174,4398126202900,4398067482760] else [10485770,4398258323484,0,4402383429648]
       (row.getD (([0,1,2,3,4,21,22,23] : List ℕ).idxOf b.val) 0).testBit c.val = true) ∧
      Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 44 C ∧ C.size ≤ 122 ∧
      (let R := fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
      let F := fun (x : Fin 42 → Bool) => let y : Fin 43 → Bool := Fin.lastCases (x 0 || x a) x; C.eval (List.ofFn (Fin.lastCases (y b || y c) y))
      (∀ u v, R u v → F (fun k => decide (k = u ∨ k = v)) = true) ∧
      (∀ s t : Fin 21 → Bool,
        let e (i j : Fin 21) := R (i.castAdd 21) (Fin.natAdd 21 j)
        (∀ i, s i = true ↔ ∀ j, t j = true → ¬ e i j) →
        (∀ j, t j = true ↔ ∀ i, s i = true → ¬ e i j) →
        F (fun k => Fin.addCases (motive := fun _ => Bool) s t k) = false))) :
    ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     (have x5 : List ℕ := if x1 = (1 : Fin (42 : ℕ)) then [(81788948 : ℕ), (0 : ℕ), (4398145077304 : ℕ), (0 : ℕ), (4398077984768 : ℕ), (4398059094016 : ℕ), (4398256226304 : ℕ), (4406653222912 : ℕ)] else if x1 = (21 : Fin (42 : ℕ)) then [(71303174 : ℕ), (4398126202900 : ℕ), (4398067482760 : ℕ)] else [(10485770 : ℕ), (4398258323484 : ℕ), (0 : ℕ), (4402383429648 : ℕ)];       (x5.getD (List.idxOf ↑x2 [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (21 : ℕ), (22 : ℕ), (23 : ℕ)]) (0 : ℕ)).testBit ↑x3 = Bool.true) ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧           x4.size ≤ (122 : ℕ) ∧             ∀ (x5 : Fin (42 : ℕ) → Bool),               have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;               x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  obtain ⟨a,b,c,C,ha,ht,hm,hb,hs,h⟩ := search
  have admissible : ∀ j : Fin 42, (6291458 : ℕ).testBit j.val = true → j = 1 ∨ j = 21 ∨ j = 22 := by decide
  refine ⟨a,b,c,C,admissible a ha,ht,hm,hb,hs,?_⟩
  exact sound a b c C (fun (u v : Fin 42) => u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) hm h
