import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The mask for a row b marks the allowed second components c of the second OR.
theorem PEqualNP.Outside.R_meta_4811_679 :
  (let P : (Fin 42 → Bool) → Prop := fun x =>
    ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧
      (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x p = true ∧ x l = true
   ∀ (a : Fin 42) (b c : Fin 43) (D : Circuit), b < c →
    (∀ x : Fin 42 → Bool, (let y : Fin 43 → Bool := Fin.lastCases (x 0 || x a) x
      D.eval (List.ofFn (Fin.lastCases (y b || y c) y)) = true ↔ P x)) →
    ∀ v : Fin 42, [0,a.val,b.val,c.val].count v.val = 1 →
      ∃ g ∈ D.gates, v.val ∈ g.inputs) →
  (let P : (Fin 42 → Bool) → Prop := fun x =>
    ∃ p l : Fin 42, (p.val < 21 ∧ 21 ≤ l.val ∧
      (l.val + 21 - p.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x p = true ∧ x l = true
   let same : List ℕ := [81788948,0,4398145077304,0,4398077984768] ++
     List.replicate 16 0 ++ [4398059094016,4398256226304,4406653222912]
   let edge : List ℕ := [71303174,4398126202900,4398067482760]
   let miss : List ℕ := [10485770,4398258323484,0,4402383429648]
   ∃ (a : Fin 42) (b c : Fin 43) (D : Circuit),
    (a = 1 ∨ a = 21 ∨ a = 22) ∧ b < c ∧ (b,c) ≠ (0,a.castSucc) ∧
    (c = Fin.last 42 → b ≠ 0 ∧ b ≠ a.castSucc) ∧
    (((if a = 1 then same else if a = 21 then edge else miss).getD b.val 0).testBit c.val = true) ∧
    Monotone2 D ∧ ReadsBack 44 D ∧ D.size ≤ 122 ∧
    ∀ x : Fin 42 → Bool,
      let y : Fin 43 → Bool := Fin.lastCases (x 0 || x a) x
      D.eval (List.ofFn (Fin.lastCases (y b || y c) y)) = true ↔ P x) →
have x1 : (Fin (42 : ℕ) → Bool) → Prop := fun (x1 : Fin (42 : ℕ) → Bool) => ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (42 : ℕ)), (↑x2 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x3 ∧ (↑x3 + (21 : ℕ) - ↑x2) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : Fin (43 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (x2 = (1 : Fin (42 : ℕ)) ∨ x2 = (21 : Fin (42 : ℕ)) ∨ x2 = (22 : Fin (42 : ℕ))) ∧     x3 < x4 ∧       (x3, x4) ≠ ((0 : Fin (43 : ℕ)), x2.castSucc) ∧         (x4 = Fin.last (42 : ℕ) → x3 ≠ (0 : Fin (43 : ℕ)) ∧ x3 ≠ x2.castSucc) ∧           (∀ (x6 : Fin (42 : ℕ)), List.count ↑x6 [(0 : ℕ), ↑x2, ↑x3, ↑x4] = (1 : ℕ) → ∃ x8 ∈ x5.gates, ↑x6 ∈ x8.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x5 ∧                 x5.size ≤ (122 : ℕ) ∧                   ∀ (x6 : Fin (42 : ℕ) → Bool),                     ((x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x7 x8 = Bool.true → x6 x8 = Bool.true) → x1 x7 → x7 = x6) ∨ ¬x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x6 x8 = Bool.true → x7 x8 = Bool.true) → ¬x1 x7 → x7 = x6) →                       have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 (0 : Fin (42 : ℕ)) || x6 x2) x6 x8;                       x5.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x3 || x8 x4) x8 x9) = Bool.true ↔ x1 x6 := by
  intro readback search P
  obtain ⟨a,b,c,D,ha,hbc,hd,he,_,hmono,hback,hsize,heval⟩ := search
  exact ⟨a,b,c,D,ha,hbc,hd,he,readback a b c D hbc heval,hmono,hback,hsize,
    fun x _ => heval x⟩
