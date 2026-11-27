import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3229_415
    (hshape : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.gates.length = 14 → PEqualNP.MetaComplexity.Monotone2 C → C.output = 23 →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.gates.length = 10 ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      ∃ j : Fin 5 → Nat, ∃ m ∈ ([2147483648,2155905024,2290122880,2290649216,2827520136,2829625344,2829625480,2860548224,2863179944,2863311528,3937053354,3941263872,3941264042,4008372970,4008636128,4008636138,4169697416,4177066120,4277071598,4278124202,4278124270,4293585642,4294901502,4294967294] : List Nat), ∀ x : List Bool, x.length = 10 → C.eval x = m.testBit (BitVec.ofBoolListLE (List.ofFn fun i : Fin 5 => (true :: D.wires (x)).getD (j i) false)).toNat)
    (hfront : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.gates.length = 10 → PEqualNP.MetaComplexity.Monotone2 D →
      ∀ j : Fin 5 → Nat, ∀ m ∈ ([2147483648,2155905024,2290122880,2290649216,2827520136,2829625344,2829625480,2860548224,2863179944,2863311528,3937053354,3941263872,3941264042,4008372970,4008636128,4008636138,4169697416,4177066120,4277071598,4278124202,4278124270,4293585642,4294901502,4294967294] : List Nat),
      let f := fun (r : Nat) (v : Bool) => m.testBit (BitVec.ofBoolListLE (List.ofFn fun i : Fin 5 => (true :: D.wires (((List.ofFn fun i : Fin 9 => r.testBit i.val) ++ [v]))).getD (j i) false)).toNat
      let g := fun r : Nat => f r (r.testBit 0 || r.testBit 3)
      ∀ p ∈ ([3,12,24,17,33,264] : List Nat), ∀ n ∈ ([50,116,208,276,402] : List Nat),
      f p false = false → f n true = true → (∀ t ∈ ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat), g t = true) →
      ¬ ∀ t ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List Nat), g t = false) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ x2 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.false]) = Bool.false) ∧ ∃ x2 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.true]) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [x3.testBit (0 : ℕ) || x3.testBit (3 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.gates.length = (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.output = (23 : ℕ) → x1 x3 → (∀ x8 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x2 x3 x8 = Bool.true) → ¬∀ x9 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x2 x3 x9 = Bool.false := by
  intro _ _ C hl hm ho hw hp hn
  obtain ⟨D,hd,hmD,j,m,hmask,he⟩ := hshape C hl hm ho
  obtain ⟨⟨p,hp',hfalse⟩,⟨n,hn',htrue⟩⟩ := hw
  have atRow (t : Nat) (b : Bool) := he ((List.ofFn fun i : Fin 9 => t.testBit i.val) ++ [b]) (by simp)
  apply hfront D hd hmD j m hmask p hp' n hn'
  · exact (atRow p false).symm.trans hfalse
  · exact (atRow n true).symm.trans htrue
  · exact fun t ht => (atRow t _).symm.trans (hp t ht)
  · exact fun t ht => (atRow t _).symm.trans (hn t ht)
