import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4940_18
    (clean : ∀ (D : Circuit) (a b : ℕ), Monotone2 D → D.size ≤ 18 →
      (∀ x : Fin 10 → Bool, ((D.wires (List.ofFn x)).getD a false ||
        (D.wires (List.ofFn x)).getD b false) = (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x) →
      ∃ j g m, D.gates[j]? = some g ∧ g.op = .and ∧ m ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ) ∧
        (D.wires (List.ofFn (fun i : Fin 10 => m.testBit i.val))).getD (10+j) false = true)
    (remaining : ∀ (D : Circuit) (a b : ℕ), FanInTwo D → D.size = 18 →
      ((∃ g ∈ D.gates, g.op = .not) ∨
        ∃ j g m, D.gates[j]? = some g ∧ g.op = .and ∧ m ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ) ∧
          (D.wires (List.ofFn (fun i : Fin 10 => m.testBit i.val))).getD (10+j) false = true) →
      (∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD a false = true ∧
        (D.wires (List.ofFn x)).getD b false = false) →
      (∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD a false = false ∧
        (D.wires (List.ofFn x)).getD b false = true) →
      ∃ x : Fin 10 → Bool, ((D.wires (List.ofFn x)).getD a false ||
        (D.wires (List.ofFn x)).getD b false) ≠ (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size = (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro g C a b hg hC hsize
  let D : Circuit := ⟨g :: C.gates,0⟩
  let W (x : Fin 10 → Bool) (i : ℕ) := (D.wires (List.ofFn x)).getD i false
  let F (x : Fin 10 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  change (∃ x, W x a = true ∧ W x b = false) →
    (∃ x, W x a = false ∧ W x b = true) →
    (∀ x, F x = false → W x a = false ∧ W x b = false) →
    ∃ x, F x = true ∧ W x a = false ∧ W x b = false
  intro hab hba hoff
  by_contra hmiss
  have he (x : Fin 10 → Bool) : (W x a || W x b) = F x := by
    cases hf : F x
    · have h := hoff x hf
      simp [h.1,h.2]
    · by_contra bad
      have hz : W x a = false ∧ W x b = false := by
        cases ha : W x a <;> cases hb : W x b <;> simp_all
      exact hmiss ⟨x,hf,hz.1,hz.2⟩
  have hfan : FanInTwo D := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hg z (by simp)
    · exact hC z hz
  have hDsize : D.size = 18 := by
    change (g :: C.gates).length = 18
    change C.gates.length = 17 at hsize
    simp only [List.length_cons]
    omega
  have hbad : (∃ z ∈ D.gates, z.op = .not) ∨
      ∃ j z m, D.gates[j]? = some z ∧ z.op = .and ∧ m ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ) ∧
        (D.wires (List.ofFn (fun i : Fin 10 => m.testBit i.val))).getD (10+j) false = true := by
    by_cases hn : ∃ z ∈ D.gates, z.op = .not
    · exact Or.inl hn
    · right
      have hm : Monotone2 D := by
        intro z hz
        have h := hfan z hz
        have hne : z.op ≠ .not := fun he => hn ⟨z,hz,he⟩
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h ⊢
        rcases h with ⟨h | h | h,hlen⟩
        · exact ⟨Or.inl h,hlen⟩
        · exact ⟨Or.inr h,hlen⟩
        · exact (hne h).elim
      apply clean D a b hm (by omega)
      exact he
  obtain ⟨x,hx⟩ := remaining D a b hfan hDsize hbad hab hba
  exact hx (he x)
