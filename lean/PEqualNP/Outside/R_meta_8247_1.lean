import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8247_1
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin C.size) (j : ℕ), j < 9 → j ≠ 4 → (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ l : Fin C.size, 4 ∈ (C.gates.get l).inputs → l = i) → ((C.gates.get i).inputs = [4,j] ∨ (C.gates.get i).inputs = [j,4]) → PEqualNP.MetaComplexity.circuitFun 9 C ≠ (fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin C.size), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 → (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ l : Fin C.size, 4 ∈ (C.gates.get l).inputs ↔ l = i) → ((C.gates.get i).inputs = [4] ∨ (C.gates.get i).inputs = [4,4]) → PEqualNP.MetaComplexity.circuitFun 9 C ≠ (fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h3 : let f := (fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))); ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin C.size), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 → (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ l : Fin C.size, 4 ∈ (C.gates.get l).inputs ↔ l = i) → ∀ j : ℕ, 9 ≤ j → ((C.gates.get i).inputs = [4,j] ∨ (C.gates.get i).inputs = [j,4]) → PEqualNP.MetaComplexity.circuitFun 9 C = f → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ), PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ 13 ∧ PEqualNP.MetaComplexity.circuitFun 8 D = (fun x : Fin 8 → Bool => f ((4 : Fin 9).insertNth false x)) ∧ ∀ x : Fin 8 → Bool, f ((4 : Fin 9).insertNth false x) = false → f ((4 : Fin 9).insertNth true x) = true → (D.wires (List.ofFn x)).getD w false = true)
    (h4 : let f := (fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))); ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 → PEqualNP.MetaComplexity.circuitFun 8 D = (fun x : Fin 8 → Bool => f ((4 : Fin 9).insertNth false x)) → ∃ x : Fin 8 → Bool, f ((4 : Fin 9).insertNth false x) = false ∧ f ((4 : Fin 9).insertNth true x) = true ∧ (D.wires (List.ofFn x)).getD w false = false)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin x1.size), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x6 : Fin x1.size), (4 : ℕ) ∈ (x1.gates.get x6).inputs ↔ x6 = x2) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) := by
  intro C i hfan hs hop hread hf
  have hmem : 4 ∈ (C.gates.get i).inputs := (hread i).2 rfl
  have hlen : (C.gates.get i).inputs.length ≤ 2 :=
    (hfan _ (List.get_mem ..)).2
  have two (j : ℕ) (hp : (C.gates.get i).inputs = [4,j] ∨ (C.gates.get i).inputs = [j,4]) :
      False := by
    by_cases hj : j = 4
    · subst j
      exact (h2 C i hfan hs hop hread (hp.elim Or.inr Or.inr)) hf
    · by_cases hsmall : j < 9
      · exact (h1 C i j hsmall hj hop (fun l => (hread l).1) hp) hf
      · obtain ⟨D, w, hD, hsize, hfun, hwire⟩ :=
          h3 C i hfan hs hop hread j (Nat.le_of_not_gt hsmall) hp hf
        obtain ⟨x, hz, ho, hfalse⟩ := h4 D w hD hsize hfun
        have htrue := hwire x hz ho
        rw [hfalse] at htrue
        exact Bool.noConfusion htrue
  cases h : (C.gates.get i).inputs with
  | nil => simp [h] at hmem
  | cons a as =>
    cases as with
    | nil =>
      have ha : a = 4 := by simpa [h, eq_comm] using hmem
      subst a
      exact (h2 C i hfan hs hop hread (Or.inl h)) hf
    | cons b bs =>
      cases bs with
      | cons c cs => simp [h] at hlen
      | nil =>
        have hp : a = 4 ∨ b = 4 := by simpa [h, eq_comm] using hmem
        rcases hp with haa | hbb
        · subst a
          exact two b (Or.inl h)
        · subst b
          exact two a (Or.inr h)
