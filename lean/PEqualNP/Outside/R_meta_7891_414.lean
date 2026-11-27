import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_7891_414
  (elim : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (S : Finset ℕ), FanInTwo C →
    (∀ j ∈ S, ∃ g : Gate, C.gates[j]? = some g ∧ v.val ∈ g.inputs ∧
      (g.op = GateOp.not → g.inputs.head? = some v.val)) →
    (∃ c : Bool, ∀ x : Fin n → Bool, x v = false → C.eval (List.ofFn x) = c) ∨
    ∃ D : Circuit, FanInTwo D ∧ D.size + S.card ≤ C.size ∧
      ∀ x : Fin n → Bool, x v = false → D.eval (List.ofFn x) = C.eval (List.ofFn x))
  (small : ∀ (v : Fin 10) (C : Circuit) (b : Bool), FanInTwo C →
    C.size + (if b then 1 else 0) ≤ 15 →
    ∃ x : Fin 10 → Bool, x v = false ∧ (if b then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) ≠ (fun x : Fin 10 → Bool =>
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x)
  (complete : ∀ (C : Circuit) (d : ℕ → Bool), Monotone2 C →
    (∀ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), C.eval (List.ofFn (Function.update (fun i : Fin 10 => r.testBit i.val) 0
      (r.testBit 0 && d r))) = true) →
    (∀ r ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), C.eval (List.ofFn (Function.update (fun i : Fin 10 => r.testBit i.val) 0
      (r.testBit 0 && d r))) = false) →
    ∀ x : Fin 10 → Bool, x 0 = false → C.eval (List.ofFn x) = (fun x : Fin 10 → Bool =>
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x)
  (restricted : ∀ (C : Circuit) (w : ℕ), IsAO2 10 C → 16 ≤ C.size ∧ C.size ≤ 18 →
    (w ≠ 0 ∧ w < 10+C.size ∧ ∀ j g, 10+j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
    (∀ S : Finset ℕ, (∀ j ∈ S, ∃ g : Gate, C.gates[j]? = some g ∧ 0 ∈ g.inputs) → S.card ≤ 2) →
    let x := fun (r : ℕ) (i : Fin 10) => r.testBit i.val
    let d := fun r => (C.wires (List.ofFn (Function.update (x r) 0 false))).getD w false
    let f := fun r => circuitFun 10 C (Function.update (x r) 0 (x r 0 && d r))
    (∀ r ∈ ([2,16,32] : List ℕ), d r = true) →
    ¬ ((∀ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), f r = true) ∧ (∀ r ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), f r = false))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 →     (16 : ℕ) ≤ x1.size ∧ x1.size ≤ (18 : ℕ) →       (x2 ≠ (0 : ℕ) ∧ x2 < (10 : ℕ) + x1.size ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x5 ≤ x2 → x1.gates[x5]? = Option.some x6 → (0 : ℕ) ∉ x6.inputs) →         have x6 : ℕ → Fin (10 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (10 : ℕ)) => x6.testBit ↑x7;         have x7 : ℕ → Bool := fun (x7 : ℕ) => (x1.wires (List.ofFn (Function.update (x6 x7) (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false;         have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update (x6 x8) (0 : Fin (10 : ℕ)) (x6 x8 (0 : Fin (10 : ℕ)) && x7 x8));         (∀ x9 ∈ [(2 : ℕ), (16 : ℕ), (32 : ℕ)], x7 x9 = Bool.true) → ¬((∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x8 x10 = Bool.true) ∧ ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x8 x10 = Bool.false) := by
  classical
  intro C w hC hsize sched
  dsimp only
  intro neigh tests
  let d : ℕ → Bool := fun r => (C.wires (List.ofFn (Function.update (fun i : Fin 10 => r.testBit i.val) 0 false))).getD w false
  have hmono : Monotone2 C := by
    intro g hg
    have hop := hC.1 g hg
    have hlen := hC.2.2 g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨hop, by omega⟩
  have hfan : FanInTwo C := by
    intro g hg
    have hop := hC.1 g hg
    have hlen := hC.2.2 g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨Or.elim hop (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)), by omega⟩
  have hp : ∀ r ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List ℕ), C.eval (List.ofFn (Function.update (fun i : Fin 10 => r.testBit i.val) 0
      (r.testBit 0 && d r))) = true := tests.1
  have hn : ∀ r ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ), C.eval (List.ofFn (Function.update (fun i : Fin 10 => r.testBit i.val) 0
      (r.testBit 0 && d r))) = false := tests.2
  have correct := complete C d hmono hp hn
  have fanout : ∀ S : Finset ℕ, (∀ j ∈ S, ∃ g : Gate, C.gates[j]? = some g ∧ 0 ∈ g.inputs) → S.card ≤ 2 := by
    intro S hS
    by_contra h
    have hs3 : 3 ≤ S.card := by omega
    have valid : ∀ j ∈ S, ∃ g : Gate, C.gates[j]? = some g ∧ (0 : Fin 10).val ∈ g.inputs ∧
        (g.op = GateOp.not → g.inputs.head? = some (0 : Fin 10).val) := by
      intro j hj
      obtain ⟨g,hg,hin⟩ := hS j hj
      refine ⟨g,hg,hin,?_⟩
      intro hnot
      have hop := hC.1 g (List.mem_of_getElem? hg)
      rcases hop with ha | ho
      · cases ha.symm.trans hnot
      · cases ho.symm.trans hnot
    rcases elim 10 C 0 S hfan valid with ⟨c,hconst⟩ | ⟨D,hD,hDsize,heq⟩
    · cases c with
      | false =>
        let x : Fin 10 → Bool := fun i => decide (i=2 ∨ i=3)
        have hx : x 0 = false := by decide
        have hf : (fun x : Fin 10 → Bool =>
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x = true := by decide
        have hc := correct x hx
        rw [hconst x hx,hf] at hc
        contradiction
      | true =>
        let x : Fin 10 → Bool := fun _ => false
        have hx : x 0 = false := rfl
        have hf : (fun x : Fin 10 → Bool =>
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x = false := by decide
        have hc := correct x hx
        rw [hconst x hx,hf] at hc
        contradiction
    · have hs : D.size + (if false then 1 else 0) ≤ 15 := by simp; omega
      obtain ⟨x,hx,hn⟩ := small 0 D false hD hs
      have hc := correct x hx
      have hDcorrect := (heq x hx).trans hc
      simp only [Bool.false_eq_true,ite_false] at hn
      exact hn hDcorrect
  exact (restricted C w hC hsize sched fanout neigh) tests
