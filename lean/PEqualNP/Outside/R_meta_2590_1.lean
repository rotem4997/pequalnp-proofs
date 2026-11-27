import Mathlib
import PEqualNP.Defs

-- The rows are the fifteen edges and the fifteen maximal independent vertex sets.
-- Give the first gate as an extra input to the remaining eighteen gates.
-- Its operation determines which of the two smaller searches contains the circuit.
theorem PEqualNP.Outside.R_meta_2590_1
    (hand : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (ins : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 18 → ins.length ≤ 2 →
      ∃ r ∈ ([(3, true), (6, true), (12, true), (24, true), (17, true), (33, true), (66, true), (132, true), (264, true), (528, true), (160, true), (640, true), (576, true), (320, true), (288, true), (50, false), (69, false), (104, false), (116, false), (138, false), (201, false), (208, false), (276, false), (385, false), (402, false), (521, false), (548, false), (554, false), (770, false), (773, false)] : List (ℕ × Bool)),
        let w := List.ofFn (fun i : Fin 10 => r.1.testBit i.val)
        D.eval (w ++ [(ins.map (fun i => w.getD i false)).all id]) ≠ r.2)
    (hor : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (ins : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 18 → ins.length ≤ 2 →
      ∃ r ∈ ([(3, true), (6, true), (12, true), (24, true), (17, true), (33, true), (66, true), (132, true), (264, true), (528, true), (160, true), (640, true), (576, true), (320, true), (288, true), (50, false), (69, false), (104, false), (116, false), (138, false), (201, false), (208, false), (276, false), (385, false), (402, false), (521, false), (548, false), (554, false), (770, false), (773, false)] : List (ℕ × Bool)),
        let w := List.ofFn (fun i : Fin 10 => r.1.testBit i.val)
        D.eval (w ++ [(ins.map (fun i => w.getD i false)).any id]) ≠ r.2) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ 19 → ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x := by
  have andVal (w : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval w = w.all id := rfl
  have orVal (w : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval w = w.any id := rfl
  have notVal (w : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.not.eval w = !w.headD false := rfl
  let F := (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let rows : List (ℕ × Bool) := [(3, true), (6, true), (12, true), (24, true), (17, true), (33, true), (66, true), (132, true), (264, true), (528, true), (160, true), (640, true), (576, true), (320, true), (288, true), (50, false), (69, false), (104, false), (116, false), (138, false), (201, false), (208, false), (276, false), (385, false), (402, false), (521, false), (548, false), (554, false), (770, false), (773, false)]
  have values : ∀ r ∈ rows, F (fun i => r.1.testBit i.val) = r.2 := by decide
  intro C
  cases C
  rename_i gs out
  intro mono size computes
  cases gs with
  | nil =>
    have h (m : ℕ) := computes (fun i => m.testBit i.val)
    by_cases bound : out < 10
    · interval_cases out <;> first | exact (by decide : ¬ _) (h 3) | exact (by decide : ¬ _) (h 12)
    · have bad := h 3
      change (List.ofFn (fun i : Fin 10 => (3 : ℕ).testBit i.val)).getD out false = true at bad
      rw [List.getD_eq_default _ _ (by simpa using bound)] at bad
      contradiction
  | cons g gs =>
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, out⟩
    have hm : PEqualNP.MetaComplexity.Monotone2 D :=
      fun t ht => mono t (List.mem_cons_of_mem _ ht)
    have hs : D.size ≤ 18 := by
      change gs.length ≤ 18
      change (g :: gs).length ≤ 19 at size
      simp only [List.length_cons] at size
      omega
    obtain ⟨hop, hlen⟩ := mono g List.mem_cons_self
    have run (r : ℕ × Bool) (hr : r ∈ rows) :
        let w := List.ofFn (fun i : Fin 10 => r.1.testBit i.val)
        D.eval (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) = r.2 :=
      (computes _).trans (values r hr)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with ha | ho
    · obtain ⟨r, hr, bad⟩ := hand D g.inputs hm hs hlen
      exact bad (by simpa only [ha, andVal, orVal, notVal] using run r hr)
    · obtain ⟨r, hr, bad⟩ := hor D g.inputs hm hs hlen
      exact bad (by simpa only [ho, andVal, orVal, notVal] using run r hr)
