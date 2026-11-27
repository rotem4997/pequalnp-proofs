import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 24000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_651_1 :
    (∀ (D : Circuit) (p : Fin 10 → Fin 10) (h : Bool → Bool), FanInTwo D → D.size ≤ 18 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn (x ∘ p) ++ [h (x 0)]) ≠
        (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) →
    (∀ (D : Circuit) (p : Fin 10 → Fin 10) (b : Bool), FanInTwo D → D.size ≤ 18 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn (x ∘ p) ++ [if b then x 0 && x 1 else x 0 || x 1]) ≠
        (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) →
    (∀ (D : Circuit) (p : Fin 10 → Fin 10), FanInTwo D → D.size ≤ 18 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn (x ∘ p) ++ [x 0 || x 2]) ≠
        (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) →
    (∀ (D : Circuit) (p : Fin 10 → Fin 10), FanInTwo D → D.size ≤ 18 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) ≠
        (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) →
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 19 := by
  let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  intro unary edge nonedgeOr nonedgeAnd hc
  obtain ⟨⟨gs, out⟩, ok, budget, computes⟩ := hc
  change ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = F x at computes
  let a : Fin 10 → Fin 10 := ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5]
  have aInv : ∀ x, F (x ∘ a) = F x := by
    intro x
    dsimp [F, a, Function.comp_def]
    ac_rfl
  let b : Fin 10 → Fin 10 := ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7]
  have bInv : ∀ x, F (x ∘ b) = F x := by
    intro x
    dsimp [F, b, Function.comp_def]
    ac_rfl
  let move : List Bool → Fin 10 → Fin 10 := fun word i =>
    word.foldl (fun j bit => if bit then b j else a j) i
  have moveInv : ∀ word x, F (x ∘ move word) = F x := by
    intro word
    induction word with
    | nil => intro x; rfl
    | cons bit rest ih =>
      intro x
      cases bit
      · exact (aInv (x ∘ move rest)).trans (ih x)
      · exact (bInv (x ∘ move rest)).trans (ih x)
  -- Words in the two graph symmetries cover the three orbits of ordered pairs.
  let routes := (List.range 7).flatMap fun n =>
    (List.range (2 ^ n)).map fun m => (List.range n).map m.testBit
  have cover : ∀ i j : Fin 10, routes.any (fun w =>
      decide (move w i = 0 ∧ (move w j = 0 ∨ move w j = 1 ∨ move w j = 2))) = true := by decide
  have orbit (i j : Fin 10) : ∃ p : Fin 10 → Fin 10, p i = 0 ∧
      (p j = 0 ∨ p j = 1 ∨ p j = 2) ∧ ∀ x, F (x ∘ p) = F x := by
    obtain ⟨w, _, hw⟩ := List.any_eq_true.mp (cover i j)
    have h := of_decide_eq_true hw
    exact ⟨move w, h.1, h.2, moveInv w⟩
  -- Give the first gate value to the remaining circuit as its eleventh input.
  cases gs with
  | nil =>
    let D := Circuit.mk [] out
    obtain ⟨x, hx⟩ := unary D id (fun _ => false) (by intro g hg; simp [D] at hg)
      (by change 0 ≤ 18; decide)
    apply hx
    change ((List.ofFn x) ++ [false]).getD out false = F x
    rw [← computes x]
    change _ = (List.ofFn x).getD out false
    by_cases h : out < 10
    · exact List.getD_append _ _ _ _ (by simpa)
    · by_cases e : out = 10
      · subst out; rfl
      · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
  | cons g gs =>
    let D := Circuit.mk gs out
    have hD : FanInTwo D := fun t ht => ok t (List.mem_cons_of_mem _ ht)
    have sz : D.size ≤ 18 := by
      change gs.length ≤ 18
      change (g :: gs).length ≤ 19 at budget
      simp only [List.length_cons] at budget
      omega
    let V := fun x : Fin 10 → Bool =>
      g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false))
    have run (p : Fin 10 → Fin 10) (hp : ∀ x, F (x ∘ p) = F x) (x : Fin 10 → Bool) :
        D.eval (List.ofFn (x ∘ p) ++ [V (x ∘ p)]) = F x :=
      (computes (x ∘ p)).trans (hp x)
    have noUnary (i : Fin 10) (h : Bool → Bool) (hv : ∀ x, V x = h (x i)) : False := by
      obtain ⟨p, hi, _, hp⟩ := orbit i i
      obtain ⟨x, hx⟩ := unary D p h hD sz
      apply hx
      simpa only [hv, Function.comp_apply, hi] using run p hp x
    have noBinary (i j : Fin 10) (b : Bool)
        (hv : ∀ x, V x = if b then x i && x j else x i || x j) : False := by
      obtain ⟨p, hi, hj, hp⟩ := orbit i j
      rcases hj with hj | hj | hj
      · obtain ⟨x, hx⟩ := unary D p id hD sz
        apply hx
        simpa [hv, hi, hj, Function.comp_def] using run p hp x
      · obtain ⟨x, hx⟩ := edge D p b hD sz
        apply hx
        simpa only [hv, Function.comp_apply, hi, hj] using run p hp x
      · cases b with
        | false =>
          obtain ⟨x, hx⟩ := nonedgeOr D p hD sz
          apply hx
          simpa only [hv, Function.comp_apply, hi, hj, Bool.false_eq_true, ite_false] using run p hp x
        | true =>
          obtain ⟨x, hx⟩ := nonedgeAnd D p hD sz
          apply hx
          simpa only [hv, Function.comp_apply, hi, hj, ite_true] using run p hp x
    obtain ⟨op, bound⟩ := ok g List.mem_cons_self
    change g.inputs.length ≤ 2 at bound
    have readValid (x : Fin 10 → Bool) (w : ℕ) (hw : w < 10) :
        (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa)]
      simp only [List.getElem_ofFn]
    have readMissing (x : Fin 10 → Bool) (w : ℕ) (hw : ¬ w < 10) :
        (List.ofFn x).getD w false = false := List.getD_eq_default _ _ (by simpa using hw)
    rcases he : g.inputs with _ | ⟨u, tail⟩
    · exact noUnary 0 (fun _ => g.op.eval []) (by intro x; simp [V, he])
    rcases ht : tail with _ | ⟨v, tail'⟩
    · by_cases hu : u < 10
      · exact noUnary ⟨u, hu⟩ (fun bit => g.op.eval [bit]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readValid _ _ hu])
      · exact noUnary 0 (fun _ => g.op.eval [false]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readMissing _ _ hu])
    have empty : tail' = [] := by simpa [he, ht] using bound
    subst tail'
    by_cases hu : u < 10
    · by_cases hv : v < 10
      · have op' : g.op = .and ∨ g.op = .or ∨ g.op = .not := op
        rcases op' with hop | hop | hop
        · apply noBinary ⟨u, hu⟩ ⟨v, hv⟩ true
          intro x
          simp only [V, he, ht, List.map_cons, List.map_nil, hop, readValid _ _ hu, readValid _ _ hv]
          change [x ⟨u, hu⟩, x ⟨v, hv⟩].all id = _
          simp
        · apply noBinary ⟨u, hu⟩ ⟨v, hv⟩ false
          intro x
          simp only [V, he, ht, List.map_cons, List.map_nil, hop, readValid _ _ hu, readValid _ _ hv]
          change [x ⟨u, hu⟩, x ⟨v, hv⟩].any id = _
          simp
        · apply noUnary ⟨u, hu⟩ (! ·)
          intro x
          simp only [V, he, ht, List.map_cons, List.map_nil, hop, readValid _ _ hu]
          rfl
      · exact noUnary ⟨u, hu⟩ (fun s => g.op.eval [s, false]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readValid _ _ hu, readMissing _ _ hv])
    · by_cases hv : v < 10
      · exact noUnary ⟨v, hv⟩ (fun s => g.op.eval [false, s]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readMissing _ _ hu, readValid _ _ hv])
      · exact noUnary 0 (fun _ => g.op.eval [false, false]) (by intro x; simp only [V, List.map_cons, List.map_nil, he, ht, readMissing _ _ hu, readMissing _ _ hv])
