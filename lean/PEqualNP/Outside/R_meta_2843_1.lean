import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2843_1
    (monotoneRows : ∀ (v : Fin 9) (D : Circuit), Monotone2 D →
      (∀ r ∈ ([3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402] : List ℕ),
        let x : Fin 9 → Bool := fun i => r.testBit i.val
        D.eval (List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v]) =
          decide (r ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320] : List ℕ))) →
      14 ≤ D.size)
    (firstNot : ∀ (v : Fin 9) (P D : Circuit), Monotone2 P → FanInTwo D →
      (∀ x : Fin 9 → Bool,
        let w := P.wires (List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v])
        D.eval (w ++ [!(w.getD P.output false)]) = ([((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x x5.1 && x x5.2)) →
      13 ≤ P.size + D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) || x4 x2]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (14 : ℕ) ≤ x1.size := by
  intro C v hFan correct
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have lengthOf (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have splitAtNot (ls : List Gate) :
      (∀ g ∈ ls, g.op ≠ GateOp.not) ∨
      ∃ pre g post, ls = pre ++ g :: post ∧ g.op = GateOp.not ∧
        ∀ h ∈ pre, h.op ≠ GateOp.not := by
    induction ls with
    | nil => exact Or.inl (by simp)
    | cons g gs ih =>
      by_cases h : g.op = GateOp.not
      · exact Or.inr ⟨[], g, gs, rfl, h, by simp⟩
      rcases ih with ih | ⟨pre, N, post, rfl, hop, hpre⟩
      · exact Or.inl (fun a ha => (List.mem_cons.mp ha).elim (fun e => e.symm ▸ h) (ih a))
      · refine Or.inr ⟨g :: pre, N, post, rfl, hop, ?_⟩
        intro a ha
        exact (List.mem_cons.mp ha).elim (fun e => e.symm ▸ h) (hpre a)
  have monotone (ls : List Gate) (o : ℕ) (sub : ∀ g ∈ ls, g ∈ C.gates)
      (hn : ∀ g ∈ ls, g.op ≠ GateOp.not) : Monotone2 ⟨ls, o⟩ := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hFan g (sub g hg)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    exact ⟨hop.elim Or.inl (fun h => Or.inr (h.resolve_right (hn g hg))), hlen⟩
  rcases splitAtNot C.gates with hn | ⟨pre, N, post, hgs, hop, hpre⟩
  · apply monotoneRows v C (monotone C.gates C.output (fun _ h => h) hn)
    intro r hr
    dsimp only
    rw [correct]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · let P : Circuit := ⟨pre, N.inputs.headD (11 + pre.length)⟩
    let Q : Circuit := ⟨post, C.output⟩
    have hm : Monotone2 P := monotone pre _ (fun g hg => by simp [hgs, hg]) hpre
    have hf : FanInTwo Q := by
      intro g hg
      change g ∈ post at hg
      exact hFan g (by simp [hgs, hg])
    have hbound := firstNot v P Q hm hf (by
      intro x
      dsimp only
      let raw := List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v]
      let w := pre.foldl step raw
      have hl : w.length = 11 + pre.length := by simp [w, raw, lengthOf]
      have hv : N.op.eval (N.inputs.map fun i => w.getD i false) =
          !(w.getD P.output false) := by
        rw [hop]
        change (!((N.inputs.map fun i => w.getD i false).headD false)) =
          !(w.getD (N.inputs.headD (11 + pre.length)) false)
        cases hi : N.inputs with
        | nil => simp [← hl, List.getD_eq_getElem?_getD]
        | cons i is => rfl
      have eqn := correct x
      change (C.gates.foldl step raw).getD C.output false = _ at eqn
      rw [hgs, List.foldl_append, List.foldl_cons] at eqn
      change (post.foldl step (w ++ [N.op.eval (N.inputs.map fun i => w.getD i false)])).getD
        C.output false = _ at eqn
      rw [hv] at eqn
      exact eqn)
    change 13 ≤ pre.length + post.length at hbound
    change 14 ≤ C.gates.length
    simp [hgs]; omega
