import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4015

def p0 (v w : Fin 10) : Bool :=
  match v.val with
  | 0 => w == 2 || w == 4
  | 1 => w == 6
  | 2 => w == 0 || w == 3
  | 3 => w == 8
  | 4 => w == 9
  | 5 => w == 7
  | 6 => w == 8
  | 7 => w == 9
  | 8 => w == 5
  | _ => w == 7

def p1 (v w : Fin 10) : Bool :=
  (w == v) || p0 v w

def petEdge (x7 : Fin (10 : ℕ) → Bool) : Bool :=
  x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))

theorem p_agree (v w : Fin 10) (hw : w ≠ v) : p0 v w = p1 v w := by
  have hbeq : (w == v) = false := beq_false_of_ne hw
  simp [p1, hbeq]

theorem p_or (v : Fin 10) : (p0 v 0 || p0 v 2) = (p1 v 0 || p1 v 2) := by
  revert v
  decide

theorem edge_p0 (v : Fin 10) : petEdge (p0 v) = false := by
  revert v
  decide

theorem edge_p1 (v : Fin 10) : petEdge (p1 v) = true := by
  revert v
  decide

end PEqualNP.Outside.L_meta_4015

theorem PEqualNP.Outside.L_meta_4015 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ¬Function.Surjective x2 → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro x1 x2 _ _ hns
  have hv : ∃ v : Fin 10, ∀ i : Fin 10, x2 i ≠ v := by
    by_contra h
    apply hns
    intro v
    by_contra hi
    exact h ⟨v, fun i he => hi ⟨i, he⟩⟩
  obtain ⟨v, hv⟩ := hv
  have heq : x1.eval (List.ofFn (PEqualNP.Outside.L_meta_4015.p0 v ∘ x2) ++ [PEqualNP.Outside.L_meta_4015.p0 v 0 || PEqualNP.Outside.L_meta_4015.p0 v 2]) =
      x1.eval (List.ofFn (PEqualNP.Outside.L_meta_4015.p1 v ∘ x2) ++ [PEqualNP.Outside.L_meta_4015.p1 v 0 || PEqualNP.Outside.L_meta_4015.p1 v 2]) := by
    have hcomp : PEqualNP.Outside.L_meta_4015.p0 v ∘ x2 = PEqualNP.Outside.L_meta_4015.p1 v ∘ x2 := by
      funext i
      exact PEqualNP.Outside.L_meta_4015.p_agree v (x2 i) (hv i)
    rw [hcomp, PEqualNP.Outside.L_meta_4015.p_or v]
  by_cases h0 : x1.eval (List.ofFn (PEqualNP.Outside.L_meta_4015.p0 v ∘ x2) ++ [PEqualNP.Outside.L_meta_4015.p0 v 0 || PEqualNP.Outside.L_meta_4015.p0 v 2]) =
      PEqualNP.Outside.L_meta_4015.petEdge (PEqualNP.Outside.L_meta_4015.p0 v)
  · refine ⟨PEqualNP.Outside.L_meta_4015.p1 v, ?_⟩
    change x1.eval (List.ofFn (PEqualNP.Outside.L_meta_4015.p1 v ∘ x2) ++ [PEqualNP.Outside.L_meta_4015.p1 v 0 || PEqualNP.Outside.L_meta_4015.p1 v 2]) ≠
      PEqualNP.Outside.L_meta_4015.petEdge (PEqualNP.Outside.L_meta_4015.p1 v)
    rw [← heq, h0, PEqualNP.Outside.L_meta_4015.edge_p0 v, PEqualNP.Outside.L_meta_4015.edge_p1 v]
    decide
  · exact ⟨PEqualNP.Outside.L_meta_4015.p0 v, h0⟩
