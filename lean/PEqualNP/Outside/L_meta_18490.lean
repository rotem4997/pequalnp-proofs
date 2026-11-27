import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18490_aux

open PEqualNP.CircuitLowerBounds

theorem getD_zip (w1 w2 : List Bool) (h : w1.length = w2.length) (i : ℕ) :
    (List.zipWith (fun a b => a || b) w1 w2).getD i false = (w1.getD i false || w2.getD i false) := by
  induction w1 generalizing w2 i with
  | nil => cases w2 <;> simp_all
  | cons a t ih =>
    cases w2 with
    | nil => simp at h
    | cons b s =>
      cases i with
      | zero => simp
      | succ i => simp only [List.zipWith_cons_cons, List.getD_cons_succ]; exact ih s (by simpa using h) i

theorem any_or (l : List ℕ) (f g : ℕ → Bool) :
    (l.map fun i => f i || g i).any id = ((l.map f).any id || (l.map g).any id) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.any_cons, ih, id]; cases f a <;> cases g a <;> simp

theorem fold_hom (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.or) (w1 w2 : List Bool)
    (h : w1.length = w2.length) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.zipWith (fun a b => a || b) w1 w2) =
    List.zipWith (fun a b => a || b)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
  induction gs generalizing w1 w2 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hop : g.op = GateOp.or := hg g (by simp)
    have e : (List.zipWith (fun a b => a || b) w1 w2 ++
        [g.op.eval (g.inputs.map fun i => (List.zipWith (fun a b => a || b) w1 w2).getD i false)]) =
        List.zipWith (fun a b => a || b) (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
          (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) := by
      rw [List.zipWith_append h]
      simp only [getD_zip w1 w2 h, hop, GateOp.eval, any_or, List.zipWith_cons_cons, List.zipWith_nil_left]
    rw [e]
    exact ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (by simp [h])

theorem len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons]; simp; omega

theorem eval_hom (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.or) {n : ℕ} (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) = (C.eval (List.ofFn a) || C.eval (List.ofFn b)) := by
  have hz : (List.ofFn fun i => a i || b i) = List.zipWith (fun a b => a || b) (List.ofFn a) (List.ofFn b) := by
    apply List.ext_getElem <;> simp
  unfold Circuit.eval Circuit.wires
  rw [hz, fold_hom C.gates hg _ _ (by simp), getD_zip]
  rw [len_fold, len_fold]; simp

end PEqualNP.Outside.L_meta_18490_aux

open PEqualNP.Outside.L_meta_18490_aux in
theorem PEqualNP.Outside.L_meta_18490 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → ∃ (x5 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x6 ∈ x5, x6.1.Nonempty ∧ x6.2.Nonempty ∧ ∀ x8 ∈ x6.1, ∀ x10 ∈ x6.2, (↑x10 + (21 : ℕ) - ↑x8) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ (∀ (x6 x7 : Fin (21 : ℕ)), (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x9 ∈ x5, x6 ∈ x9.1 ∧ x7 ∈ x9.2) ∧ ∑ x6 ∈ x5, (x6.1.card + x6.2.card - (1 : ℕ)) ≤ List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x6.op Bool.false Bool.true Bool.false (fun (x7 : ℕ) => Bool.false) Bool.false) x1.gates + (1 : ℕ) := by
  intro C hm hna hc
  exfalso
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hgm
    have h1 := (hm g hgm).1
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hgm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd ⟨i, h1⟩ hna
    · exact h1
  have hs : ∀ u : Fin 42, C.eval (List.ofFn fun i : Fin 42 => decide (i = u)) = false := by
    intro u
    by_contra h
    simp only [Bool.not_eq_false] at h
    obtain ⟨a, b, ⟨h1, h2, _⟩, h3, h4⟩ := (hc _).mp h
    simp at h3 h4
    subst h3; subst h4
    omega
  have h := eval_hom C hg (fun i : Fin 42 => decide (i = 0)) (fun i : Fin 42 => decide (i = 21))
  rw [hs, hs] at h
  have ht : C.eval (List.ofFn fun i : Fin 42 => decide (i = 0) || decide (i = 21)) = true := by
    rw [hc]
    exact ⟨0, 21, ⟨by decide, by decide, by decide⟩, by decide, by decide⟩
  rw [h] at ht
  exact absurd ht (by decide)
