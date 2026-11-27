import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8053

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem and_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a && b) ≤ (a' && b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem or_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a || b) ≤ (a' || b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    exact and_mono _ _ _ _ (h a) ih

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    exact or_mono _ _ _ _ (h a) ih

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def R (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, W.getD i false ≤ W'.getD i false

theorem step_R (W W' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : R W W') : R (step W g) (step W' g) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => W.getD i false) ≤
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · exact all_mono _ _ _ hle
    · exact any_mono _ _ _ hle
  refine ⟨by simp [step, hl], fun i => ?_⟩
  simp only [step, getD_snoc, hl]
  split_ifs
  · exact hle i
  · exact hv
  · exact le_refl _

theorem fold_R (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, R W W' → R (gs.foldl step W) (gs.foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_R W W' g (hgs g List.mem_cons_self) h)

theorem R_append {l1 l1' l2 l2' : List Bool} (h1 : R l1 l1') (h2 : R l2 l2') :
    R (l1 ++ l2) (l1' ++ l2') := by
  obtain ⟨hl1, h1⟩ := h1
  obtain ⟨hl2, h2⟩ := h2
  refine ⟨by simp [hl1, hl2], fun i => ?_⟩
  by_cases hi : i < l1.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl1 ▸ hi)]
    exact h1 i
  · have hi' : l1.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ (hl1 ▸ hi'), hl1]
    exact h2 _

theorem R_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i ≤ g i) :
    R (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem eval_mono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (l l' : List Bool)
    (h : R l l') : C.eval l ≤ C.eval l' := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  show (C.wires l).getD C.output false ≤ (C.wires l').getD C.output false
  rw [wires_eq, wires_eq]
  exact (fold_R C.gates hops _ _ h).2 C.output

end PEqualNP.Outside.L_meta_8053

theorem PEqualNP.Outside.L_meta_8053 : have x1 : (Fin (42 : ℕ) → Bool) → List Bool := fun (x1 : Fin (42 : ℕ) → Bool) =>   have x2 : Fin (7 : ℕ) → ℕ → Bool := fun (x2 : Fin (7 : ℕ)) (x3 : ℕ) => x1 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x2 + x3) % (21 : ℕ)));   (List.ofFn x1 ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ)) ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ) || x2 x3 (20 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → Monotone fun (x4 : Fin (42 : ℕ) → Bool) => x2.eval (x1 x4) := by
  dsimp only
  intro C hm a b hab
  apply PEqualNP.Outside.L_meta_8053.eval_mono C hm
  refine PEqualNP.Outside.L_meta_8053.R_append
    (PEqualNP.Outside.L_meta_8053.R_append (PEqualNP.Outside.L_meta_8053.R_ofFn a b hab)
      (PEqualNP.Outside.L_meta_8053.R_ofFn _ _ fun k => ?_))
    (PEqualNP.Outside.L_meta_8053.R_ofFn _ _ fun k => ?_)
  · exact PEqualNP.Outside.L_meta_8053.or_mono _ _ _ _ (hab _) (hab _)
  · first
    | exact PEqualNP.Outside.L_meta_8053.or_mono _ _ _ _
        (PEqualNP.Outside.L_meta_8053.or_mono _ _ _ _ (hab _) (hab _)) (hab _)
    | exact PEqualNP.Outside.L_meta_8053.or_mono _ _ _ _ (hab _)
        (PEqualNP.Outside.L_meta_8053.or_mono _ _ _ _ (hab _) (hab _))
