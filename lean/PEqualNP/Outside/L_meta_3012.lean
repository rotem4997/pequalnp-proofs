import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3012_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_le {w v : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w v) (i : ℕ) :
    w.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w v : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx2
    obtain ⟨i, hi, rfl⟩ := hx2
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w v : List Bool, List.Forall₂ (fun a b => a ≤ b) w v →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step v) := by
  induction gs with
  | nil => intro w v h; simpa using h
  | cons g gs ih =>
    intro w v h
    simp only [List.foldl_cons]
    apply ih (fun g2 hg2 => hgs g2 (List.mem_cons_of_mem _ hg2))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem mono (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (o : ℕ) :
    (gs.foldl step (List.ofFn x)).getD o false ≤ (gs.foldl step (List.ofFn y)).getD o false := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact bool_le.mpr (hxy _)
  exact getD_le (fold_le gs hgs _ _ h0) o

end PEqualNP.Outside.L_meta_3012_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3012_aux in
theorem PEqualNP.Outside.L_meta_3012 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : (Fin x1 → Bool) → Bool), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ (x5 : Fin x1 → Bool), x3 x5 = Bool.true → (∀ x7 ≤ x5, x3 x7 = Bool.true → x7 = x5) → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), x3 x6 = Bool.false → (∀ (x8 : Fin x1 → Bool), x6 ≤ x8 → x3 x8 = Bool.false → x8 = x6) → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x3 x7 := by
  rintro n ⟨gs, out⟩ P hC hmin hmax x
  have hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    exact hC.1 g hg
  have hm : ∀ y z : Fin n → Bool, y ≤ z → Circuit.eval ⟨gs, out⟩ (List.ofFn y) = true →
      Circuit.eval ⟨gs, out⟩ (List.ofFn z) = true := by
    intro y z h hy
    exact bool_le.mp (mono n gs hgs y z (fun i => bool_le.mp (h i)) out) hy
  cases hx : P x with
  | true =>
    obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT (fun w => P w = true) x hx
    exact hm y x hyx (hmin y hy.1 (fun w hw hPw => le_antisymm hw (hy.2 hPw hw)))
  | false =>
    obtain ⟨z, hxz, hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun w => P w = false) x hx
    have h1 := hmax z hz.1 (fun w hw hPw => le_antisymm (hz.2 hPw hw) hw)
    cases h2 : Circuit.eval ⟨gs, out⟩ (List.ofFn x) with
    | false => rfl
    | true =>
      have h3 := hm x z hxz h2
      rw [h1] at h3
      exact absurd h3 Bool.false_ne_true
