import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8273_aux

open PEqualNP.CircuitLowerBounds

theorem step (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w v : List Bool), w.length = v.length →
      (∀ i, w.getD i false = true → v.getD i false = true) →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).length ∧
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).getD i false = true := by
  induction gs with
  | nil => intro w v hl hm; exact ⟨hl, hm⟩
  | cons g gs ih =>
    intro w v hl hm
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · have hab : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
        rcases hg g (List.mem_cons_self) with h | h
        · rw [h]; simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
          rintro H x ⟨j, hj, rfl⟩
          exact hm j (H _ ⟨j, hj, rfl⟩)
        · rw [h]; simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
          rintro ⟨x, ⟨j, hj, rfl⟩, hx⟩
          exact ⟨_, ⟨j, hj, rfl⟩, hm j hx⟩
      intro i hi
      rcases lt_trichotomy i w.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ h1)]
        exact hm i hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ le_rfl] at hi
        rw [hl, List.getD_append_right _ _ _ _ le_rfl] at *
        simp at hi ⊢
        exact hab hi
      · rw [List.getD_eq_default] at hi
        · simp at hi
        · simp; omega

theorem base {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ j, x j = true → y j = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases h : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, Option.getD] at hi ⊢
    simp_all
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    simp at hi

theorem mono_eval (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {n : ℕ}
    (x y : Fin n → Bool) (hxy : ∀ j, x j = true → y j = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact (step C.gates hg (List.ofFn x) (List.ofFn y) (by simp) (base x y hxy)).2 C.output

theorem lc_mono {n : ℕ} (a b : Bool) (f g : Fin n → Bool) (hab : a = true → b = true)
    (hfg : ∀ j, f j = true → g j = true) :
    ∀ i, Fin.lastCases a f i = true → Fin.lastCases b g i = true := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa using hab
  | cast j => simpa using hfg j

theorem or_mono (a b c d : Bool) (h1 : a = true → c = true) (h2 : b = true → d = true) :
    (a || b) = true → (c || d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

def G (x1 : Fin 42) (x2 x3 : Fin 43) (x4 : Circuit) : (Fin 42 → Bool) → Bool :=
  fun (x7 : Fin (42 : ℕ) → Bool) =>
      have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x7 (0 : Fin (42 : ℕ)) || x7 x1) x7 x8;
      x4.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x2 || x8 x3) x8 x9)

theorem G_mono (x1 : Fin 42) (x2 x3 : Fin 43) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (f g : Fin 42 → Bool) (hfg : ∀ k, f k = true → g k = true) : G x1 x2 x3 C f = true → G x1 x2 x3 C g = true := by
  have h8 := lc_mono _ _ f g (or_mono _ _ _ _ (hfg 0) (hfg x1)) hfg
  exact mono_eval C hC _ _ (lc_mono _ _ _ _ (or_mono _ _ _ _ (h8 x2) (h8 x3)) h8)

theorem core (x5 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop) (x7 : (Fin 42 → Bool) → Bool)
    (hF : ∀ f g : Fin 42 → Bool, (∀ k, f k = true → g k = true) → x7 f = true → x7 g = true) :
    ((∀ (x8 x9 : Fin (42 : ℕ)), x5 x8 x9 → (x7 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = x8 ∨ x11 = x9)) = Bool.true) ∧         ∀ (x8 x9 : Fin (21 : ℕ) → Bool),           have x10 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x10 x11 : Fin (21 : ℕ)) => x5 (Fin.castAdd (21 : ℕ) x10) (Fin.natAdd (21 : ℕ) x11);           (∀ (x11 : Fin (21 : ℕ)), x8 x11 = Bool.true ↔ ∀ (x12 : Fin (21 : ℕ)), x9 x12 = Bool.true → ¬x10 x11 x12) → (∀ (x12 : Fin (21 : ℕ)), x9 x12 = Bool.true ↔ ∀ (x13 : Fin (21 : ℕ)), x8 x13 = Bool.true → ¬x10 x13 x12) → (x7 fun (x13 : Fin (42 : ℕ)) => Fin.addCases x8 x9 x13) = Bool.false) →       ∀ (x9 : Fin (42 : ℕ) → Bool), x7 x9 = Bool.true ↔ ∃ (x10 : Fin (42 : ℕ)) (x11 : Fin (42 : ℕ)), x5 x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true := by
  classical
  rintro ⟨h1, h2⟩ x9
  constructor
  · intro hx
    by_contra hne
    simp only [not_exists, not_and] at hne
    let B0 : Fin 21 → Bool := fun j => x9 (Fin.natAdd 21 j)
    let A : Fin 21 → Bool := fun i => decide (∀ j, B0 j = true → ¬ x5 (Fin.castAdd 21 i) (Fin.natAdd 21 j))
    let B : Fin 21 → Bool := fun j => decide (∀ i, A i = true → ¬ x5 (Fin.castAdd 21 i) (Fin.natAdd 21 j))
    have hB0 : ∀ j, B0 j = true → B j = true := by
      intro j hj
      simp only [B, decide_eq_true_eq]
      intro i hi
      simp only [A, decide_eq_true_eq] at hi
      exact hi j hj
    have hA : ∀ i, A i = true ↔ ∀ j, B j = true → ¬ x5 (Fin.castAdd 21 i) (Fin.natAdd 21 j) := by
      intro i
      constructor
      · intro hi j hj
        simp only [B, decide_eq_true_eq] at hj
        exact hj i hi
      · intro h
        simp only [A, decide_eq_true_eq]
        intro j hj
        exact h j (hB0 j hj)
    have hBB : ∀ j, B j = true ↔ ∀ i, A i = true → ¬ x5 (Fin.castAdd 21 i) (Fin.natAdd 21 j) := by
      intro j
      simp only [B, decide_eq_true_eq]
    have hfalse := h2 A B hA hBB
    have hle : ∀ k, x9 k = true → Fin.addCases A B k = true := by
      intro k
      refine Fin.addCases (m := 21) (n := 21) (fun i => ?_) (fun j => ?_) k
      · intro hk
        simp only [Fin.addCases_left, A, decide_eq_true_eq]
        intro j hj hx5
        exact hne _ _ hx5 hk hj
      · intro hk
        simp only [Fin.addCases_right]
        exact hB0 j hk
    have := hF x9 _ hle hx
    rw [hfalse] at this
    exact Bool.false_ne_true this
  · rintro ⟨a, b, hab, ha, hb⟩
    apply hF _ _ _ (h1 a b hab)
    intro k hk
    simp only [decide_eq_true_eq] at hk
    rcases hk with rfl | rfl <;> assumption

end PEqualNP.Outside.L_meta_8273_aux

open PEqualNP.Outside.L_meta_8273_aux in
theorem PEqualNP.Outside.L_meta_8273 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop),   PEqualNP.MetaComplexity.Monotone2 x4 →     have x7 : (Fin (42 : ℕ) → Bool) → Bool := fun (x7 : Fin (42 : ℕ) → Bool) =>       have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x7 (0 : Fin (42 : ℕ)) || x7 x1) x7 x8;       x4.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x2 || x8 x3) x8 x9);     ((∀ (x8 x9 : Fin (42 : ℕ)), x5 x8 x9 → (x7 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = x8 ∨ x11 = x9)) = Bool.true) ∧         ∀ (x8 x9 : Fin (21 : ℕ) → Bool),           have x10 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x10 x11 : Fin (21 : ℕ)) => x5 (Fin.castAdd (21 : ℕ) x10) (Fin.natAdd (21 : ℕ) x11);           (∀ (x11 : Fin (21 : ℕ)), x8 x11 = Bool.true ↔ ∀ (x12 : Fin (21 : ℕ)), x9 x12 = Bool.true → ¬x10 x11 x12) → (∀ (x12 : Fin (21 : ℕ)), x9 x12 = Bool.true ↔ ∀ (x13 : Fin (21 : ℕ)), x8 x13 = Bool.true → ¬x10 x13 x12) → (x7 fun (x13 : Fin (42 : ℕ)) => Fin.addCases x8 x9 x13) = Bool.false) →       ∀ (x9 : Fin (42 : ℕ) → Bool), x7 x9 = Bool.true ↔ ∃ (x10 : Fin (42 : ℕ)) (x11 : Fin (42 : ℕ)), x5 x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true := by
  intro x1 x2 x3 C x5 hC
  exact core x5 (G x1 x2 x3 C) (G_mono x1 x2 x3 C hC)
