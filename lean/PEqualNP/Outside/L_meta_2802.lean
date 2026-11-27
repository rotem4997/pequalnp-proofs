import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2802

open PEqualNP.CircuitLowerBounds

def target (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

def encoded (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 6]

def low (v i : Fin 9) : Bool :=
  (([80, 1, 2, 4, 1, 1, 257, 4, 8] : List ℕ).getD v.val 0).testBit i.val

def high (v i : Fin 9) : Bool := (i == v) || low v i

lemma distinguish :
    ∀ v : Fin 9, target (low v) ≠ target (high v) ∧
      ∀ j : Fin 10, j.val ≠ v.val →
        (encoded (low v)).getD j.val false = (encoded (high v)).getD j.val false := by
  decide

def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

lemma snoc_other (w : List Bool) (b : Bool) (j : ℕ) (different : j ≠ w.length) :
    (w ++ [b]).getD j false = w.getD j false := by
  by_cases h : j < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma snoc_last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp

lemma agree_at_other_indices (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (runGates gs w).getD j false = (runGates gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have unused := hno g List.mem_cons_self
    have same : (g.inputs.map fun i => w.getD i false) =
        g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => unused (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases atEnd : j = w.length
    · rw [atEnd, snoc_last, hl, snoc_last, same]
    · rw [snoc_other _ _ _ atEnd, snoc_other _ _ _ (by omega)]
      exact h j hj

lemma all_raw (C : Circuit) (correct : ∀ x, C.eval (encoded x) = target x)
    (v : Fin 9) : v.val ∈ C.output :: C.gates.flatMap Gate.inputs := by
  apply Classical.byContradiction
  intro absent
  have neither : v.val ≠ C.output ∧ v.val ∉ C.gates.flatMap Gate.inputs := by
    simpa only [List.mem_cons, not_or] using absent
  have sameOutput := agree_at_other_indices v.val C.gates (encoded (low v)) (encoded (high v))
    (fun g hg hg' => neither.2 (List.mem_flatMap.mpr ⟨g, hg, hg'⟩)) (by simp [encoded])
    (fun j hj => by
      by_cases bounded : j < 10
      · exact (distinguish v).2 ⟨j, bounded⟩ hj
      · rw [List.getD_eq_default _ _ (by simp [encoded]; omega),
            List.getD_eq_default _ _ (by simp [encoded]; omega)])
    C.output (Ne.symm neither.1)
  apply (distinguish v).1
  exact (correct (low v)).symm.trans (sameOutput.trans (correct (high v)))

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (runGates gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runGates gs (w ++ [_])).getD i false = w.getD i false
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma singles : ∀ v : Fin 9,
    (encoded fun i => i == v).getD v.val false ≠ target (fun i => i == v) := by
  decide

lemma out_ne (C : Circuit) (correct : ∀ x, C.eval (encoded x) = target x) (v : Fin 9) :
    C.output ≠ v.val := by
  intro h
  have t := correct (fun i => i == v)
  change (runGates C.gates _).getD C.output false = _ at t
  have hv := v.isLt
  rw [h, run_input _ _ _ (by simp [encoded]; omega)] at t
  exact singles v t

private theorem count_budget (l : List Nat) :
    l.count 0 + l.count 1 + l.count 2 + l.count 3 + l.count 4 +
      l.count 5 + l.count 6 + l.count 7 + l.count 8 ≤
        l.countP (fun i => decide (i < 10)) := by
  induction l with
  | nil => decide
  | cons a l ih =>
    simp only [List.count_cons, List.countP_cons, beq_iff_eq, decide_eq_true_eq]
    have cases_a : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ 9 ≤ a := by omega
    rcases cases_a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    all_goals simp (config := { decide := true }) <;> try omega
    repeat' (split <;> try omega)

theorem pigeonhole (l : List Nat) (used : ∀ v : Fin 9, v.val ∈ l)
    (budget : l.countP (fun i => decide (i < 10)) ≤ 15) :
    ∃ v : Fin 9, v ≠ 0 ∧ v ≠ 6 ∧ l.count v.val = 1 := by
  have total := count_budget l
  apply Classical.byContradiction
  intro hn
  have two (v : Fin 9) (h₀ : v ≠ 0) (h₆ : v ≠ 6) : 2 ≤ l.count v.val := by
    have positive : 0 < l.count v.val := List.count_pos_iff.mpr (used v)
    have hne : l.count v.val ≠ 1 := fun he => hn ⟨v, h₀, h₆, he⟩
    omega
  have h0 : 0 < l.count 0 := List.count_pos_iff.mpr (used 0)
  have h1 : 2 ≤ l.count 1 := two 1 (by decide) (by decide)
  have h2 : 2 ≤ l.count 2 := two 2 (by decide) (by decide)
  have h3 : 2 ≤ l.count 3 := two 3 (by decide) (by decide)
  have h4 : 2 ≤ l.count 4 := two 4 (by decide) (by decide)
  have h5 : 2 ≤ l.count 5 := two 5 (by decide) (by decide)
  have h6 : 0 < l.count 6 := List.count_pos_iff.mpr (used 6)
  have h7 : 2 ≤ l.count 7 := two 7 (by decide) (by decide)
  have h8 : 2 ≤ l.count 8 := two 8 (by decide) (by decide)
  omega

end PEqualNP.Outside.L_meta_2802

open PEqualNP.Outside.L_meta_2802

theorem PEqualNP.Outside.L_meta_2802 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin (9 : ℕ) → Bool), x3.eval (x2 x4) = x1 x4) → List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < (10 : ℕ))) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) ≤ (15 : ℕ) → ∃ (x6 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (6 : Fin (9 : ℕ)) ∧ x3.output ≠ ↑x6 ∧ List.count (↑x6) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) = (1 : ℕ) := by
  dsimp only
  intro C correct budget
  obtain ⟨v, h0, h6, once⟩ := pigeonhole _ (all_raw C correct) budget
  have output := out_ne C correct v
  exact ⟨v, h0, h6, output, by simpa [List.count_cons, output] using once⟩
