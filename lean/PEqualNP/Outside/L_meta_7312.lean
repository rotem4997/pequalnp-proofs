import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7312

open PEqualNP.CircuitLowerBounds

def F : (Fin 10 → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))))

def Rd (x2 : Gate) (x3 : ℕ) : Prop :=
  x2.op = GateOp.not ∧ x2.inputs.head? = Option.some x3 ∨ x2.op ≠ GateOp.not ∧ x3 ∈ x2.inputs

def X3 (x3 : Bool) : List Bool := x3 :: Bool.true :: List.replicate (8 : ℕ) Bool.false ++ [!x3]

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_lt (l : List Bool) (a : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_new (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem len_stp (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  simp [stp]

theorem getD_foldl (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ _ (by rw [len_stp]; omega)]
    exact getD_lt _ _ _ h

theorem mono_all (l : List ℕ) (fu fv : ℕ → Bool) (h : ∀ i ∈ l, fu i = true ∨ fv i = false) :
    (l.map fu).all id = true ∨ (l.map fv).all id = false := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    rcases h a (by simp) with h1 | h1 <;>
      rcases ih (fun i hi => h i (by simp [hi])) with h2 | h2 <;> simp [h1, h2]

theorem mono_any (l : List ℕ) (fu fv : ℕ → Bool) (h : ∀ i ∈ l, fu i = true ∨ fv i = false) :
    (l.map fu).any id = true ∨ (l.map fv).any id = false := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    rcases h a (by simp) with h1 | h1 <;>
      rcases ih (fun i hi => h i (by simp [hi])) with h2 | h2 <;> simp [h1, h2]

theorem inv2 (gs : List Gate) : ∀ u v : List Bool, u.length = v.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ g ∈ gs, ¬ Rd g 0) →
    (∀ i, i ≠ 0 → (u.getD i false = true ∨ v.getD i false = false)) →
    (∀ j, j < gs.length → ∀ g, gs[j]? = some g → g.op = GateOp.not →
      ¬((gs.foldl stp u).getD (u.length + j) false = false ∧
        (gs.foldl stp v).getD (u.length + j) false = true)) →
    ∀ i, i ≠ 0 → ((gs.foldl stp u).getD i false = true ∨ (gs.foldl stp v).getD i false = false) := by
  induction gs with
  | nil => intro u v _ _ _ h _; simpa using h
  | cons g gs ih =>
    intro u v hl hop hrd hinv hnot
    simp only [List.foldl_cons]
    have eu : (stp u g).getD u.length false =
        g.op.eval (g.inputs.map fun i => u.getD i false) := getD_new _ _
    have ev : (stp v g).getD u.length false =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by rw [hl]; exact getD_new _ _
    apply ih (stp u g) (stp v g) (by rw [len_stp, len_stp, hl])
      (fun g' hg' => hop g' (by simp [hg'])) (fun g' hg' => hrd g' (by simp [hg']))
    · intro i hi
      rcases lt_trichotomy i u.length with h | h | h
      · have hv : i < v.length := hl ▸ h
        rw [stp, stp, getD_lt _ _ _ h, getD_lt _ _ _ hv]
        exact hinv i hi
      · subst h
        rw [eu, ev]
        rcases hop g (by simp) with ho | ho | ho
        · rw [ho]; simp only [GateOp.eval]
          apply mono_all
          intro k hk
          apply hinv
          rintro rfl
          exact hrd g (by simp) (Or.inr ⟨(by rw [ho]; intro hh; cases hh), hk⟩)
        · rw [ho]; simp only [GateOp.eval]
          apply mono_any
          intro k hk
          apply hinv
          rintro rfl
          exact hrd g (by simp) (Or.inr ⟨(by rw [ho]; intro hh; cases hh), hk⟩)
        · have := hnot 0 (by simp) g (by simp) ho
          simp only [List.foldl_cons, Nat.add_zero] at this
          rw [getD_foldl _ _ _ (by rw [len_stp]; omega),
            getD_foldl _ _ _ (by rw [len_stp]; omega), eu, ev] at this
          revert this
          cases g.op.eval (g.inputs.map fun i => u.getD i false) <;>
            cases g.op.eval (g.inputs.map fun i => v.getD i false) <;> simp
      · right
        apply getD_big
        rw [len_stp]; omega
    · intro j hj g' hg' ho
      have := hnot (j + 1) (by simp; omega) g' (by simpa using hg') ho
      simp only [List.foldl_cons] at this
      rw [len_stp, show u.length + 1 + j = u.length + (j + 1) by omega]
      exact this

theorem inv1 (gs : List Gate) : ∀ u v : List Bool, u.length = v.length →
    (∀ g ∈ gs, ¬ Rd g 0) → (∀ g ∈ gs, ¬ Rd g 10) →
    (∀ i, i ≠ 0 → i ≠ 10 → u.getD i false = v.getD i false) →
    ∀ i, i ≠ 0 → i ≠ 10 → (gs.foldl stp u).getD i false = (gs.foldl stp v).getD i false := by
  induction gs with
  | nil => intro u v _ _ _ h; simpa using h
  | cons g gs ih =>
    intro u v hl hr0 hr10 hinv
    simp only [List.foldl_cons]
    apply ih (stp u g) (stp v g) (by rw [len_stp, len_stp, hl])
      (fun g' hg' => hr0 g' (by simp [hg'])) (fun g' hg' => hr10 g' (by simp [hg']))
    intro i hi0 hi10
    rcases lt_trichotomy i u.length with h | h | h
    · have hv : i < v.length := hl ▸ h
      rw [stp, stp, getD_lt _ _ _ h, getD_lt _ _ _ hv]
      exact hinv i hi0 hi10
    · subst h
      rw [stp, stp, getD_new, hl, getD_new]
      by_cases ho : g.op = GateOp.not
      · rw [ho]; simp only [GateOp.eval]
        cases hin : g.inputs with
        | nil => simp
        | cons k ks =>
          have h0 : k ≠ 0 := fun h => hr0 g (by simp) (Or.inl ⟨ho, by simp [hin, h]⟩)
          have h10 : k ≠ 10 := fun h => hr10 g (by simp) (Or.inl ⟨ho, by simp [hin, h]⟩)
          simp only [List.map_cons, List.headD_cons]
          rw [hinv k h0 h10]
      · congr 1
        apply List.map_congr_left
        intro k hk
        apply hinv k
        · rintro rfl; exact hr0 g (by simp) (Or.inr ⟨ho, hk⟩)
        · rintro rfl; exact hr10 g (by simp) (Or.inr ⟨ho, hk⟩)
    · rw [getD_big _ _ (by rw [len_stp]; omega), getD_big _ _ (by rw [len_stp]; omega)]

def x6f : Fin 10 → Bool := fun i => decide (i = 1)
def x6t : Fin 10 → Bool := fun i => decide (i = 0) || decide (i = 1)
def x6z : Fin 10 → Bool := fun i => decide (i = 0)

theorem main (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (heval : ∀ (x6 : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x6 ++ [!x6 (0 : Fin (10 : ℕ))]) = F x6)
    (hno : ∀ (x7 : Fin C.size), ¬ Rd (C.gates.get x7) (0 : ℕ)) :
    (∃ (x8 : Fin C.size), Rd (C.gates.get x8) (10 : ℕ)) ∧ ∃ (x8 : Fin C.size),
      (C.gates.get x8).op = GateOp.not ∧
      (C.wires (X3 Bool.false)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.false ∧
      (C.wires (X3 Bool.true)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.true := by
  have hr0 : ∀ g ∈ C.gates, ¬ Rd g 0 := by
    intro g hg
    obtain ⟨n, rfl⟩ := List.mem_iff_get.1 hg
    exact hno n
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    simpa using (hfan g hg).1
  have e0 : C.eval (X3 false) = false := by
    have h := heval x6f
    have hx : List.ofFn x6f ++ [!x6f 0] = X3 false := by decide
    rw [hx] at h
    rw [h]; decide
  have e1 : C.eval (X3 true) = true := by
    have h := heval x6t
    have hx : List.ofFn x6t ++ [!x6t 0] = X3 true := by decide
    rw [hx] at h
    rw [h]; decide
  have ez : C.eval (List.ofFn x6z ++ [!x6z 0]) = false := by
    rw [heval x6z]; decide
  have hlen : ∀ b, (X3 b).length = 11 := by intro b; rfl
  have hO : C.output ≠ 0 := by
    intro h
    rw [Circuit.eval, wires_eq, h, getD_foldl _ _ _ (by simp)] at ez
    revert ez; decide
  refine ⟨?_, ?_⟩
  · by_contra h1
    push_neg at h1
    have hr10 : ∀ g ∈ C.gates, ¬ Rd g 10 := by
      intro g hg
      obtain ⟨n, rfl⟩ := List.mem_iff_get.1 hg
      exact h1 n
    have hinit : ∀ i, i ≠ 0 → i ≠ 10 → (X3 false).getD i false = (X3 true).getD i false := by
      intro i h0 h10
      rcases Nat.lt_or_ge i 11 with h | h
      · interval_cases i <;> first | rfl | exact absurd rfl h0 | exact absurd rfl h10
      · rw [getD_big _ _ (by rw [hlen]; exact h), getD_big _ _ (by rw [hlen]; exact h)]
    have key := inv1 C.gates (X3 false) (X3 true) (by rw [hlen, hlen]) hr0 hr10 hinit
    rw [Circuit.eval, wires_eq] at e0 e1
    by_cases h10 : C.output = 10
    · rw [h10, getD_foldl _ _ _ (by rw [hlen]; omega)] at e0
      revert e0; decide
    · have := key C.output hO h10
      rw [e0, e1] at this
      exact absurd this (by decide)
  · by_contra h2
    push_neg at h2
    have hinit : ∀ i, i ≠ 0 → ((X3 false).getD i false = true ∨ (X3 true).getD i false = false) := by
      intro i h0
      rcases Nat.lt_or_ge i 11 with h | h
      · interval_cases i <;> first | (left; rfl) | (right; rfl) | exact absurd rfl h0
      · right; exact getD_big _ _ (by rw [hlen]; exact h)
    have hnot : ∀ j, j < C.gates.length → ∀ g, C.gates[j]? = some g → g.op = GateOp.not →
        ¬((C.gates.foldl stp (X3 false)).getD ((X3 false).length + j) false = false ∧
          (C.gates.foldl stp (X3 true)).getD ((X3 false).length + j) false = true) := by
      intro j hj g hg ho hc
      rw [List.getElem?_eq_some_iff] at hg
      obtain ⟨hj', hg⟩ := hg
      have hj2 : j < C.size := hj
      have := h2 ⟨j, hj2⟩ (by show (C.gates[j]'hj).op = GateOp.not; rw [hg]; exact ho)
      rw [hlen] at hc
      rw [wires_eq, wires_eq] at this
      exact this hc.1 hc.2
    have key := inv2 C.gates (X3 false) (X3 true) (by rw [hlen, hlen]) hop hr0 hinit hnot
    rw [Circuit.eval, wires_eq] at e0 e1
    rcases key C.output hO with h | h
    · rw [e0] at h; exact absurd h (by decide)
    · rw [e1] at h; exact absurd h (by decide)

end PEqualNP.Outside.L_meta_7312

theorem PEqualNP.Outside.L_meta_7312 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); have x2 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : ℕ) => x2.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2.inputs.head? = Option.some x3 ∨ x2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x3 ∈ x2.inputs; have x3 : Bool → List Bool := fun (x3 : Bool) => x3 :: Bool.true :: List.replicate (8 : ℕ) Bool.false ++ [!x3]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x6 : Fin (10 : ℕ) → Bool), x4.eval (List.ofFn x6 ++ [!x6 (0 : Fin (10 : ℕ))]) = x1 x6) → (∀ (x7 : Fin x4.size), ¬x2 (x4.gates.get x7) (0 : ℕ)) → (∃ (x8 : Fin x4.size), x2 (x4.gates.get x8) (10 : ℕ)) ∧ ∃ (x8 : Fin x4.size), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x4.wires (x3 Bool.false)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.false ∧ (x4.wires (x3 Bool.true)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.true := by
  intro x1 x2 x3 C hfan heval hno
  exact PEqualNP.Outside.L_meta_7312.main C hfan heval hno
