import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7197

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def stepG {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (w : List α) (g : Gate) : List α :=
  w ++ [F (fun i => w.getD i d) g]

def Loc {α : Type} (F : (ℕ → α) → Gate → α) : Prop :=
  ∀ V V' : ℕ → α, ∀ g : Gate, (∀ i ∈ g.inputs, V i = V' i) → F V g = F V' g

lemma gfoldl_getD_lt {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (gs : List Gate) (w : List α)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (stepG F d) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepG F d w g).length := by simp [stepG]; omega
    rw [ih (stepG F d w g) hlt]
    simp [stepG, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ggetD_ge {α : Type} (w : List α) (d : α) (i : ℕ) (hi : w.length ≤ i) : w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma gfoldl_getD_gate {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (hF : Loc F)
    (gs : List Gate) (w : List α) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (stepG F d) w).getD (w.length + j) d =
      F (fun i => if i < w.length + j then (gs.foldl (stepG F d) w).getD i d else d) gs[j] := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepG F d w g).length := by simp [stepG]
      rw [Nat.add_zero, gfoldl_getD_lt F d gs (stepG F d w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepG F d w g).getD w.length d = F (fun i => w.getD i d) g := by
        simp [stepG, List.getD_eq_getElem?_getD]
      rw [h2]
      apply hF
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, gfoldl_getD_lt F d gs (stepG F d w g) i (by simp [stepG]; omega)]
        simp [stepG, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact ggetD_ge w d i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepG F d w g) j hj'
      have hl : (stepG F d w g).length = w.length + 1 := by simp [stepG]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gate_val {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (hF : Loc F) (n : ℕ) (C : Circuit)
    (hRB : ReadsBack n C) (w : List α) (hw : w.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (stepG F d) w).getD (n + j) d =
      F (fun i => (C.gates.foldl (stepG F d) w).getD i d) C.gates[j] := by
  subst hw
  rw [gfoldl_getD_gate F d hF C.gates w j hj]
  apply hF
  intro i hi
  have : i < w.length + j := hRB j hj i (by rw [gateAt_eq hj]; exact hi)
  rw [ite_eq_left this]

def comb : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.sum
  | _, l => l.foldr max 0

def Fd (V : ℕ → ℕ) (g : Gate) : ℕ := comb g.op (g.inputs.map V)

lemma loc_d : Loc Fd := by
  intro V V' g h; unfold Fd; rw [List.map_congr_left h]

lemma lineDegrees_eq (C : Circuit) (n : ℕ) (m : Finset ℕ) :
    C.lineDegrees n m = C.gates.foldl (stepG Fd 0)
      ((List.range n).map fun i => if i ∈ m then 1 else 0) := by
  unfold Circuit.lineDegrees
  congr 1
  funext w g
  obtain ⟨op, l⟩ := g
  cases op <;> simp [stepG, Fd, comb, Gate.lineDegree]

def D (n : ℕ) (C : Circuit) (m : Finset ℕ) (u : ℕ) : ℕ :=
  (C.lineDegrees n m).getD u 0

lemma inp_D (n : ℕ) (C : Circuit) (m : Finset ℕ) (u : ℕ) (hu : u < n) :
    D n C m u = if u ∈ m then 1 else 0 := by
  unfold D
  rw [lineDegrees_eq, gfoldl_getD_lt _ _ _ _ _ (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma gate_m (n : ℕ) (C : Circuit) (m : Finset ℕ) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ a b, C.gates[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((C.gates[j].op = GateOp.and ∧ D n C m (n + j) = D n C m a + D n C m b) ∨
       (C.gates[j].op = GateOp.or ∧ D n C m (n + j) = max (D n C m a) (D n C m b))) := by
  obtain ⟨hAnd, hRB, hL⟩ := hAO
  have hmem := List.getElem_mem hj
  have hop := hAnd _ hmem
  have hl := hL _ hmem
  have hrb : ∀ i ∈ C.gates[j].inputs, i < n + j := by
    intro i hi; exact hRB j hj i (by rw [gateAt_eq hj]; exact hi)
  have eD : D n C m (n + j) = Fd (D n C m) C.gates[j] := by
    unfold D
    rw [lineDegrees_eq]
    exact gate_val Fd 0 loc_d n C hRB _ (by simp) j hj
  rw [eD]
  generalize C.gates[j] = g at hop hl hrb
  obtain ⟨op, l⟩ := g
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · refine ⟨a, b, rfl, hrb a (by simp), hrb b (by simp), ?_⟩
    rcases hop with h | h <;> simp only at h <;> subst h
    · left
      exact ⟨rfl, by simp [Fd, comb]⟩
    · right
      exact ⟨rfl, by simp [Fd, comb]⟩
  · simp at hl

lemma gate2 (n : ℕ) (C : Circuit) (m1 m2 : Finset ℕ) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ a b, C.gates[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((C.gates[j].op = GateOp.and ∧ D n C m1 (n + j) = D n C m1 a + D n C m1 b ∧
          D n C m2 (n + j) = D n C m2 a + D n C m2 b) ∨
       (C.gates[j].op = GateOp.or ∧ D n C m1 (n + j) = max (D n C m1 a) (D n C m1 b) ∧
          D n C m2 (n + j) = max (D n C m2 a) (D n C m2 b))) := by
  obtain ⟨a, b, hab, ha, hb, h1⟩ := gate_m n C m1 hAO j hj
  obtain ⟨a', b', hab', -, -, h2⟩ := gate_m n C m2 hAO j hj
  rw [hab] at hab'
  simp only [List.cons.injEq, and_true] at hab'
  obtain ⟨rfl, rfl⟩ := hab'
  refine ⟨a, b, hab, ha, hb, ?_⟩
  rcases h1 with ⟨o1, e1⟩ | ⟨o1, e1⟩ <;> rcases h2 with ⟨o2, e2⟩ | ⟨o2, e2⟩
  · exact Or.inl ⟨o1, e1, e2⟩
  · rw [o1] at o2; cases o2
  · rw [o1] at o2; cases o2
  · exact Or.inr ⟨o1, e1, e2⟩

lemma nonzero (x1 x2 : ℕ) (C : Circuit) (hAO : IsAO2 (x1 + x2) C) :
    ∀ u, u < x1 + x2 + C.gates.length →
      1 ≤ D (x1 + x2) C (Finset.range x1) u + D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < x1 + x2
    · rw [inp_D _ _ _ _ hun, inp_D _ _ _ _ hun]
      simp only [Finset.mem_range, Finset.mem_Ico]
      split_ifs <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, u = x1 + x2 + j := ⟨u - (x1 + x2), by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨a, b, -, ha, hb, h⟩ :=
        gate2 (x1 + x2) C (Finset.range x1) (Finset.Ico x1 (x1 + x2)) hAO j hj
      have iha := ih a (by omega) (by omega)
      have ihb := ih b (by omega) (by omega)
      rcases h with ⟨-, e1, e2⟩ | ⟨-, e1, e2⟩
      · omega
      · rw [e1, e2]
        have := le_max_left (D (x1 + x2) C (Finset.range x1) a) (D (x1 + x2) C (Finset.range x1) b)
        have := le_max_left (D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) a)
          (D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) b)
        omega

end PEqualNP.Outside.L_meta_7197

open PEqualNP.Outside.L_meta_7197 in
theorem PEqualNP.Outside.L_meta_7197 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ x5 < x1 + x2 + x3.size, (x3.lineDegrees (x1 + x2) (Finset.range x1)).getD x5 (0 : ℕ) ≤ (1 : ℕ) ∧ (x3.lineDegrees (x1 + x2) (Finset.Ico x1 (x1 + x2))).getD x5 (0 : ℕ) ≤ (1 : ℕ)) → ∃ (x6 : Finset ℕ) (x7 : Finset ℕ), (∀ x8 ∈ x6, x8 < x1 ∨ ∃ x10 < x3.size, x8 = x1 + x2 + x10 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).inputs, x11 ∈ x6) ∧ (∀ x8 ∈ x7, x1 ≤ x8 ∧ x8 < x1 + x2 ∨ ∃ x10 < x3.size, x8 = x1 + x2 + x10 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).inputs, x11 ∈ x7) ∧ ∀ x8 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).inputs = [x11, x12] ∧ (x11 ∈ x6 ∧ x12 ∈ x7 ∨ x11 ∈ x7 ∧ x12 ∈ x6) := by
  intro x1 x2 C hAO hdeg
  have hs : C.size = C.gates.length := rfl
  have hdeg' : ∀ u < x1 + x2 + C.gates.length, D (x1 + x2) C (Finset.range x1) u ≤ 1 ∧
      D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) u ≤ 1 := hdeg
  have hnz := nonzero x1 x2 C hAO
  refine ⟨(Finset.range (x1 + x2 + C.gates.length)).filter
      (fun w => D (x1 + x2) C (Finset.range x1) w = 1 ∧ D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) w = 0),
    (Finset.range (x1 + x2 + C.gates.length)).filter
      (fun w => D (x1 + x2) C (Finset.range x1) w = 0 ∧ D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) w = 1),
    ?_, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwN, h1, h0⟩ := hw
    by_cases hwn : w < x1 + x2
    · left
      rw [inp_D _ _ _ _ hwn] at h1
      simp only [Finset.mem_range] at h1
      split_ifs at h1 with h <;> omega
    · right
      obtain ⟨j, rfl⟩ : ∃ j, w = x1 + x2 + j := ⟨w - (x1 + x2), by omega⟩
      have hj : j < C.gates.length := by omega
      refine ⟨j, by rw [hs]; exact hj, rfl, ?_⟩
      rw [gateAt_eq hj]
      obtain ⟨a, b, hab, ha, hb, h⟩ :=
        gate2 (x1 + x2) C (Finset.range x1) (Finset.Ico x1 (x1 + x2)) hAO j hj
      have hna := hnz a (by omega)
      have hnb := hnz b (by omega)
      have hda := hdeg' a (by omega)
      have hdb := hdeg' b (by omega)
      rcases h with ⟨-, e1, e2⟩ | ⟨hop, e1, e2⟩
      · rw [e1] at h1; rw [e2] at h0; omega
      · refine ⟨hop, ?_⟩
        rw [e1] at h1; rw [e2] at h0
        have := le_max_left (D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) a)
          (D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) b)
        have := le_max_right (D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) a)
          (D (x1 + x2) C (Finset.Ico x1 (x1 + x2)) b)
        intro x hx
        rw [hab] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hx with rfl | rfl
        · refine ⟨by omega, by omega, by omega⟩
        · refine ⟨by omega, by omega, by omega⟩
  · intro w hw
    rw [Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwN, h0, h1⟩ := hw
    by_cases hwn : w < x1 + x2
    · left
      rw [inp_D _ _ _ _ hwn] at h1
      simp only [Finset.mem_Ico] at h1
      split_ifs at h1 with h <;> omega
    · right
      obtain ⟨j, rfl⟩ : ∃ j, w = x1 + x2 + j := ⟨w - (x1 + x2), by omega⟩
      have hj : j < C.gates.length := by omega
      refine ⟨j, by rw [hs]; exact hj, rfl, ?_⟩
      rw [gateAt_eq hj]
      obtain ⟨a, b, hab, ha, hb, h⟩ :=
        gate2 (x1 + x2) C (Finset.range x1) (Finset.Ico x1 (x1 + x2)) hAO j hj
      have hna := hnz a (by omega)
      have hnb := hnz b (by omega)
      have hda := hdeg' a (by omega)
      have hdb := hdeg' b (by omega)
      rcases h with ⟨-, e1, e2⟩ | ⟨hop, e1, e2⟩
      · rw [e1] at h0; rw [e2] at h1; omega
      · refine ⟨hop, ?_⟩
        rw [e1] at h0; rw [e2] at h1
        have := le_max_left (D (x1 + x2) C (Finset.range x1) a)
          (D (x1 + x2) C (Finset.range x1) b)
        have := le_max_right (D (x1 + x2) C (Finset.range x1) a)
          (D (x1 + x2) C (Finset.range x1) b)
        intro x hx
        rw [hab] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hx with rfl | rfl
        · refine ⟨by omega, by omega, by omega⟩
        · refine ⟨by omega, by omega, by omega⟩
  · intro j hj hop
    rw [hs] at hj
    rw [gateAt_eq hj] at hop ⊢
    obtain ⟨a, b, hab, ha, hb, h⟩ :=
      gate2 (x1 + x2) C (Finset.range x1) (Finset.Ico x1 (x1 + x2)) hAO j hj
    refine ⟨a, b, hab, ?_⟩
    have hna := hnz a (by omega)
    have hnb := hnz b (by omega)
    have hdj := hdeg' (x1 + x2 + j) (by omega)
    rcases h with ⟨-, e1, e2⟩ | ⟨hop', -, -⟩
    · rw [e1, e2] at hdj
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · rw [hop] at hop'; cases hop'
