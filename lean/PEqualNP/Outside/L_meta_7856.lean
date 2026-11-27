import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7856

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (b : Bool) (f g : ℕ → Bool) (l : List ℕ) (h : ∀ i, f i = b → g i = b) :
    op.eval (l.map f) = b → op.eval (l.map g) = b := by
  rcases hop with rfl | rfl
  · cases b <;> simp only [GateOp.eval, List.all_map, List.all_eq_true,
      List.all_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩
    · exact fun H x hx => h x (H x hx)
  · cases b <;> simp only [GateOp.eval, List.any_map, List.any_eq_true,
      List.any_eq_false, Function.comp, id, Bool.not_eq_true]
    · exact fun H x hx => h x (H x hx)
    · exact fun ⟨x, hx, H⟩ => ⟨x, hx, h x H⟩

theorem main_fold (n m p : ℕ) (b : Bool) (B : List Gate)
    (hB : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hp : p < n + m ∨ w'.length + B.length ≤ p)
    (hI : ∀ i, w.getD i false = b → w'.getD (eraseRedirect n m p i) false = b) :
    ∀ i, (B.foldl step w).getD i false = b →
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false = b := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    simp only [List.length_cons] at hp
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      simp only [step, getD_snoc, List.map_map]
      have hx := op_mono g.op hg b (fun i => w.getD i false)
        (fun i => w'.getD (eraseRedirect n m p i) false) g.inputs hI
      have hIi := hI i
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      by_cases h1 : i < w.length
      · rw [if_pos h1]
        intro hb
        have h3 := hIi hb
        by_cases hr1 : r < w'.length
        · rw [if_pos hr1]; exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg hr1, if_neg (by omega)]
          rw [getD_big _ _ (by omega)] at h3
          exact h3
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · rw [if_pos h2]
          intro hb
          have h3 := hx hb
          have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_neg (by omega), if_pos h4]
          exact h3
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
          exact id

theorem erase_main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     x3 < x2.size →       x4 < x1 + x3 ∨ x4 = x1 + x2.size →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4;         PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size + (1 : ℕ) = x2.size ∧ ∀ (x9 : List Bool), x9.length = x1 → ∀ (x11 : Bool), (PEqualNP.LowMerge.wireVal x2 x9 (x1 + x3) = x11 → PEqualNP.LowMerge.wireVal x2 x9 x4 = x11) → ∀ (x13 : ℕ), PEqualNP.LowMerge.wireVal x2 x9 x13 = x11 → PEqualNP.LowMerge.wireVal x8 x9 (PEqualNP.CircuitMoves.eraseRedirect x1 x3 x4 x13) = x11 := by
  intro n C m p hM hm hp
  have hm' : m < C.gates.length := hm
  have hsize : C.size = C.gates.length := rfl
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, if_pos hm', List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hM g (List.mem_of_mem_take hg)
    · have := hM g' (List.mem_of_mem_drop hg')
      exact ⟨this.1, by simpa using this.2⟩
  · simp only [eraseGate, if_pos hm', Circuit.size, List.length_append, List.length_take,
      List.length_map, List.length_drop]
    omega
  · intro x hx b hyp i
    simp only [PEqualNP.LowMerge.wireVal, wires_eq] at hyp ⊢
    have key : C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
        (step ((C.gates.take m).foldl step x) C.gates[m]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    rw [key] at hyp ⊢
    simp only [eraseGate, if_pos hm']
    rw [List.foldl_append]
    have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
      rw [fold_len, hx, List.length_take]; omega
    have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := by simp
    apply main_fold n m p b _ (fun g hg => (hM g (List.mem_of_mem_drop hg)).1)
    · simp [step]
    · omega
    · rw [hWA, hdl]; rcases hp with hp | hp
      · left; exact hp
      · right; rw [hp, hsize]; omega
    · intro j
      generalize hWAd : List.foldl step x (List.take m C.gates) = WA at *
      rw [fold_stab _ _ _ (by simp [step]; omega)] at hyp
      unfold eraseRedirect
      by_cases h1 : j = n + m
      · subst h1; rw [if_pos rfl]
        intro hb
        have h2 := hyp hb
        rcases hp with hp | hp
        · rw [fold_stab _ _ _ (by simp [step]; omega)] at h2
          simp only [step, getD_snoc, hWA, if_pos hp] at h2; exact h2
        · rw [getD_big _ _ (by rw [fold_len]; simp [step]; omega)] at h2
          rw [getD_big _ _ (by omega)]; exact h2
      · rw [if_neg h1]
        simp only [step, getD_snoc, hWA]
        by_cases h3 : j < n + m
        · rw [if_pos h3, if_neg (by omega)]; exact id
        · rw [if_neg h3, if_neg h1, if_pos (by omega), getD_big _ _ (by omega)]; exact id

theorem and_true_mem (l : List ℕ) (f : ℕ → Bool) (p : ℕ) (hp : p ∈ l)
    (h : GateOp.and.eval (l.map f) = true) : f p = true := by
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at h
  exact h p hp

theorem final_aux : ∀ (n : ℕ) (C : Circuit) (m p : ℕ),
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
    m < C.size →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = GateOp.and →
    p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs →
    PEqualNP.MetaComplexity.Monotone2 (eraseGate n C m p) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n (eraseGate n C m p) ∧
    (eraseGate n C m p).size < C.size ∧
    ∀ (x : List Bool) (i : ℕ), x.length = n → (C.wires x).getD i false = true →
      ((eraseGate n C m p).wires x).getD (eraseRedirect n m p i) false = true := by
  intro n C m p hM hR hm hop hpin
  have hm' : m < C.gates.length := hm
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C m = C.gates[m] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hm']
  have hpl : p < n + m := hR m hm' p hpin
  obtain ⟨h1, h2, h3⟩ := erase_main n C m p hM hm (Or.inl hpl)
  refine ⟨h1, ?_, by omega, ?_⟩
  · intro j hj i hi
    simp only [eraseGate, if_pos hm', List.length_append, List.length_take,
      List.length_map, List.length_drop] at hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, eraseGate, if_pos hm',
      List.getD_eq_getElem?_getD] at hi
    by_cases hjm : j < m
    · rw [List.getElem?_append_left (by simp; omega)] at hi
      have := hR j (by omega) i
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] at this
      rw [List.getElem?_take, if_pos hjm] at hi
      exact this hi
    · rw [List.getElem?_append_right (by simp; omega)] at hi
      have hlen : (List.take m C.gates).length = m := by simp; omega
      rw [hlen, List.getElem?_map, List.getElem?_drop,
        List.getElem?_eq_getElem (by omega)] at hi
      simp only [Option.map_some, Option.getD_some, List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      have := hR (m + 1 + (j - m)) (by omega) i'
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] at this
      rw [List.getElem?_eq_getElem (by omega)] at this
      have := this hi'
      unfold eraseRedirect
      split_ifs <;> omega
  · intro x i hx
    refine h3 x hx true ?_ i
    simp only [PEqualNP.LowMerge.wireVal, wires_eq]
    have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
    have key : C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
        (step ((C.gates.take m).foldl step x) C.gates[m]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
      rw [fold_len, hx, List.length_take]; omega
    rw [key, fold_stab _ _ _ (by simp [step]; omega), fold_stab _ _ _ (by simp [step]; omega)]
    simp only [step, getD_snoc, hWA, if_pos hpl, lt_irrefl, if_false, if_true]
    intro h
    rw [hga] at hop hpin
    rw [hop] at h
    exact and_true_mem _ _ p hpin h

end PEqualNP.Outside.L_meta_7856

theorem PEqualNP.Outside.L_meta_7856 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 →       x3 < x2.size →         (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and →           x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).inputs →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4;             PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.size < x2.size ∧ ∀ (x11 : List Bool) (x12 : ℕ), x11.length = x1 → (x2.wires x11).getD x12 Bool.false = Bool.true → (x10.wires x11).getD (PEqualNP.CircuitMoves.eraseRedirect x1 x3 x4 x12) Bool.false = Bool.true := by
  intro x1 x2 x3 x4 a b c d e
  exact PEqualNP.Outside.L_meta_7856.final_aux x1 x2 x3 x4 a b c d e
