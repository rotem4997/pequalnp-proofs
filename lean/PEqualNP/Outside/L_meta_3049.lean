import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3049

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

private lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [ite_eq_left rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [ite_eq_right h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private lemma runWires_len (gs : List Gate) (init : List Bool) :
    (runWires gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).length = init.length + (gs.length + 1)
    rw [ih, stepWire, List.length_append, List.length_singleton]
    omega

private lemma runWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (runWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).getD i false = init.getD i false
    have hlt : i < (stepWire init g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire init g) hlt, stepWire, getD_append_singleton, ite_eq_left hi]

private lemma runWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (runWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (runWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (runWires gs (stepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (runWires gs (stepWire init g)).getD i false else false)
      have hlen : init.length < (stepWire init g).length := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, runWires_getD_prefix gs (stepWire init g) init.length hlen]
      have hhead : (stepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [stepWire, getD_append_singleton, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [ite_eq_left hi]
        have hi' : i < (stepWire init g).length := by
          simp only [stepWire, List.length_append, List.length_singleton]
          omega
        rw [runWires_getD_prefix gs (stepWire init g) i hi', stepWire,
          getD_append_singleton, ite_eq_left hi]
      · rw [ite_eq_right hi, getD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (stepWire init g).length + k := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      change (runWires gs (stepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (runWires gs (stepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (stepWire init g) k hk

private def wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal C x i = x ⟨i, hi⟩ := by
  unfold wireVal
  change (runWires C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [runWires_getD_prefix C.gates (List.ofFn x) i (by simp [hi])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

private lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    wireVal C x (n + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < n + j then wireVal C x i else false) := by
  unfold wireVal
  have h := runWires_getD_gate C.gates (List.ofFn x) j hj
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  rw [hlen] at h
  exact h

private lemma wireVal_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal C x w = false := by
  unfold wireVal
  apply getD_of_ge
  change (runWires C.gates (List.ofFn x)).length ≤ w
  rw [runWires_len, List.length_ofFn]
  exact hw

private lemma mono_eval {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, wireVal C x w = true → wireVal C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < n
    · rw [wireVal_input C x w hlt, wireVal_input C y w hlt]
      exact hxy ⟨w, hlt⟩
    · by_cases hlt2 : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have heq : n + (w - n) = w := by omega
        rw [← heq, wireVal_gate C x (w - n) hj, wireVal_gate C y (w - n) hj]
        obtain ⟨hop, _⟩ := hm C.gates[w - n] (List.getElem_mem hj)
        rcases hop with hop | hop
        · rw [hop]
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro hall i hi
          have h1 := hall i hi
          by_cases hil : i < n + (w - n)
          · rw [ite_eq_left hil] at h1 ⊢
            exact ih i (by omega) h1
          · rw [ite_eq_right hil] at h1
            exact absurd h1 (by decide)
        · rw [hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i, hi, h1⟩
          refine ⟨i, hi, ?_⟩
          by_cases hil : i < n + (w - n)
          · rw [ite_eq_left hil] at h1 ⊢
            exact ih i (by omega) h1
          · rw [ite_eq_right hil] at h1
            exact absurd h1 (by decide)
      · rw [wireVal_ge C x w (by omega)]
        intro h; exact absurd h (by decide)

private def shiftIdx (cut rep i : ℕ) : ℕ :=
  if i < cut then i else if i = cut then rep else i - 1

private lemma shiftIdx_lt (cut rep i : ℕ) (h : i < cut) : shiftIdx cut rep i = i := by
  unfold shiftIdx; exact ite_eq_left h

private lemma shiftIdx_eq (cut rep : ℕ) : shiftIdx cut rep cut = rep := by
  unfold shiftIdx; rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]

private lemma shiftIdx_gt (cut rep i : ℕ) (h : ¬i < cut) (hne : i ≠ cut) :
    shiftIdx cut rep i = i - 1 := by
  unfold shiftIdx; rw [ite_eq_right h, ite_eq_right hne]

private lemma deleteGate {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length) (rep : ℕ)
    (hrep : rep < n + j ∨ rep = n + C.gates.length)
    (heq : ∀ x : Fin n → Bool, wireVal C x (n + j) = wireVal C x rep) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size = C.size - 1 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let gs' : List Gate :=
    C.gates.take j ++ (C.gates.drop (j + 1)).map fun g =>
      ⟨g.op, g.inputs.map (shiftIdx (n + j) rep)⟩
  let C' : Circuit := ⟨gs', shiftIdx (n + j) rep C.output⟩
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs', hlen_take]
    omega
  have hm' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    simp only [C', gs', List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hm g (List.mem_of_mem_take h1)
    · obtain ⟨hop, hlen⟩ := hm g0 (List.mem_of_mem_drop hg0)
      exact ⟨hop, by simpa using hlen⟩
  have hagree : ∀ (x : Fin n → Bool) (w : ℕ),
      (w < n + j → wireVal C' x w = wireVal C x w) ∧
      (∀ k < C.gates.length - (j + 1), w = n + j + k → wireVal C' x w = wireVal C x (n + j + 1 + k)) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      constructor
      · intro hlt
        by_cases hlt_n : w < n
        · rw [wireVal_input C' x w hlt_n, wireVal_input C x w hlt_n]
        · have hj1 : w - n < j := by omega
          have hj1' : w - n < C'.gates.length := by omega
          have hj1c : w - n < C.gates.length := by omega
          have hw_eq : n + (w - n) = w := by omega
          rw [← hw_eq, wireVal_gate C' x (w - n) hj1', wireVal_gate C x (w - n) hj1c]
          have hg_eq : C'.gates[w - n] = C.gates[w - n] := by
            simp only [C', gs']
            rw [List.getElem_append_left (by rw [hlen_take]; exact hj1)]
            simp
          rw [hg_eq]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hil : i < n + (w - n)
          · rw [ite_eq_left hil, ite_eq_left hil]
            exact (ih i (by omega)).1 (by omega)
          · rw [ite_eq_right hil, ite_eq_right hil]
      · intro k hk hw
        subst hw
        have hk' : j + k < C'.gates.length := by omega
        have hkc : j + 1 + k < C.gates.length := by omega
        have hidx1 : n + (j + k) = n + j + k := by omega
        have hidx2 : n + (j + 1 + k) = n + j + 1 + k := by omega
        rw [← hidx1, ← hidx2, wireVal_gate C' x (j + k) hk', wireVal_gate C x (j + 1 + k) hkc]
        have hg_eq : C'.gates[j + k] =
            ⟨(C.gates[j + 1 + k]).op, (C.gates[j + 1 + k]).inputs.map (shiftIdx (n + j) rep)⟩ := by
          simp only [C', gs']
          rw [List.getElem_append_right (by rw [hlen_take]; omega)]
          simp only [hlen_take, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_drop]
        rw [hg_eq, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
        by_cases h1 : i < n + j
        · simp only [shiftIdx_lt _ _ _ h1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          exact (ih i (by omega)).1 h1
        · by_cases h2 : i = n + j
          · subst h2
            simp only [shiftIdx_eq]
            rw [ite_eq_left (show n + j < n + (j + 1 + k) by omega), heq x]
            rcases hrep with hrl | hre
            · rw [ite_eq_left (by omega)]
              exact (ih rep (by omega)).1 hrl
            · rw [hre, ite_eq_right (by omega), wireVal_ge C x (n + C.gates.length) (le_refl _)]
          · simp only [shiftIdx_gt _ _ _ h1 h2]
            by_cases h3 : i < n + (j + 1 + k)
            · rw [ite_eq_left (by omega), ite_eq_left h3]
              have h4 := (ih (i - 1) (by omega)).2 (i - 1 - (n + j)) (by omega) (by omega)
              have h5 : n + j + 1 + (i - 1 - (n + j)) = i := by omega
              rw [h5] at h4
              exact h4
            · rw [ite_eq_right (by omega), ite_eq_right h3]
  refine ⟨C', hm', hlen', ?_⟩
  intro x
  change wireVal C' x (shiftIdx (n + j) rep C.output) = wireVal C x C.output
  simp only [shiftIdx]
  by_cases h1 : C.output < n + j
  · rw [ite_eq_left h1]
    exact (hagree x C.output).1 h1
  · rw [ite_eq_right h1]
    by_cases h2 : C.output = n + j
    · rw [ite_eq_left h2, h2, heq x]
      rcases hrep with hrl | hre
      · exact (hagree x rep).1 hrl
      · rw [hre, wireVal_ge C' x (n + C.gates.length) (by omega),
            wireVal_ge C x (n + C.gates.length) (le_refl _)]
    · rw [ite_eq_right h2]
      by_cases h3 : C.output < n + C.gates.length
      · have h4 := (hagree x (C.output - 1)).2 (C.output - 1 - (n + j)) (by omega) (by omega)
        have h5 : n + j + 1 + (C.output - 1 - (n + j)) = C.output := by omega
        rw [h5] at h4
        exact h4
      · rw [wireVal_ge C' x (C.output - 1) (by omega), wireVal_ge C x C.output (by omega)]

private lemma deleteTrueGate {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length)
    (htrue : ∀ x : Fin n → Bool, wireVal C x (n + j) = true)
    (hout_ne : C.output ≠ n + j) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size = C.size - 1 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let xform : Gate → Gate := fun g =>
    if (n + j) ∈ g.inputs then
      match g.op with
      | GateOp.or => ⟨GateOp.and, []⟩
      | _ => ⟨g.op, (g.inputs.filter (· ≠ n + j)).map (shiftIdx (n + j) 0)⟩
    else
      ⟨g.op, g.inputs.map (shiftIdx (n + j) 0)⟩
  let gs' : List Gate := C.gates.take j ++ (C.gates.drop (j + 1)).map xform
  let C' : Circuit := ⟨gs', shiftIdx (n + j) 0 C.output⟩
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs', hlen_take]
    omega
  have hm' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    simp only [C', gs', List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hm g (List.mem_of_mem_take h1)
    · obtain ⟨hop, hlen⟩ := hm g0 (List.mem_of_mem_drop hg0)
      simp only [xform]
      split_ifs
      · rcases hop with hop | hop
        · rw [hop]; exact ⟨Or.inl rfl, by simp; exact le_trans (List.length_filter_le _ _) hlen⟩
        · rw [hop]; exact ⟨Or.inl rfl, by simp⟩
      · exact ⟨hop, by simpa using hlen⟩
  have hagree : ∀ (x : Fin n → Bool) (w : ℕ),
      (w < n + j → wireVal C' x w = wireVal C x w) ∧
      (∀ k < C.gates.length - (j + 1), w = n + j + k → wireVal C' x w = wireVal C x (n + j + 1 + k)) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      constructor
      · intro hlt
        by_cases hlt_n : w < n
        · rw [wireVal_input C' x w hlt_n, wireVal_input C x w hlt_n]
        · have hj1 : w - n < j := by omega
          have hj1' : w - n < C'.gates.length := by omega
          have hj1c : w - n < C.gates.length := by omega
          have hw_eq : n + (w - n) = w := by omega
          rw [← hw_eq, wireVal_gate C' x (w - n) hj1', wireVal_gate C x (w - n) hj1c]
          have hg_eq : C'.gates[w - n] = C.gates[w - n] := by
            simp only [C', gs']
            rw [List.getElem_append_left (by rw [hlen_take]; exact hj1)]
            simp
          rw [hg_eq]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hil : i < n + (w - n)
          · rw [ite_eq_left hil, ite_eq_left hil]
            exact (ih i (by omega)).1 (by omega)
          · rw [ite_eq_right hil, ite_eq_right hil]
      · intro k hk hw
        subst hw
        have hk' : j + k < C'.gates.length := by omega
        have hkc : j + 1 + k < C.gates.length := by omega
        have hidx1 : n + (j + k) = n + j + k := by omega
        have hidx2 : n + (j + 1 + k) = n + j + 1 + k := by omega
        rw [← hidx1, ← hidx2, wireVal_gate C' x (j + k) hk', wireVal_gate C x (j + 1 + k) hkc]
        have hg_eq : C'.gates[j + k] = xform (C.gates[j + 1 + k]) := by
          simp only [C', gs']
          rw [List.getElem_append_right (by rw [hlen_take]; omega)]
          simp only [hlen_take, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_drop]
        rw [hg_eq]
        have hne_val : ∀ i : ℕ, i ≠ n + j →
            (if shiftIdx (n + j) 0 i < n + (j + k) then wireVal C' x (shiftIdx (n + j) 0 i) else false) =
            (if i < n + (j + 1 + k) then wireVal C x i else false) := by
          intro i hine
          by_cases h1 : i < n + j
          · simp only [shiftIdx_lt _ _ _ h1]
            rw [ite_eq_left (by omega), ite_eq_left (by omega)]
            exact (ih i (by omega)).1 h1
          · simp only [shiftIdx_gt _ _ _ h1 hine]
            by_cases h3 : i < n + (j + 1 + k)
            · rw [ite_eq_left (by omega), ite_eq_left h3]
              have h4 := (ih (i - 1) (by omega)).2 (i - 1 - (n + j)) (by omega) (by omega)
              have h5 : n + j + 1 + (i - 1 - (n + j)) = i := by omega
              rw [h5] at h4
              exact h4
            · rw [ite_eq_right (by omega), ite_eq_right h3]
        obtain ⟨hop, _⟩ := hm C.gates[j + 1 + k] (List.getElem_mem hkc)
        simp only [xform]
        by_cases hmem : n + j ∈ (C.gates[j + 1 + k]).inputs
        · rw [ite_eq_left hmem]
          rcases hop with hop | hop
          · rw [hop]
            simp only [GateOp.eval, List.map_map, List.all_map]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true, Function.comp_apply, id_eq, List.mem_filter,
              decide_eq_true_eq, and_imp]
            constructor
            · intro h i hi
              by_cases hij : i = n + j
              · subst hij; rw [ite_eq_left (by omega)]; exact htrue x
              · rw [← hne_val i hij]; exact h i hi hij
            · intro h i hi hij
              rw [hne_val i hij]; exact h i hi
          · rw [hop]
            simp only [GateOp.eval, List.map_nil, List.all_nil, List.any_map]
            symm
            rw [List.any_eq_true]
            refine ⟨n + j, hmem, ?_⟩
            simp [show n + j < n + (j + 1 + k) by omega, htrue x]
        · rw [ite_eq_right hmem, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          have hine : i ≠ n + j := fun h => hmem (h ▸ hi)
          exact hne_val i hine
  refine ⟨C', hm', hlen', ?_⟩
  intro x
  change wireVal C' x (shiftIdx (n + j) 0 C.output) = wireVal C x C.output
  simp only [shiftIdx]
  by_cases h1 : C.output < n + j
  · rw [ite_eq_left h1]
    exact (hagree x C.output).1 h1
  · rw [ite_eq_right h1, ite_eq_right hout_ne]
    by_cases h3 : C.output < n + C.gates.length
    · have h4 := (hagree x (C.output - 1)).2 (C.output - 1 - (n + j)) (by omega) (by omega)
      have h5 : n + j + 1 + (C.output - 1 - (n + j)) = C.output := by omega
      rw [h5] at h4
      exact h4
    · rw [wireVal_ge C' x (C.output - 1) (by omega), wireVal_ge C x C.output (by omega)]

private def outdeg (C : Circuit) (w : ℕ) : ℕ :=
  (C.gates.map fun g => g.inputs.count w).sum

private lemma outdeg_zero_unused (C : Circuit) (w : ℕ) (h : outdeg C w = 0) :
    ∀ g ∈ C.gates, w ∉ g.inputs := by
  intro g hg hmem
  have hpos : 0 < g.inputs.count w := List.count_pos_iff.mpr hmem
  have hle : g.inputs.count w ≤ outdeg C w := by
    unfold outdeg
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨g, hg, rfl⟩)
  omega

private lemma minimal_props {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (hdeg1 : ∀ v : Fin n, ∃ u : Fin n, G.Adj v u)
    (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hev : ∀ u v : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true ↔ G.Adj u v)
    (hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      (∀ u v : Fin n, D.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true ↔ G.Adj u v) →
      C.size ≤ D.size) :
    1 ≤ C.gates.length ∧
    C.output = n + C.gates.length - 1 ∧
    (∀ j (hj : j < C.gates.length),
      ∃ a b : ℕ, (C.gates[j]).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j) ∧
    (∀ w < n + C.gates.length, wireVal C (fun _ : Fin n => false) w = false) ∧
    (∀ w < n + C.gates.length - 1, 1 ≤ outdeg C w) := by
  have hzero_out : wireVal C (fun _ : Fin n => false) C.output = false := by
    by_contra h
    have ht : wireVal C (fun _ : Fin n => false) C.output = true := Bool.eq_true_of_not_eq_false h
    let v0 : Fin n := ⟨0, by omega⟩
    have h1 : wireVal C (fun i : Fin n => decide (i = v0 ∨ i = v0)) C.output = true :=
      mono_eval C hm _ _ (fun _ h0 => absurd h0 (by decide)) C.output ht
    have hadj : G.Adj v0 v0 := (hev v0 v0).mp h1
    exact G.ne_of_adj hadj rfl
  have hval0 : ∀ w < n + C.gates.length, wireVal C (fun _ : Fin n => false) w = false := by
    intro w hw
    by_contra h
    have ht : wireVal C (fun _ : Fin n => false) w = true := Bool.eq_true_of_not_eq_false h
    by_cases hwn : w < n
    · rw [wireVal_input C _ w hwn] at ht; exact absurd ht (by decide)
    · have hj : w - n < C.gates.length := by omega
      have hweq : n + (w - n) = w := by omega
      have htrue_all : ∀ x : Fin n → Bool, wireVal C x (n + (w - n)) = true := fun x =>
        mono_eval C hm _ x (fun _ h0 => absurd h0 (by decide)) _ (hweq.symm ▸ ht)
      have hout_ne : C.output ≠ n + (w - n) := by
        intro heq; rw [heq, hweq, ht] at hzero_out; exact absurd hzero_out (by decide)
      obtain ⟨C', hm', hsz', heq'⟩ := deleteTrueGate C hm (w - n) hj htrue_all hout_ne
      have hle := hmin C' hm' (fun u v => by rw [heq']; exact hev u v)
      change C.gates.length ≤ C'.gates.length at hle
      change C'.gates.length = C.gates.length - 1 at hsz'
      omega
  have hout_ge_n : n ≤ C.output := by
    by_contra h
    have hlt : C.output < n := by omega
    let v0 : Fin n := ⟨C.output, hlt⟩
    have h1 : C.eval (List.ofFn fun i : Fin n => decide (i = v0 ∨ i = v0)) = true := by
      change wireVal C _ C.output = true
      rw [wireVal_input C _ C.output hlt]
      simp [v0]
    exact G.ne_of_adj ((hev v0 v0).mp h1) rfl
  have hout_lt : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨u0, hu0⟩ := hdeg1 ⟨0, by omega⟩
    have h1 : C.eval (List.ofFn fun i : Fin n => decide (i = ⟨0, by omega⟩ ∨ i = u0)) = true :=
      (hev ⟨0, by omega⟩ u0).mpr hu0
    have h2 : wireVal C (fun i : Fin n => decide (i = ⟨0, by omega⟩ ∨ i = u0)) C.output = false :=
      wireVal_ge C _ C.output (by omega)
    rw [show C.eval (List.ofFn fun i : Fin n => decide (i = ⟨0, by omega⟩ ∨ i = u0)) =
      wireVal C (fun i : Fin n => decide (i = ⟨0, by omega⟩ ∨ i = u0)) C.output from rfl, h2] at h1
    exact absurd h1 (by decide)
  have hpos_gates : 1 ≤ C.gates.length := by omega
  have hbinary : ∀ j (hj : j < C.gates.length),
      ∃ a b : ℕ, (C.gates[j]).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j := by
    intro j hj
    obtain ⟨hop, hlen⟩ := hm C.gates[j] (List.getElem_mem hj)
    have hdel : ∀ rep, (rep < n + j ∨ rep = n + C.gates.length) →
        (∀ x : Fin n → Bool, wireVal C x (n + j) = wireVal C x rep) → False := by
      intro rep hrep heq
      obtain ⟨C', hm', hsz', heq'⟩ := deleteGate C hm j hj rep hrep heq
      have hle := hmin C' hm' (fun u v => by rw [heq']; exact hev u v)
      change C.gates.length ≤ C'.gates.length at hle
      change C'.gates.length = C.gates.length - 1 at hsz'
      omega
    cases hin : (C.gates[j]).inputs with
    | nil =>
      rcases hop with hop | hop
      · have h1 := hval0 (n + j) (by omega)
        rw [wireVal_gate C _ j hj, hop, hin] at h1
        simp [GateOp.eval] at h1
      · exfalso
        apply hdel (n + C.gates.length) (Or.inr rfl)
        intro x
        rw [wireVal_gate C x j hj, hop, hin, wireVal_ge C x (n + C.gates.length) (le_refl _)]
        rfl
    | cons a rest =>
      cases rest with
      | nil =>
        exfalso
        by_cases ha : a < n + j
        · apply hdel a (Or.inl ha)
          intro x
          rw [wireVal_gate C x j hj, hin]
          rcases hop with hop | hop <;> (rw [hop]; simp [GateOp.eval, ha])
        · apply hdel (n + C.gates.length) (Or.inr rfl)
          intro x
          rw [wireVal_gate C x j hj, hin, wireVal_ge C x (n + C.gates.length) (le_refl _)]
          rcases hop with hop | hop <;> (rw [hop]; simp [GateOp.eval, ha])
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          by_cases ha : a < n + j
          · by_cases hb : b < n + j
            · by_cases hab : a = b
              · exfalso
                subst hab
                apply hdel a (Or.inl ha)
                intro x
                rw [wireVal_gate C x j hj, hin]
                rcases hop with hop | hop <;> (rw [hop]; simp [GateOp.eval, ha])
              · exact ⟨a, b, rfl, hab, ha, hb⟩
            · exfalso
              rcases hop with hop | hop
              · apply hdel (n + C.gates.length) (Or.inr rfl)
                intro x
                rw [wireVal_gate C x j hj, hop, hin, wireVal_ge C x (n + C.gates.length) (le_refl _)]
                simp [GateOp.eval, hb]
              · apply hdel a (Or.inl ha)
                intro x
                rw [wireVal_gate C x j hj, hop, hin]
                simp [GateOp.eval, ha, hb]
          · exfalso
            rcases hop with hop | hop
            · apply hdel (n + C.gates.length) (Or.inr rfl)
              intro x
              rw [wireVal_gate C x j hj, hop, hin, wireVal_ge C x (n + C.gates.length) (le_refl _)]
              simp [GateOp.eval, ha]
            · by_cases hb : b < n + j
              · apply hdel b (Or.inl hb)
                intro x
                rw [wireVal_gate C x j hj, hop, hin]
                simp [GateOp.eval, ha, hb]
              · apply hdel (n + C.gates.length) (Or.inr rfl)
                intro x
                rw [wireVal_gate C x j hj, hop, hin, wireVal_ge C x (n + C.gates.length) (le_refl _)]
                simp [GateOp.eval, ha, hb]
        | cons _ _ =>
          rw [hin] at hlen; simp at hlen
  have hused : ∀ w < n + C.gates.length, w ≠ C.output → 1 ≤ outdeg C w := by
    intro w hw hne
    by_contra h0
    have hz : outdeg C w = 0 := by omega
    have hunused := outdeg_zero_unused C w hz
    by_cases hwn : w < n
    · let u : Fin n := ⟨w, hwn⟩
      obtain ⟨v, huv⟩ := hdeg1 u
      have hsame : ∀ z < n + C.gates.length, z ≠ w →
          wireVal C (fun i : Fin n => decide (i = u ∨ i = v)) z =
          wireVal C (fun i : Fin n => decide (i = v ∨ i = v)) z := by
        intro z hz
        induction z using Nat.strong_induction_on with
        | ind z ih =>
          intro hzw
          by_cases hzn : z < n
          · rw [wireVal_input C _ z hzn, wireVal_input C _ z hzn]
            have hne_u : (⟨z, hzn⟩ : Fin n) ≠ u := fun h => hzw (congrArg Fin.val h)
            simp [hne_u]
          · have hj : z - n < C.gates.length := by omega
            have hzeq : n + (z - n) = z := by omega
            rw [← hzeq, wireVal_gate C _ (z - n) hj, wireVal_gate C _ (z - n) hj]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hiw : i ≠ w := fun h => hunused C.gates[z - n] (List.getElem_mem hj) (h ▸ hi)
            by_cases hil : i < n + (z - n)
            · rw [ite_eq_left hil, ite_eq_left hil]
              exact ih i (by omega) (by omega) hiw
            · rw [ite_eq_right hil, ite_eq_right hil]
      have h1 := hsame C.output hout_lt hne.symm
      have h2 : C.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true := (hev u v).mpr huv
      have h3 : C.eval (List.ofFn fun i : Fin n => decide (i = v ∨ i = v)) = false := by
        by_contra hc
        exact G.ne_of_adj ((hev v v).mp (Bool.eq_true_of_not_eq_false hc)) rfl
      change wireVal C _ C.output = true at h2
      change wireVal C _ C.output = false at h3
      rw [h1, h3] at h2
      exact absurd h2 (by decide)
    · have hj : w - n < C.gates.length := by omega
      have hweq : n + (w - n) = w := by omega
      let gs' : List Gate :=
        C.gates.take (w - n) ++ (C.gates.drop (w - n + 1)).map fun g =>
          ⟨g.op, g.inputs.map (shiftIdx w 0)⟩
      let C' : Circuit := ⟨gs', shiftIdx w 0 C.output⟩
      have hlen_take : (C.gates.take (w - n)).length = w - n := List.length_take_of_le (le_of_lt hj)
      have hlen' : C'.gates.length = C.gates.length - 1 := by simp [C', gs', hlen_take]; omega
      have hm' : PEqualNP.MetaComplexity.Monotone2 C' := by
        intro g hg
        simp only [C', gs', List.mem_append, List.mem_map] at hg
        rcases hg with h1 | ⟨g0, hg0, rfl⟩
        · exact hm g (List.mem_of_mem_take h1)
        · obtain ⟨hop, hlen⟩ := hm g0 (List.mem_of_mem_drop hg0)
          exact ⟨hop, by simpa using hlen⟩
      have hagree : ∀ (x : Fin n → Bool) (z : ℕ),
          (z < w → wireVal C' x z = wireVal C x z) ∧
          (∀ k < C.gates.length - (w - n + 1), z = w + k → wireVal C' x z = wireVal C x (w + 1 + k)) := by
        intro x z
        induction z using Nat.strong_induction_on with
        | ind z ih =>
          constructor
          · intro hlt
            by_cases hlt_n : z < n
            · rw [wireVal_input C' x z hlt_n, wireVal_input C x z hlt_n]
            · have hj1 : z - n < w - n := by omega
              have hj1' : z - n < C'.gates.length := by omega
              have hj1c : z - n < C.gates.length := by omega
              have hzeq : n + (z - n) = z := by omega
              rw [← hzeq, wireVal_gate C' x (z - n) hj1', wireVal_gate C x (z - n) hj1c]
              have hg_eq : C'.gates[z - n] = C.gates[z - n] := by
                simp only [C', gs']
                rw [List.getElem_append_left (by rw [hlen_take]; exact hj1)]
                simp
              rw [hg_eq]
              congr 1
              apply List.map_congr_left
              intro i _
              by_cases hil : i < n + (z - n)
              · rw [ite_eq_left hil, ite_eq_left hil]
                exact (ih i (by omega)).1 (by omega)
              · rw [ite_eq_right hil, ite_eq_right hil]
          · intro k hk hz
            subst hz
            have hk' : w - n + k < C'.gates.length := by omega
            have hkc : w - n + 1 + k < C.gates.length := by omega
            have hidx1 : n + (w - n + k) = w + k := by omega
            have hidx2 : n + (w - n + 1 + k) = w + 1 + k := by omega
            rw [← hidx1, ← hidx2, wireVal_gate C' x (w - n + k) hk', wireVal_gate C x (w - n + 1 + k) hkc]
            have hg_eq : C'.gates[w - n + k] =
                ⟨(C.gates[w - n + 1 + k]).op, (C.gates[w - n + 1 + k]).inputs.map (shiftIdx w 0)⟩ := by
              simp only [C', gs']
              rw [List.getElem_append_right (by rw [hlen_take]; omega)]
              simp only [hlen_take, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_drop]
            rw [hg_eq, List.map_map]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hiw : i ≠ w := fun h => hunused C.gates[w - n + 1 + k] (List.getElem_mem hkc) (h ▸ hi)
            simp only [Function.comp_apply]
            by_cases h1 : i < w
            · simp only [shiftIdx_lt _ _ _ h1]
              rw [ite_eq_left (by omega), ite_eq_left (by omega)]
              exact (ih i (by omega)).1 h1
            · simp only [shiftIdx_gt _ _ _ h1 hiw]
              by_cases h3 : i < n + (w - n + 1 + k)
              · rw [ite_eq_left (by omega), ite_eq_left h3]
                have h4 := (ih (i - 1) (by omega)).2 (i - 1 - w) (by omega) (by omega)
                have h5 : w + 1 + (i - 1 - w) = i := by omega
                rw [h5] at h4
                exact h4
              · rw [ite_eq_right (by omega), ite_eq_right h3]
      have heval' : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
        intro x
        change wireVal C' x (shiftIdx w 0 C.output) = wireVal C x C.output
        simp only [shiftIdx]
        by_cases h1 : C.output < w
        · rw [ite_eq_left h1]
          exact (hagree x C.output).1 h1
        · rw [ite_eq_right h1, ite_eq_right hne.symm]
          have h4 := (hagree x (C.output - 1)).2 (C.output - 1 - w) (by omega) (by omega)
          have h5 : w + 1 + (C.output - 1 - w) = C.output := by omega
          rw [h5] at h4
          exact h4
      have hle := hmin C' hm' (fun u v => by rw [heval']; exact hev u v)
      change C.gates.length ≤ C'.gates.length at hle
      omega
  have hout_last : C.output = n + C.gates.length - 1 := by
    by_contra hne
    have h1 := hused (n + C.gates.length - 1) (by omega) (by omega)
    have hzero : outdeg C (n + C.gates.length - 1) = 0 := by
      unfold outdeg
      have hall : ∀ g ∈ C.gates, g.inputs.count (n + C.gates.length - 1) = 0 := by
        intro g hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        obtain ⟨a, b, hin, _, ha, hb⟩ := hbinary j hj
        rw [hin]
        simp [show a ≠ n + C.gates.length - 1 by omega, show b ≠ n + C.gates.length - 1 by omega]
      have : C.gates.map (fun g => g.inputs.count (n + C.gates.length - 1)) =
          List.replicate C.gates.length 0 := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_replicate]
          have hi : i < C.gates.length := by simpa using h1
          exact hall C.gates[i] (List.getElem_mem hi)
      rw [this]
      simp
    omega
  refine ⟨hpos_gates, hout_last, hbinary, hval0, ?_⟩
  intro w hw
  exact hused w (by omega) (by omega)

private lemma sum_outdeg_eq {n : ℕ} (C : Circuit)
    (hbinary : ∀ j (hj : j < C.gates.length),
      ∃ a b : ℕ, (C.gates[j]).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j) :
    ∑ w ∈ Finset.range (n + C.gates.length - 1), outdeg C w = 2 * C.gates.length := by
  have h1 : ∀ j (hj : j < C.gates.length),
      ∑ w ∈ Finset.range (n + C.gates.length - 1), (C.gates[j]).inputs.count w = 2 := by
    intro j hj
    obtain ⟨a, b, hin, hab, ha, hb⟩ := hbinary j hj
    rw [hin]
    have ha_mem : a ∈ Finset.range (n + C.gates.length - 1) := Finset.mem_range.mpr (by omega)
    have hb_mem : b ∈ Finset.range (n + C.gates.length - 1) := Finset.mem_range.mpr (by omega)
    have hsplit : ∀ w : ℕ, ([a, b] : List ℕ).count w = (if w = a then 1 else 0) + (if w = b then 1 else 0) := by
      intro w
      by_cases hwa : w = a
      · subst hwa; simp [hab]
      · by_cases hwb : w = b
        · subst hwb; simp [hab, hwa]
        · simp [hwa, hwb, Ne.symm hwa, Ne.symm hwb]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    simp [ha_mem, hb_mem]
  have hout_sum : ∀ w, outdeg C w = ∑ j : Fin C.gates.length, (C.gates[j.val]).inputs.count w := by
    intro w
    unfold outdeg
    rw [← List.sum_ofFn (f := fun j : Fin C.gates.length => (C.gates[j.val]).inputs.count w)]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp
  simp_rw [hout_sum]
  rw [Finset.sum_comm]
  have : ∀ j : Fin C.gates.length,
      ∑ w ∈ Finset.range (n + C.gates.length - 1), (C.gates[j.val]).inputs.count w = 2 :=
    fun j => h1 j.val j.isLt
  simp_rw [this]
  simp [Nat.mul_comm]

private lemma unique_consumer {n : ℕ} (C : Circuit)
    (hbinary : ∀ j (hj : j < C.gates.length),
      ∃ a b : ℕ, (C.gates[j]).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j)
    (w : ℕ) (h1 : outdeg C w = 1) :
    ∃! j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs := by
  have hout_sum : outdeg C w = ∑ j : Fin C.gates.length, (C.gates[j.val]).inputs.count w := by
    unfold outdeg
    rw [← List.sum_ofFn (f := fun j : Fin C.gates.length => (C.gates[j.val]).inputs.count w)]
    congr 1
    apply List.ext_getElem <;> simp
  have hcnt : ∀ j : Fin C.gates.length,
      (C.gates[j.val]).inputs.count w = if w ∈ (C.gates[j.val]).inputs then 1 else 0 := by
    intro j
    obtain ⟨a, b, hin, hab, _, _⟩ := hbinary j.val j.isLt
    rw [hin]
    by_cases hwa : w = a
    · subst hwa; simp [hab]
    · by_cases hwb : w = b
      · subst hwb; simp [hab, hwa]
      · simp [hwa, hwb, Ne.symm hwa, Ne.symm hwb]
  rw [hout_sum] at h1
  simp_rw [hcnt] at h1
  rw [Finset.sum_boole, Nat.cast_id] at h1
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
  refine ⟨j, ?_, ?_⟩
  · have hmem : j ∈ Finset.univ.filter (fun k : Fin C.gates.length => w ∈ (C.gates[k.val]).inputs) := by
      rw [hj]; exact Finset.mem_singleton_self j
    exact (Finset.mem_filter.mp hmem).2
  · intro k hk
    have hmem : k ∈ Finset.univ.filter (fun k : Fin C.gates.length => w ∈ (C.gates[k.val]).inputs) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
    rw [hj] at hmem
    exact Finset.mem_singleton.mp hmem

private lemma follow_or {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hbinary : ∀ j (hj : j < C.gates.length),
      ∃ a b : ℕ, (C.gates[j]).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j)
    (u : Fin n) :
    ∃ (b : ℕ) (P : Finset ℕ),
      b < n + C.gates.length ∧
      u.val ∈ P ∧ b ∈ P ∧
      (∀ w ∈ P, w ≤ b) ∧
      (∀ w ∈ P, w ≠ b → outdeg C w = 1 ∧
        ∀ j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs → n + j.val ∈ P ∧ (C.gates[j.val]).op = GateOp.or) ∧
      (∀ w ∈ P, ∀ x : Fin n → Bool, x u = true → wireVal C x w = true) ∧
      (outdeg C b ≠ 1 ∨ ∀ j : Fin C.gates.length, b ∈ (C.gates[j.val]).inputs → (C.gates[j.val]).op = GateOp.and) := by
  classical
  have hstep : ∀ (d : ℕ) (cur : ℕ) (P : Finset ℕ),
      n + C.gates.length - cur ≤ d →
      cur < n + C.gates.length →
      u.val ∈ P → cur ∈ P →
      (∀ w ∈ P, w ≤ cur) →
      (∀ w ∈ P, w ≠ cur → outdeg C w = 1 ∧
        ∀ j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs → n + j.val ∈ P ∧ (C.gates[j.val]).op = GateOp.or) →
      (∀ w ∈ P, ∀ x : Fin n → Bool, x u = true → wireVal C x w = true) →
      ∃ (b : ℕ) (Q : Finset ℕ),
        b < n + C.gates.length ∧
        u.val ∈ Q ∧ b ∈ Q ∧
        (∀ w ∈ Q, w ≤ b) ∧
        (∀ w ∈ Q, w ≠ b → outdeg C w = 1 ∧
          ∀ j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs → n + j.val ∈ Q ∧ (C.gates[j.val]).op = GateOp.or) ∧
        (∀ w ∈ Q, ∀ x : Fin n → Bool, x u = true → wireVal C x w = true) ∧
        (outdeg C b ≠ 1 ∨ ∀ j : Fin C.gates.length, b ∈ (C.gates[j.val]).inputs → (C.gates[j.val]).op = GateOp.and) := by
    intro d
    induction d with
    | zero =>
      intro cur _ hd hlt
      omega
    | succ d ih =>
      intro cur P hd hlt huP hcurP hle hprev htrue
      by_cases h1 : outdeg C cur = 1
      · obtain ⟨j0, hj0_in, hj0_uniq⟩ := unique_consumer C hbinary cur h1
        obtain ⟨hop, _⟩ := hm C.gates[j0.val] (List.getElem_mem j0.isLt)
        rcases hop with hop_and | hop_or
        · refine ⟨cur, P, hlt, huP, hcurP, hle, hprev, htrue, Or.inr ?_⟩
          intro j hj
          have := hj0_uniq j hj
          subst this
          exact hop_and
        · obtain ⟨a, b, hin, _, ha, hb⟩ := hbinary j0.val j0.isLt
          have hcur_lt : cur < n + j0.val := by
            rw [hin] at hj0_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj0_in
            rcases hj0_in with rfl | rfl <;> omega
          apply ih (n + j0.val) (insert (n + j0.val) P) (by omega) (by omega)
            (Finset.mem_insert_of_mem huP) (Finset.mem_insert_self _ _)
          · intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact le_refl _
            · exact le_trans (hle w hw) (le_of_lt hcur_lt)
          · intro w hw hne
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact absurd rfl hne
            · by_cases hwcur : w = cur
              · subst hwcur
                refine ⟨h1, fun j hj => ?_⟩
                have heq := hj0_uniq j hj
                subst heq
                exact ⟨Finset.mem_insert_self _ _, hop_or⟩
              · obtain ⟨hd1, hcons⟩ := hprev w hw hwcur
                exact ⟨hd1, fun j hj => ⟨Finset.mem_insert_of_mem (hcons j hj).1, (hcons j hj).2⟩⟩
          · intro w hw x hxu
            rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [wireVal_gate C x j0.val j0.isLt, hop_or, hin]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                Bool.or_false, id_eq, Bool.or_eq_true]
              rw [hin] at hj0_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hj0_in
              rcases hj0_in with rfl | rfl
              · left; rw [ite_eq_left ha]; exact htrue cur hcurP x hxu
              · right; rw [ite_eq_left hb]; exact htrue cur hcurP x hxu
            · exact htrue w hw x hxu
      · exact ⟨cur, P, hlt, huP, hcurP, hle, hprev, htrue, Or.inl h1⟩
  refine hstep (n + C.gates.length) u.val {u.val} (by omega) (by omega)
    (Finset.mem_singleton_self _) (Finset.mem_singleton_self _)
    (fun w hw => by rw [Finset.mem_singleton.mp hw])
    (fun w hw hne => absurd (Finset.mem_singleton.mp hw) hne)
    (fun w hw x hxu => by
      rw [Finset.mem_singleton.mp hw, wireVal_input C x u.val u.isLt]
      exact hxu)

private lemma main_minimal {n t : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (hdeg1 : ∀ v : Fin n, ∃ u : Fin n, G.Adj v u)
    (htwin : ∀ u v : Fin n, u ≠ v → ¬G.Adj u v →
      2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
      ∃ w : Fin n, ¬(G.Adj u w ↔ G.Adj v w))
    (hnoK22 : ∀ u v : Fin n, G.Adj u v →
      2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
      ∃ a b : Fin n, G.Adj u a ∧ a ≠ v ∧ G.Adj v b ∧ b ≠ u ∧ (a = b ∨ ¬G.Adj a b))
    (hcov_min : ∀ K : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ K ∨ v ∈ K) →
      t ≤ K.card)
    (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hev : ∀ u v : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true ↔ G.Adj u v)
    (hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D →
      (∀ u v : Fin n, D.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true ↔ G.Adj u v) →
      C.size ≤ D.size) :
    n + t ≤ C.size + 1 := by
  classical
  obtain ⟨hpos_gates, hout_last, hbinary, hval0, houtdeg_ge1⟩ := minimal_props G hn hdeg1 C hm hev hmin
  let B : Fin n → ℕ := fun u => (follow_or C hm hbinary u).choose
  let P : Fin n → Finset ℕ := fun u => (follow_or C hm hbinary u).choose_spec.choose
  have hspec : ∀ u : Fin n,
      B u < n + C.gates.length ∧
      u.val ∈ P u ∧ B u ∈ P u ∧
      (∀ w ∈ P u, w ≤ B u) ∧
      (∀ w ∈ P u, w ≠ B u → outdeg C w = 1 ∧
        ∀ j : Fin C.gates.length, w ∈ (C.gates[j.val]).inputs → n + j.val ∈ P u ∧ (C.gates[j.val]).op = GateOp.or) ∧
      (∀ w ∈ P u, ∀ x : Fin n → Bool, x u = true → wireVal C x w = true) ∧
      (outdeg C (B u) ≠ 1 ∨ ∀ j : Fin C.gates.length, B u ∈ (C.gates[j.val]).inputs → (C.gates[j.val]).op = GateOp.and) :=
    fun u => (follow_or C hm hbinary u).choose_spec.choose_spec
  have hout_not_P : ∀ u : Fin n, C.output ∉ P u := by
    intro u hmem
    have ht : wireVal C (fun i : Fin n => decide (i = u ∨ i = u)) C.output = true :=
      (hspec u).2.2.2.2.2.1 C.output hmem _ (by simp)
    exact G.ne_of_adj ((hev u u).mp ht) rfl
  have hB_lt_out : ∀ u : Fin n, B u < n + C.gates.length - 1 := by
    intro u
    have h1 := (hspec u).1
    have h2 : B u ≠ C.output := fun h => hout_not_P u (h ▸ (hspec u).2.2.1)
    omega
  have hP_inputs : ∀ u : Fin n, ∀ i : Fin n, i.val ∈ P u → i = u := by
    intro u i hi
    by_contra hne
    have ht : wireVal C (fun j : Fin n => decide (j = u)) i.val = true :=
      (hspec u).2.2.2.2.2.1 i.val hi _ (by simp)
    rw [wireVal_input C _ i.val i.isLt] at ht
    simp [hne] at ht
  have hB_inj : ∀ u v : Fin n, 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
      B u = B v → u = v := by
    intro u v hdu hdv hBeq
    by_contra huv
    let W := B u
    let E := (P u ∪ P v).erase W
    have hagree_uv : ∀ (x y : Fin n → Bool),
        (∀ i : Fin n, i ≠ u → i ≠ v → x i = y i) →
        wireVal C x W = wireVal C y W →
        ∀ w < n + C.gates.length, w ∉ E → wireVal C x w = wireVal C y w := by
      intro x y hxy hW w hw
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwE
        by_cases hwW : w = W
        · rw [hwW]; exact hW
        · by_cases hwn : w < n
          · rw [wireVal_input C x w hwn, wireVal_input C y w hwn]
            have hnu : (⟨w, hwn⟩ : Fin n) ≠ u := by
              intro h
              have : w = u.val := congrArg Fin.val h
              apply hwE
              exact Finset.mem_erase.mpr ⟨hwW, Finset.mem_union_left _ (this ▸ (hspec u).2.1)⟩
            have hnv : (⟨w, hwn⟩ : Fin n) ≠ v := by
              intro h
              have : w = v.val := congrArg Fin.val h
              apply hwE
              exact Finset.mem_erase.mpr ⟨hwW, Finset.mem_union_right _ (this ▸ (hspec v).2.1)⟩
            exact hxy ⟨w, hwn⟩ hnu hnv
          · have hj : w - n < C.gates.length := by omega
            have heq : n + (w - n) = w := by omega
            rw [← heq, wireVal_gate C x (w - n) hj, wireVal_gate C y (w - n) hj]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hiE : i ∉ E := by
              intro hiE
              obtain ⟨hiW, hiP⟩ := Finset.mem_erase.mp hiE
              rcases Finset.mem_union.mp hiP with hiu | hiv
              · have hnext := ((hspec u).2.2.2.2.1 i hiu hiW).2 ⟨w - n, hj⟩ hi
                rw [heq] at hnext
                exact hwE (Finset.mem_erase.mpr ⟨hwW, Finset.mem_union_left _ hnext.1⟩)
              · have hnext := ((hspec v).2.2.2.2.1 i hiv (hBeq ▸ hiW)).2 ⟨w - n, hj⟩ hi
                rw [heq] at hnext
                exact hwE (Finset.mem_erase.mpr ⟨hwW, Finset.mem_union_right _ hnext.1⟩)
            by_cases hil : i < n + (w - n)
            · rw [ite_eq_left hil, ite_eq_left hil]
              exact ih i (by omega) (by omega) hiE
            · rw [ite_eq_right hil, ite_eq_right hil]
    have houtE : C.output ∉ E := by
      intro h
      rcases Finset.mem_union.mp (Finset.mem_of_mem_erase h) with h1 | h2
      · exact hout_not_P u h1
      · exact hout_not_P v h2
    have hnot_adj : ¬G.Adj u v := by
      intro hadj
      have h1 := hagree_uv (fun i => decide (i = u ∨ i = v)) (fun i => decide (i = u ∨ i = u))
        (fun i hiu hiv => by simp [hiu, hiv])
        (by
          rw [(hspec u).2.2.2.2.2.1 W (hspec u).2.2.1 _ (by simp),
              (hspec u).2.2.2.2.2.1 W (hspec u).2.2.1 _ (by simp)])
        C.output (by omega) houtE
      have ht : C.eval (List.ofFn fun i => decide (i = u ∨ i = v)) = true := (hev u v).mpr hadj
      have hf : C.eval (List.ofFn fun i => decide (i = u ∨ i = u)) = false := by
        by_contra hc; exact G.ne_of_adj ((hev u u).mp (Bool.eq_true_of_not_eq_false hc)) rfl
      change wireVal C _ C.output = true at ht
      change wireVal C _ C.output = false at hf
      rw [h1, hf] at ht
      exact absurd ht (by decide)
    obtain ⟨w0, hw0⟩ := htwin u v huv hnot_adj hdu hdv
    apply hw0
    by_cases hwu : w0 = u
    · subst hwu; exact ⟨fun h => absurd rfl (G.ne_of_adj h), fun h => absurd h.symm hnot_adj⟩
    · by_cases hwv : w0 = v
      · subst hwv; exact ⟨fun h => absurd h hnot_adj, fun h => absurd rfl (G.ne_of_adj h)⟩
      · have h1 := hagree_uv (fun i => decide (i = u ∨ i = w0)) (fun i => decide (i = v ∨ i = w0))
          (fun i hiu hiv => by simp [hiu, hiv])
          (by
            rw [(hspec u).2.2.2.2.2.1 W (hspec u).2.2.1 _ (by simp),
                show W = B v from hBeq, (hspec v).2.2.2.2.2.1 (B v) (hspec v).2.2.1 _ (by simp)])
          C.output (by omega) houtE
        rw [← hev u w0, ← hev v w0]
        change wireVal C _ C.output = true ↔ wireVal C _ C.output = true
        rw [h1]
  have hP_disj : ∀ u v : Fin n, 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
      u ≠ v → Disjoint (P u) (P v) := by
    intro u v hdu hdv huv
    rw [Finset.disjoint_left]
    intro w hwu hwv
    have hreach : ∀ (d : ℕ) (z : ℕ), n + C.gates.length - z ≤ d → z ∈ P u → z ∈ P v → False := by
      intro d
      induction d with
      | zero =>
        intro z hd hzu _
        have := (hspec u).2.2.2.1 z hzu
        have := (hspec u).1
        omega
      | succ d ih =>
        intro z hd hzu hzv
        by_cases hbu : z = B u
        · by_cases hbv : z = B v
          · exact huv (hB_inj u v hdu hdv (hbu.symm.trans hbv))
          · obtain ⟨hd1, hcons⟩ := (hspec v).2.2.2.2.1 z hzv hbv
            obtain ⟨j0, hj0_in, _⟩ := unique_consumer C hbinary z hd1
            have hor := (hcons j0 hj0_in).2
            rcases (hspec u).2.2.2.2.2.2 with hne1 | hand
            · exact hne1 (hbu ▸ hd1)
            · have ha := hand j0 (hbu ▸ hj0_in)
              rw [ha] at hor; cases hor
        · by_cases hbv : z = B v
          · obtain ⟨hd1, hcons⟩ := (hspec u).2.2.2.2.1 z hzu hbu
            obtain ⟨j0, hj0_in, _⟩ := unique_consumer C hbinary z hd1
            have hor := (hcons j0 hj0_in).2
            rcases (hspec v).2.2.2.2.2.2 with hne1 | hand
            · exact hne1 (hbv ▸ hd1)
            · have ha := hand j0 (hbv ▸ hj0_in)
              rw [ha] at hor; cases hor
          · obtain ⟨hd1, hcons_u⟩ := (hspec u).2.2.2.2.1 z hzu hbu
            obtain ⟨_, hcons_v⟩ := (hspec v).2.2.2.2.1 z hzv hbv
            obtain ⟨j0, hj0_in, _⟩ := unique_consumer C hbinary z hd1
            obtain ⟨a, b, hin, _, ha, hb⟩ := hbinary j0.val j0.isLt
            have hz_lt : z < n + j0.val := by
              rw [hin] at hj0_in
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hj0_in
              rcases hj0_in with rfl | rfl <;> omega
            exact ih (n + j0.val) (by omega) (hcons_u j0 hj0_in).1 (hcons_v j0 hj0_in).1
    exact hreach (n + C.gates.length) w (by omega) hwu hwv
  let K : Finset (Fin n) := Finset.univ.filter fun u =>
    2 ≤ (G.neighborSet u).ncard ∧ 2 ≤ outdeg C (B u)
  have hK_cov : ∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
      u ∈ K ∨ v ∈ K := by
    intro u v huv hdu hdv
    by_contra hneither
    simp only [not_or, K, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hneither
    have hdu1 : outdeg C (B u) = 1 := by
      have hge := houtdeg_ge1 (B u) (hB_lt_out u)
      have hlt := hneither.1 hdu
      omega
    have hdv1 : outdeg C (B v) = 1 := by
      have hge := houtdeg_ge1 (B v) (hB_lt_out v)
      have hlt := hneither.2 hdv
      omega
    have huv_ne : u ≠ v := G.ne_of_adj huv
    have hdisj := hP_disj u v hdu hdv huv_ne
    obtain ⟨ju, hju_in, hju_uniq⟩ := unique_consumer C hbinary (B u) hdu1
    obtain ⟨jv, hjv_in, hjv_uniq⟩ := unique_consumer C hbinary (B v) hdv1
    have hju_and : (C.gates[ju.val]).op = GateOp.and := by
      rcases (hspec u).2.2.2.2.2.2 with h | h
      · exact absurd hdu1 h
      · exact h ju hju_in
    have hjv_and : (C.gates[jv.val]).op = GateOp.and := by
      rcases (hspec v).2.2.2.2.2.2 with h | h
      · exact absurd hdv1 h
      · exact h jv hjv_in
    have hBu_lt : B u < n + ju.val := by
      obtain ⟨a, b, hin, _, ha, hb⟩ := hbinary ju.val ju.isLt
      rw [hin] at hju_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hju_in
      rcases hju_in with rfl | rfl <;> omega
    have hBv_lt : B v < n + jv.val := by
      obtain ⟨a, b, hin, _, ha, hb⟩ := hbinary jv.val jv.isLt
      rw [hin] at hjv_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hjv_in
      rcases hjv_in with rfl | rfl <;> omega
    have hju_not_Pu : n + ju.val ∉ P u := by
      intro hmem; have := (hspec u).2.2.2.1 (n + ju.val) hmem; omega
    have hjv_not_Pv : n + jv.val ∉ P v := by
      intro hmem; have := (hspec v).2.2.2.1 (n + jv.val) hmem; omega
    by_cases hjeq : ju = jv
    · subst hjeq
      have hBu_ne_Bv : B u ≠ B v := fun h => huv_ne (hB_inj u v hdu hdv h)
      obtain ⟨a0, b0, hin, hab0, ha0, hb0⟩ := hbinary ju.val ju.isLt
      have hinputs_eq : (a0 = B u ∧ b0 = B v) ∨ (a0 = B v ∧ b0 = B u) := by
        rw [hin] at hju_in hjv_in
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hju_in hjv_in
        rcases hju_in with h1 | h1 <;> rcases hjv_in with h2 | h2
        · exact absurd (h1.trans h2.symm) hBu_ne_Bv
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
        · exact absurd (h1.trans h2.symm) hBu_ne_Bv
      have hval_ju : ∀ x : Fin n → Bool,
          wireVal C x (n + ju.val) = (wireVal C x (B u) && wireVal C x (B v)) := by
        intro x
        rw [wireVal_gate C x ju.val ju.isLt, hju_and, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, ite_eq_left ha0, ite_eq_left hb0]
        rcases hinputs_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Bool.and_comm _ _
      have hagree_outside_Pu : ∀ (x y : Fin n → Bool),
          (∀ i : Fin n, i ≠ u → x i = y i) →
          wireVal C x (n + ju.val) = wireVal C y (n + ju.val) →
          ∀ w < n + C.gates.length, w ∉ P u → wireVal C x w = wireVal C y w := by
        intro x y hxy hju_eq w hw
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwP
          by_cases hwju : w = n + ju.val
          · rw [hwju]; exact hju_eq
          · by_cases hwn : w < n
            · rw [wireVal_input C x w hwn, wireVal_input C y w hwn]
              have hnu : (⟨w, hwn⟩ : Fin n) ≠ u := fun h => hwP ((show w = u.val from congrArg Fin.val h) ▸ (hspec u).2.1)
              exact hxy ⟨w, hwn⟩ hnu
            · have hj : w - n < C.gates.length := by omega
              have heq : n + (w - n) = w := by omega
              rw [← heq, wireVal_gate C x (w - n) hj, wireVal_gate C y (w - n) hj]
              congr 1
              apply List.map_congr_left
              intro i hi
              have hiP : i ∉ P u := by
                intro hiP
                by_cases hiB : i = B u
                · have hval_eq : w - n = ju.val := congrArg Fin.val (hju_uniq ⟨w - n, hj⟩ (hiB ▸ hi))
                  exact hwju (by omega)
                · have hnext := ((hspec u).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                  rw [heq] at hnext
                  exact hwP hnext.1
              by_cases hil : i < n + (w - n)
              · rw [ite_eq_left hil, ite_eq_left hil]
                exact ih i (by omega) (by omega) hiP
              · rw [ite_eq_right hil, ite_eq_right hil]
      have hagree_lt_Pu : ∀ (x y : Fin n → Bool),
          (∀ i : Fin n, i ≠ u → x i = y i) →
          ∀ w < n + ju.val, w ∉ P u → wireVal C x w = wireVal C y w := by
        intro x y hxy w hw
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwP
          by_cases hwn : w < n
          · rw [wireVal_input C x w hwn, wireVal_input C y w hwn]
            have hnu : (⟨w, hwn⟩ : Fin n) ≠ u := fun h => hwP ((show w = u.val from congrArg Fin.val h) ▸ (hspec u).2.1)
            exact hxy ⟨w, hwn⟩ hnu
          · have hj : w - n < C.gates.length := by omega
            have heq : n + (w - n) = w := by omega
            rw [← heq, wireVal_gate C x (w - n) hj, wireVal_gate C y (w - n) hj]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hiP : i ∉ P u := by
              intro hiP
              by_cases hiB : i = B u
              · have := hju_uniq ⟨w - n, hj⟩ (hiB ▸ hi)
                have hval_eq : w - n = ju.val := congrArg Fin.val this
                omega
              · have hnext := ((hspec u).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                rw [heq] at hnext
                exact hwP hnext.1
            by_cases hil : i < n + (w - n)
            · rw [ite_eq_left hil, ite_eq_left hil]
              exact ih i (by omega) (by omega) hiP
            · rw [ite_eq_right hil, ite_eq_right hil]
      have hagree_outside_Pv : ∀ (x y : Fin n → Bool),
          (∀ i : Fin n, i ≠ v → x i = y i) →
          wireVal C x (n + ju.val) = wireVal C y (n + ju.val) →
          ∀ w < n + C.gates.length, w ∉ P v → wireVal C x w = wireVal C y w := by
        intro x y hxy hju_eq w hw
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwP
          by_cases hwju : w = n + ju.val
          · rw [hwju]; exact hju_eq
          · by_cases hwn : w < n
            · rw [wireVal_input C x w hwn, wireVal_input C y w hwn]
              have hnv : (⟨w, hwn⟩ : Fin n) ≠ v := fun h => hwP ((show w = v.val from congrArg Fin.val h) ▸ (hspec v).2.1)
              exact hxy ⟨w, hwn⟩ hnv
            · have hj : w - n < C.gates.length := by omega
              have heq : n + (w - n) = w := by omega
              rw [← heq, wireVal_gate C x (w - n) hj, wireVal_gate C y (w - n) hj]
              congr 1
              apply List.map_congr_left
              intro i hi
              have hiP : i ∉ P v := by
                intro hiP
                by_cases hiB : i = B v
                · have hval_eq : w - n = ju.val := congrArg Fin.val (hjv_uniq ⟨w - n, hj⟩ (hiB ▸ hi))
                  exact hwju (by omega)
                · have hnext := ((hspec v).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                  rw [heq] at hnext
                  exact hwP hnext.1
              by_cases hil : i < n + (w - n)
              · rw [ite_eq_left hil, ite_eq_left hil]
                exact ih i (by omega) (by omega) hiP
              · rw [ite_eq_right hil, ite_eq_right hil]
      have hagree_lt_Pv : ∀ (x y : Fin n → Bool),
          (∀ i : Fin n, i ≠ v → x i = y i) →
          ∀ w < n + ju.val, w ∉ P v → wireVal C x w = wireVal C y w := by
        intro x y hxy w hw
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwP
          by_cases hwn : w < n
          · rw [wireVal_input C x w hwn, wireVal_input C y w hwn]
            have hnv : (⟨w, hwn⟩ : Fin n) ≠ v := fun h => hwP ((show w = v.val from congrArg Fin.val h) ▸ (hspec v).2.1)
            exact hxy ⟨w, hwn⟩ hnv
          · have hj : w - n < C.gates.length := by omega
            have heq : n + (w - n) = w := by omega
            rw [← heq, wireVal_gate C x (w - n) hj, wireVal_gate C y (w - n) hj]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hiP : i ∉ P v := by
              intro hiP
              by_cases hiB : i = B v
              · have := hjv_uniq ⟨w - n, hj⟩ (hiB ▸ hi)
                have hval_eq : w - n = ju.val := congrArg Fin.val this
                omega
              · have hnext := ((hspec v).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                rw [heq] at hnext
                exact hwP hnext.1
            by_cases hil : i < n + (w - n)
            · rw [ite_eq_left hil, ite_eq_left hil]
              exact ih i (by omega) (by omega) hiP
            · rw [ite_eq_right hil, ite_eq_right hil]
      obtain ⟨a, b, hua, hav, hvb, hbu, hab_disj⟩ := hnoK22 u v huv hdu hdv
      have hBv_a : wireVal C (fun i => decide (i = a ∨ i = a)) (B v) = true := by
        by_contra h
        have hf : wireVal C (fun i => decide (i = a ∨ i = a)) (B v) = false := Bool.eq_false_iff.mpr h
        have hBv_not_Pu : B v ∉ P u := Finset.disjoint_right.mp hdisj (hspec v).2.2.1
        have hBv_ua : wireVal C (fun i => decide (i = u ∨ i = a)) (B v) = false := by
          rw [hagree_lt_Pu (fun i => decide (i = u ∨ i = a)) (fun i => decide (i = a ∨ i = a))
            (fun i hiu => by simp [hiu]) (B v) hBv_lt hBv_not_Pu, hf]
        have hju_eq : wireVal C (fun i => decide (i = u ∨ i = a)) (n + ju.val) =
            wireVal C (fun i => decide (i = a ∨ i = a)) (n + ju.val) := by
          rw [hval_ju, hval_ju, hBv_ua, hf]; simp
        have hout_eq := hagree_outside_Pu (fun i => decide (i = u ∨ i = a)) (fun i => decide (i = a ∨ i = a))
          (fun i hiu => by simp [hiu]) hju_eq C.output (by omega) (hout_not_P u)
        have ht : wireVal C (fun i => decide (i = u ∨ i = a)) C.output = true := (hev u a).mpr hua
        have hfa : wireVal C (fun i => decide (i = a ∨ i = a)) C.output = false := by
          by_contra hc; exact G.ne_of_adj ((hev a a).mp (Bool.eq_true_of_not_eq_false hc)) rfl
        rw [hout_eq, hfa] at ht; exact absurd ht (by decide)
      have hBu_b : wireVal C (fun i => decide (i = b ∨ i = b)) (B u) = true := by
        by_contra h
        have hf : wireVal C (fun i => decide (i = b ∨ i = b)) (B u) = false := Bool.eq_false_iff.mpr h
        have hBu_not_Pv : B u ∉ P v := Finset.disjoint_left.mp hdisj (hspec u).2.2.1
        have hBu_vb : wireVal C (fun i => decide (i = v ∨ i = b)) (B u) = false := by
          rw [hagree_lt_Pv (fun i => decide (i = v ∨ i = b)) (fun i => decide (i = b ∨ i = b))
            (fun i hiv => by simp [hiv]) (B u) hBu_lt hBu_not_Pv, hf]
        have hju_eq : wireVal C (fun i => decide (i = v ∨ i = b)) (n + ju.val) =
            wireVal C (fun i => decide (i = b ∨ i = b)) (n + ju.val) := by
          rw [hval_ju, hval_ju, hBu_vb, hf]; simp
        have hout_eq := hagree_outside_Pv (fun i => decide (i = v ∨ i = b)) (fun i => decide (i = b ∨ i = b))
          (fun i hiv => by simp [hiv]) hju_eq C.output (by omega) (hout_not_P v)
        have ht : wireVal C (fun i => decide (i = v ∨ i = b)) C.output = true := (hev v b).mpr hvb
        have hfb : wireVal C (fun i => decide (i = b ∨ i = b)) C.output = false := by
          by_contra hc; exact G.ne_of_adj ((hev b b).mp (Bool.eq_true_of_not_eq_false hc)) rfl
        rw [hout_eq, hfb] at ht; exact absurd ht (by decide)
      have hju_ab : wireVal C (fun i => decide (i = a ∨ i = b)) (n + ju.val) = true := by
        rw [hval_ju]
        have h1 : wireVal C (fun i => decide (i = a ∨ i = b)) (B u) = true :=
          mono_eval C hm _ _ (fun i hi => by simp only [decide_eq_true_eq, or_self] at hi; simp [hi]) (B u) hBu_b
        have h2 : wireVal C (fun i => decide (i = a ∨ i = b)) (B v) = true :=
          mono_eval C hm _ _ (fun i hi => by simp only [decide_eq_true_eq, or_self] at hi; simp [hi]) (B v) hBv_a
        rw [h1, h2]; rfl
      have hlift : ∀ w < n + C.gates.length, w ∉ P u → w ∉ P v →
          wireVal C (fun i => decide (i = u ∨ i = v)) w = true →
          wireVal C (fun i => decide (i = a ∨ i = b)) w = true := by
        intro w hw
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hwPu hwPv hwt
          by_cases hwju : w = n + ju.val
          · rw [hwju]; exact hju_ab
          · by_cases hwn : w < n
            · rw [wireVal_input C _ w hwn] at hwt
              simp only [decide_eq_true_eq] at hwt
              rcases hwt with h1 | h2
              · exact absurd ((show w = u.val from congrArg Fin.val h1) ▸ (hspec u).2.1) hwPu
              · exact absurd ((show w = v.val from congrArg Fin.val h2) ▸ (hspec v).2.1) hwPv
            · have hj : w - n < C.gates.length := by omega
              have heq : n + (w - n) = w := by omega
              rw [← heq, wireVal_gate C _ (w - n) hj] at hwt ⊢
              obtain ⟨hop, _⟩ := hm C.gates[w - n] (List.getElem_mem hj)
              have hi_not_P : ∀ i ∈ (C.gates[w - n]).inputs, i ∉ P u ∧ i ∉ P v := by
                intro i hi
                constructor
                · intro hiP
                  by_cases hiB : i = B u
                  · have hval_eq : w - n = ju.val := congrArg Fin.val (hju_uniq ⟨w - n, hj⟩ (hiB ▸ hi))
                    exact hwju (by omega)
                  · have hnext := ((hspec u).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                    rw [heq] at hnext; exact hwPu hnext.1
                · intro hiP
                  by_cases hiB : i = B v
                  · have hval_eq : w - n = ju.val := congrArg Fin.val (hjv_uniq ⟨w - n, hj⟩ (hiB ▸ hi))
                    exact hwju (by omega)
                  · have hnext := ((hspec v).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                    rw [heq] at hnext; exact hwPv hnext.1
              rcases hop with hop | hop
              · rw [hop] at hwt ⊢
                simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hwt ⊢
                intro i hi
                have h1 := hwt i hi
                by_cases hil : i < n + (w - n)
                · rw [ite_eq_left hil] at h1 ⊢
                  exact ih i (by omega) (by omega) (hi_not_P i hi).1 (hi_not_P i hi).2 h1
                · rw [ite_eq_right hil] at h1; exact absurd h1 (by decide)
              · rw [hop] at hwt ⊢
                simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwt ⊢
                obtain ⟨i, hi, h1⟩ := hwt
                refine ⟨i, hi, ?_⟩
                by_cases hil : i < n + (w - n)
                · rw [ite_eq_left hil] at h1 ⊢
                  exact ih i (by omega) (by omega) (hi_not_P i hi).1 (hi_not_P i hi).2 h1
                · rw [ite_eq_right hil] at h1; exact absurd h1 (by decide)
      have hab_adj : G.Adj a b :=
        (hev a b).mp (hlift C.output (by omega) (hout_not_P u) (hout_not_P v) ((hev u v).mpr huv))
      rcases hab_disj with rfl | hna
      · exact G.ne_of_adj hab_adj rfl
      · exact hna hab_adj
    · have hsub2 : ∀ (p q : Fin n) (jp jq : Fin C.gates.length),
          G.Adj p q → p ≠ q → Disjoint (P p) (P q) →
          B p ∈ (C.gates[jp.val]).inputs → (∀ j, B p ∈ (C.gates[j.val]).inputs → j = jp) →
          (C.gates[jp.val]).op = GateOp.and →
          B q ∈ (C.gates[jq.val]).inputs → (∀ j, B q ∈ (C.gates[j.val]).inputs → j = jq) →
          jp.val < jq.val → False := by
        intro p q jp jq hpq hpq_ne hpq_disj hBp_in hjp_uniq hjp_and hBq_in hjq_uniq hlt_j
        obtain ⟨a0, b0, hin, hab0, ha0, hb0⟩ := hbinary jp.val jp.isLt
        have hy_ex : ∃ y : ℕ, y ∈ (C.gates[jp.val]).inputs ∧ y ≠ B p ∧ y < n + jp.val := by
          rw [hin] at hBp_in ⊢
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hBp_in ⊢
          rcases hBp_in with rfl | rfl
          · exact ⟨b0, Or.inr rfl, Ne.symm hab0, hb0⟩
          · exact ⟨a0, Or.inl rfl, hab0, ha0⟩
        obtain ⟨y, hy_in, hy_ne, hy_lt⟩ := hy_ex
        have hy_not_Pp : y ∉ P p := by
          intro hyP
          have hnext := ((hspec p).2.2.2.2.1 y hyP hy_ne).2 jp hy_in
          have hle := (hspec p).2.2.2.1 (n + jp.val) hnext.1
          have hBp_lt : B p < n + jp.val := by
            rw [hin] at hBp_in
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hBp_in
            rcases hBp_in with rfl | rfl <;> omega
          omega
        have hy_not_Pq : y ∉ P q := by
          intro hyQ
          by_cases hyB : y = B q
          · have := hjq_uniq jp (hyB ▸ hy_in)
            have : jp.val = jq.val := congrArg Fin.val this
            omega
          · have hnext := ((hspec q).2.2.2.2.1 y hyQ hyB).2 jp hy_in
            rw [hjp_and] at hnext
            cases hnext.2
        have hzero_lt : ∀ (x : Fin n → Bool), (∀ i : Fin n, i ≠ p → i ≠ q → x i = false) →
            ∀ w < n + jp.val, w ∉ P p → w ∉ P q → wireVal C x w = false := by
          intro x hx w hw
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hwPp hwPq
            by_cases hwn : w < n
            · rw [wireVal_input C x w hwn]
              have hnp : (⟨w, hwn⟩ : Fin n) ≠ p := fun h => hwPp ((show w = p.val from congrArg Fin.val h) ▸ (hspec p).2.1)
              have hnq : (⟨w, hwn⟩ : Fin n) ≠ q := fun h => hwPq ((show w = q.val from congrArg Fin.val h) ▸ (hspec q).2.1)
              exact hx ⟨w, hwn⟩ hnp hnq
            · have hj : w - n < C.gates.length := by omega
              have heq : n + (w - n) = w := by omega
              rw [← heq, wireVal_gate C x (w - n) hj]
              have hall_false : ∀ i ∈ (C.gates[w - n]).inputs,
                  (if i < n + (w - n) then wireVal C x i else false) = false := by
                intro i hi
                by_cases hil : i < n + (w - n)
                · rw [ite_eq_left hil]
                  have hiPp : i ∉ P p := by
                    intro hiP
                    by_cases hiB : i = B p
                    · have := hjp_uniq ⟨w - n, hj⟩ (hiB ▸ hi)
                      have : w - n = jp.val := congrArg Fin.val this
                      omega
                    · have hnext := ((hspec p).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                      rw [heq] at hnext; exact hwPp hnext.1
                  have hiPq : i ∉ P q := by
                    intro hiQ
                    by_cases hiB : i = B q
                    · have := hjq_uniq ⟨w - n, hj⟩ (hiB ▸ hi)
                      have : w - n = jq.val := congrArg Fin.val this
                      omega
                    · have hnext := ((hspec q).2.2.2.2.1 i hiQ hiB).2 ⟨w - n, hj⟩ hi
                      rw [heq] at hnext; exact hwPq hnext.1
                  exact ih i (by omega) (by omega) hiPp hiPq
                · rw [ite_eq_right hil]
              obtain ⟨hop, _⟩ := hm C.gates[w - n] (List.getElem_mem hj)
              obtain ⟨c, d, hcd, _, _, _⟩ := hbinary (w - n) hj
              have hc := hall_false c (by rw [hcd]; simp)
              have hd := hall_false d (by rw [hcd]; simp)
              rw [hcd]
              rcases hop with hop | hop <;> (rw [hop]; simp only [GateOp.eval, List.map_cons, List.map_nil, hc, hd]; rfl)
        have hy_pq : wireVal C (fun i => decide (i = p ∨ i = q)) y = false :=
          hzero_lt _ (fun i hip hiq => by simp [hip, hiq]) y hy_lt hy_not_Pp hy_not_Pq
        have hy_q : wireVal C (fun i => decide (i = q ∨ i = q)) y = false :=
          hzero_lt _ (fun i hip hiq => by simp [hiq]) y hy_lt hy_not_Pp hy_not_Pq
        have hjp_false : ∀ x : Fin n → Bool, wireVal C x y = false → wireVal C x (n + jp.val) = false := by
          intro x hxy
          rw [wireVal_gate C x jp.val jp.isLt, hjp_and]
          simp only [GateOp.eval, List.all_map, List.all_eq_false]
          refine ⟨y, hy_in, ?_⟩
          simp [hy_lt, hxy]
        have hjp_eq : wireVal C (fun i => decide (i = p ∨ i = q)) (n + jp.val) =
            wireVal C (fun i => decide (i = q ∨ i = q)) (n + jp.val) := by
          rw [hjp_false _ hy_pq, hjp_false _ hy_q]
        have hagree_p : ∀ w < n + C.gates.length, w ∉ P p →
            wireVal C (fun i => decide (i = p ∨ i = q)) w =
            wireVal C (fun i => decide (i = q ∨ i = q)) w := by
          intro w hw
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hwPp
            by_cases hwjp : w = n + jp.val
            · rw [hwjp]; exact hjp_eq
            · by_cases hwn : w < n
              · rw [wireVal_input C _ w hwn, wireVal_input C _ w hwn]
                have hnp : (⟨w, hwn⟩ : Fin n) ≠ p := fun h => hwPp ((show w = p.val from congrArg Fin.val h) ▸ (hspec p).2.1)
                simp [hnp]
              · have hj : w - n < C.gates.length := by omega
                have heq : n + (w - n) = w := by omega
                rw [← heq, wireVal_gate C _ (w - n) hj, wireVal_gate C _ (w - n) hj]
                congr 1
                apply List.map_congr_left
                intro i hi
                have hiPp : i ∉ P p := by
                  intro hiP
                  by_cases hiB : i = B p
                  · have hval_eq : w - n = jp.val := congrArg Fin.val (hjp_uniq ⟨w - n, hj⟩ (hiB ▸ hi))
                    exact hwjp (by omega)
                  · have hnext := ((hspec p).2.2.2.2.1 i hiP hiB).2 ⟨w - n, hj⟩ hi
                    rw [heq] at hnext; exact hwPp hnext.1
                by_cases hil : i < n + (w - n)
                · rw [ite_eq_left hil, ite_eq_left hil]
                  exact ih i (by omega) (by omega) hiPp
                · rw [ite_eq_right hil, ite_eq_right hil]
        have hout_eq := hagree_p C.output (by omega) (hout_not_P p)
        have ht : wireVal C (fun i => decide (i = p ∨ i = q)) C.output = true := (hev p q).mpr hpq
        have hf : wireVal C (fun i => decide (i = q ∨ i = q)) C.output = false := by
          by_contra hc; exact G.ne_of_adj ((hev q q).mp (Bool.eq_true_of_not_eq_false hc)) rfl
        rw [hout_eq, hf] at ht
        exact absurd ht (by decide)
      have hne_val : ju.val ≠ jv.val := fun h => hjeq (Fin.ext h)
      rcases lt_or_gt_of_ne hne_val with hlt | hgt
      · exact hsub2 u v ju jv huv huv_ne hdisj hju_in hju_uniq hju_and hjv_in hjv_uniq hlt
      · exact hsub2 v u jv ju huv.symm huv_ne.symm hdisj.symm hjv_in hjv_uniq hjv_and hju_in hju_uniq hgt
  have ht_le_K : t ≤ K.card := hcov_min K hK_cov
  have hK_le : K.card ≤ ∑ w ∈ Finset.range (n + C.gates.length - 1), (outdeg C w - 1) := by
    have hinj : Set.InjOn B K := by
      intro u hu v hv hBeq
      have hu' := (Finset.mem_filter.mp hu).2.1
      have hv' := (Finset.mem_filter.mp hv).2.1
      exact hB_inj u v hu' hv' hBeq
    have hsub : K.image B ⊆ Finset.range (n + C.gates.length - 1) := by
      intro w hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_range.mpr (hB_lt_out u)
    have h1 : K.card = (K.image B).card := (Finset.card_image_of_injOn hinj).symm
    have h2 : (K.image B).card = ∑ w ∈ K.image B, 1 := by simp
    have h3 : ∑ w ∈ K.image B, 1 ≤ ∑ w ∈ K.image B, (outdeg C w - 1) := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have := (Finset.mem_filter.mp hu).2.2
      omega
    have h4 : ∑ w ∈ K.image B, (outdeg C w - 1) ≤
        ∑ w ∈ Finset.range (n + C.gates.length - 1), (outdeg C w - 1) :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have hsum_id : (∑ w ∈ Finset.range (n + C.gates.length - 1), (outdeg C w - 1)) +
      (n + C.gates.length - 1) = 2 * C.gates.length := by
    have hadd : ∀ w ∈ Finset.range (n + C.gates.length - 1), (outdeg C w - 1) + 1 = outdeg C w := by
      intro w hw
      have := houtdeg_ge1 w (Finset.mem_range.mp hw)
      omega
    have hsum1 : ∑ w ∈ Finset.range (n + C.gates.length - 1), ((outdeg C w - 1) + 1) =
        ∑ w ∈ Finset.range (n + C.gates.length - 1), outdeg C w :=
      Finset.sum_congr rfl hadd
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      sum_outdeg_eq C hbinary] at hsum1
    exact hsum1
  change n + t ≤ C.gates.length + 1
  omega

private lemma main_proof
    (n t : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (hdeg1 : ∀ v : Fin n, ∃ u : Fin n, G.Adj v u)
    (htwin : ∀ u v : Fin n, u ≠ v → ¬G.Adj u v →
      2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
      ∃ w : Fin n, ¬(G.Adj u w ↔ G.Adj v w))
    (hnoK22 : ∀ u v : Fin n, G.Adj u v →
      2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
      ∃ a b : Fin n, G.Adj u a ∧ a ≠ v ∧ G.Adj v b ∧ b ≠ u ∧ (a = b ∨ ¬G.Adj a b))
    (hcov_ex : ∃ K : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ K ∨ v ∈ K) ∧
      K.card = t)
    (hcov_min : ∀ K : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ K ∨ v ∈ K) →
      t ≤ K.card)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hev : ∀ u v : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true ↔ G.Adj u v) :
    n + t ≤ C.size + 1 := by
  classical
  by_cases hn2 : 2 ≤ n
  · let P : ℕ → Prop := fun s =>
      ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = s ∧
        ∀ u v : Fin n, D.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true ↔ G.Adj u v
    have hex : ∃ s, P s := ⟨C.size, C, hm, rfl, hev⟩
    let s0 := Nat.find hex
    obtain ⟨D, hDm, hDsz, hDev⟩ := Nat.find_spec hex
    have hDmin : ∀ E : Circuit, PEqualNP.MetaComplexity.Monotone2 E →
        (∀ u v : Fin n, E.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true ↔ G.Adj u v) →
        D.size ≤ E.size := by
      intro E hEm hEev
      rw [hDsz]
      exact Nat.find_min' hex ⟨E, hEm, rfl, hEev⟩
    have hbound := main_minimal G hn2 hdeg1 htwin hnoK22 hcov_min D hDm hDev hDmin
    have hle : D.size ≤ C.size := hDmin C hm hev
    omega
  · cases n with
    | zero =>
      have ht0 : t ≤ (∅ : Finset (Fin 0)).card := hcov_min ∅ (fun u => Fin.elim0 u)
      simp at ht0
      omega
    | succ k =>
      have hk0 : k = 0 := by omega
      subst hk0
      obtain ⟨u, hu⟩ := hdeg1 ⟨0, by omega⟩
      have hu0 : u = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [hu0] at hu
      exact (G.ne_of_adj hu rfl).elim

end PEqualNP.Outside.L_meta_3049

theorem PEqualNP.Outside.L_meta_3049 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x11 x12 : Fin x1), x4.eval (List.ofFn fun (x13 : Fin x1) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ x3.Adj x11 x12) → x1 + x2 ≤ x4.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_3049.main_proof
