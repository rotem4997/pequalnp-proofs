import Mathlib
import PEqualNP.Defs

namespace LMeta600

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma main_ind (n : ℕ) (C : Circuit) (v : Fin n)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hno : ¬ ∃ (j : ℕ) (g : Gate) (i : ℕ), C.gates[j]? = some g ∧ g.op = GateOp.or ∧ i ∈ g.inputs ∧ i < n + j ∧ ∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD i false = false) :
    ∀ w : ℕ,
      (∃ x : Fin n → Bool, x v = false ∧
        (C.wires (List.ofFn x)).getD w false ≠
        (C.wires (List.ofFn (Function.update x v true))).getD w false) →
      ∀ y : Fin n → Bool, y v = false → (C.wires (List.ofFn y)).getD w false = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro ⟨x, hxv, hne⟩ y hyv
    by_cases hw1 : w < n
    · have h1 : (C.wires (List.ofFn x)).getD w false = x ⟨w, hw1⟩ := by
        rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw1]), ofFn_getD_lt]
      have h2 : (C.wires (List.ofFn (Function.update x v true))).getD w false = Function.update x v true ⟨w, hw1⟩ := by
        rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn (Function.update x v true)) w (by simp [hw1]), ofFn_getD_lt]
      have h3 : (C.wires (List.ofFn y)).getD w false = y ⟨w, hw1⟩ := by
        rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn y) w (by simp [hw1]), ofFn_getD_lt]
      rw [h1, h2] at hne
      by_cases hwv : (⟨w, hw1⟩ : Fin n) = v
      · rw [h3, hwv, hyv]
      · rw [Function.update_of_ne hwv] at hne
        exact absurd rfl hne
    · by_cases hw2 : n + C.gates.length ≤ w
      · have h1 : (C.wires (List.ofFn x)).getD w false = false := by
          rw [wires_eq_foldl]
          exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw2])
        have h2 : (C.wires (List.ofFn (Function.update x v true))).getD w false = false := by
          rw [wires_eq_foldl]
          exact foldl_step_getD_ge C.gates (List.ofFn (Function.update x v true)) w (by simp [hw2])
        rw [h1, h2] at hne
        exact absurd rfl hne
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n with hjdef
        have hwj : w = n + j := by omega
        set g := C.gates[j]'hjlt with hgdef
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
        have hgmem : g ∈ C.gates := List.mem_of_getElem? hg
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by
          have h := (hmono g hgmem).1
          simpa using h
        have hgx : (C.wires (List.ofFn x)).getD w false =
            g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
          rw [hwj]; exact wires_gate_ofFn C x j g hg
        have hgx' : (C.wires (List.ofFn (Function.update x v true))).getD w false =
            g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn (Function.update x v true))).getD i false else false) := by
          rw [hwj]; exact wires_gate_ofFn C (Function.update x v true) j g hg
        have hgy : (C.wires (List.ofFn y)).getD w false =
            g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn y)).getD i false else false) := by
          rw [hwj]; exact wires_gate_ofFn C y j g hg
        rw [hgx, hgx'] at hne
        have hex : ∃ i ∈ g.inputs,
            (if i < n + j then (C.wires (List.ofFn x)).getD i false else false) ≠
            (if i < n + j then (C.wires (List.ofFn (Function.update x v true))).getD i false else false) := by
          by_contra hall
          apply hne
          congr 1
          apply List.map_congr_left
          intro i hi
          by_contra hnei
          exact hall ⟨i, hi, hnei⟩
        obtain ⟨i, hi_mem, hi_ne⟩ := hex
        have hi_lt : i < n + j := by
          by_contra hge
          simp only [hge, ↓reduceIte] at hi_ne
          exact hi_ne rfl
        simp only [hi_lt, ↓reduceIte] at hi_ne
        have hZi : ∀ z : Fin n → Bool, z v = false → (C.wires (List.ofFn z)).getD i false = false :=
          ih i (by omega) ⟨x, hxv, hi_ne⟩
        rcases hgop with hand | hor
        · rw [hgy, hand]
          change (g.inputs.map fun k => if k < n + j then (C.wires (List.ofFn y)).getD k false else false).all id = false
          cases hval : (g.inputs.map fun k => if k < n + j then (C.wires (List.ofFn y)).getD k false else false).all id with
          | false => rfl
          | true =>
            have htrue := List.all_eq_true.mp hval
            have hi_mapped : (if i < n + j then (C.wires (List.ofFn y)).getD i false else false) ∈
                g.inputs.map (fun k => if k < n + j then (C.wires (List.ofFn y)).getD k false else false) :=
              List.mem_map_of_mem hi_mem
            have hres := htrue _ hi_mapped
            simp only [id_eq, hi_lt, ↓reduceIte, hZi y hyv] at hres
            exact absurd hres (by decide)
        · exact absurd ⟨j, g, i, hg, hor, hi_mem, hi_lt, hZi⟩ hno

end LMeta600

theorem PEqualNP.Outside.L_meta_600 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n), PEqualNP.MetaComplexity.Monotone2 C → (∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧ C.eval (List.ofFn (Function.update x v true)) = true) → (∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true) → ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ i ∈ g.inputs ∧ i < n + j ∧ ∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD i false = false := by
  intro n C v hmono hdep hnotle
  by_contra hno
  obtain ⟨x1, hx1v, hx1f, hx1t⟩ := hdep
  obtain ⟨x2, hx2v, hx2t⟩ := hnotle
  have hzero := LMeta600.main_ind n C v hmono hno C.output ⟨x1, hx1v, by
    change C.eval (List.ofFn x1) ≠ C.eval (List.ofFn (Function.update x1 v true))
    rw [hx1f, hx1t]
    decide⟩ x2 hx2v
  change C.eval (List.ofFn x2) = false at hzero
  rw [hx2t] at hzero
  exact absurd hzero (by decide)
