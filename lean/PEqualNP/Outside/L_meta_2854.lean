import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2854
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem gate_full (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length)
    (hrb : ∀ i ∈ gates[k].inputs, i < X.length + k) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf gates X).getD i false) := by
  rw [gate_val gates X k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (wire_take gates X k i (hrb i hi) (le_of_lt hk)).symm

theorem ev_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ ins, f i = true → g i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map g) = true := by
  rcases hop with h' | h' <;> rw [h']
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H i hi => h i hi (H i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hi hv⟩

end PEqualNP.Outside.L_meta_2854

open PEqualNP.Outside.L_meta_2854 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2854 : ∀ (n : ℕ) (C C' : PEqualNP.CircuitLowerBounds.Circuit) (σ : ℕ → ℕ) (m : ℕ) (x : Fin n → Bool), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' → (∀ i < n, σ i = i) → (∀ j < C.gates.length, n ≤ σ (n + j) ∧ σ (n + j) < n + C'.gates.length) → (∀ j < C.gates.length, j ≠ m → (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).op = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (σ (n + j) - n)).inputs = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map σ) → (((C'.wires (List.ofFn x)).getD (σ (n + m)) false = true → (C.wires (List.ofFn x)).getD (n + m) false = true) → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = true → (C.wires (List.ofFn x)).getD (n + j) false = true) ∧ ((C'.wires (List.ofFn x)).getD (σ (n + m)) false = (C.wires (List.ofFn x)).getD (n + m) false → ∀ j < C.gates.length, (C'.wires (List.ofFn x)).getD (σ (n + j)) false = (C.wires (List.ofFn x)).getD (n + j) false) := by
  intro n C C' σ m x hmono hrb hrb' hσ hrange hcopy
  have hC : ∀ j (hj : j < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    intro j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hj]
  have hC' : ∀ j (hj : j < C'.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C' j = C'.gates[j] := by
    intro j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hj]
  have hb : ∀ j (hj : j < C.gates.length), (wf C.gates (List.ofFn x)).getD (n + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => (wf C.gates (List.ofFn x)).getD i false) := by
    intro j hj
    have := gate_full C.gates (List.ofFn x) j hj (by
      intro i hi
      rw [List.length_ofFn]
      have := hrb j hj i
      rw [hC j hj] at this
      exact this hi)
    rw [List.length_ofFn] at this
    exact this
  have ha : ∀ j (hj : j < C.gates.length), j ≠ m → (wf C'.gates (List.ofFn x)).getD (σ (n + j)) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => (wf C'.gates (List.ofFn x)).getD (σ i) false) := by
    intro j hj hjm
    obtain ⟨h1, h2⟩ := hrange j hj
    have hk : σ (n + j) - n < C'.gates.length := by omega
    obtain ⟨hop, hin⟩ := hcopy j hj hjm
    rw [hC' _ hk, hC j hj] at hop hin
    have := gate_full C'.gates (List.ofFn x) (σ (n + j) - n) hk (by
      intro i hi
      rw [List.length_ofFn]
      have := hrb' _ hk i
      rw [hC' _ hk] at this
      exact this hi)
    rw [List.length_ofFn, hop, hin, List.map_map] at this
    have e : n + (σ (n + j) - n) = σ (n + j) := by omega
    rw [e] at this
    exact this
  have hinp : ∀ i < n, (wf C'.gates (List.ofFn x)).getD (σ i) false
      = (wf C.gates (List.ofFn x)).getD i false := by
    intro i hi
    rw [hσ i hi, wf_keep _ _ _ (by simpa using hi), wf_keep _ _ _ (by simpa using hi)]
  have hinl : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j := by
    intro j hj i hi
    have := hrb j hj i
    rw [hC j hj] at this
    exact this hi
  constructor
  · intro hm j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjm : j = m
      · rw [hjm]; exact hm
      · show (wf C'.gates (List.ofFn x)).getD (σ (n + j)) false = true →
          (wf C.gates (List.ofFn x)).getD (n + j) false = true
        rw [ha j hj hjm, hb j hj]
        refine ev_mono _ (by
          rcases (hmono _ (List.getElem_mem hj)).1 with h | h
          · exact Or.inl h
          · exact Or.inr h) _ _ _ ?_
        intro i hi
        have hlt := hinl j hj i hi
        by_cases hin : i < n
        · rw [hinp i hin]; exact id
        · obtain ⟨j', rfl⟩ : ∃ j', i = n + j' := ⟨i - n, by omega⟩
          exact ih j' (by omega) (by omega)
  · intro hm j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjm : j = m
      · rw [hjm]; exact hm
      · show (wf C'.gates (List.ofFn x)).getD (σ (n + j)) false =
          (wf C.gates (List.ofFn x)).getD (n + j) false
        rw [ha j hj hjm, hb j hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlt := hinl j hj i hi
        by_cases hin : i < n
        · exact hinp i hin
        · obtain ⟨j', rfl⟩ : ∃ j', i = n + j' := ⟨i - n, by omega⟩
          exact ih j' (by omega) (by omega)
