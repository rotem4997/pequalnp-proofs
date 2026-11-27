import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6929
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem step (gs : List Gate) (op : GateOp) (o a b : ℕ) (x : List Bool) :
    Circuit.eval ⟨⟨op, [a, b]⟩ :: gs, o⟩ x
      = Circuit.eval ⟨gs, o⟩ (x ++ [op.eval [x.getD a false, x.getD b false]]) := by
  simp [Circuit.eval, Circuit.wires]

theorem pre_true (gs : List Gate) (X : List Bool) (k i : ℕ) (hk : k ≤ gs.length)
    (h : (wf (gs.take k) X).getD i false = true) :
    i < X.length + k ∧ (wf gs X).getD i false = true := by
  have hl : (wf (gs.take k) X).length = X.length + k := by
    rw [wf_len, List.length_take, Nat.min_eq_left hk]
  have hi : i < X.length + k := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h
    exact absurd h (by simp)
  exact ⟨hi, by rw [wire_take gs X k i hi hk]; exact h⟩

theorem or_val (gs : List Gate) (X : List Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    (wf gs X).getD (X.length + k) false = true ↔
      ∃ i ∈ gs[k].inputs, (wf (gs.take k) X).getD i false = true := by
  rw [gate_val gs X k hk, hop]
  show (gs[k].inputs.map fun i => (wf (gs.take k) X).getD i false).any id = true ↔ _
  simp [List.any_eq_true]

theorem and_val (gs : List Gate) (X : List Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    (wf gs X).getD (X.length + k) false = true ↔
      ∀ i ∈ gs[k].inputs, (wf (gs.take k) X).getD i false = true := by
  rw [gate_val gs X k hk, hop]
  show (gs[k].inputs.map fun i => (wf (gs.take k) X).getD i false).all id = true ↔ _
  simp [List.all_eq_true]

end PEqualNP.Outside.L_meta_6929

open PEqualNP.Outside.L_meta_6929 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6929 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 ∧ x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x5 : Fin (42 : ℕ)) => Decidable.decide (↑x5 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x3) Bool.false = Bool.true) → ∃ (x4 : Finset (Fin (42 : ℕ))), (∀ x5 ∈ x4, ↑x5 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) ∧ x4.card ≤ (2 : ℕ) ∧ ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x7 : Fin (42 : ℕ)) => Decidable.decide (x7 ∈ x4))).getD ((42 : ℕ) + x5) Bool.false = Bool.true := by
  intro C hm hex
  classical
  obtain ⟨xS, hxS⟩ : ∃ xS : Fin 42 → Bool, xS = fun i : Fin 42 => decide ((i : ℕ) ∈ ([(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)] : List ℕ)) := ⟨_, rfl⟩
  have hex' : ∃ j, ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      (wf C.gates (List.ofFn xS)).getD (42 + j) false = true := by
    rw [hxS]
    exact hex
  obtain ⟨g, hgj, hgand, hgt⟩ := Nat.find_spec hex'
  have hmin := fun k (hk : k < Nat.find hex') => Nat.find_min hex' hk
  generalize Nat.find hex' = j at hgj hgt hmin
  obtain ⟨hjl, hgeq⟩ := List.getElem?_eq_some_iff.1 hgj
  subst hgeq
  have hXl : ∀ x : Fin 42 → Bool, (List.ofFn x).length = 42 := fun x => by simp
  have legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hm g hg).2⟩
    rcases (hm g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have A : ∀ w, w < 42 + j → (wf C.gates (List.ofFn xS)).getD w false = true →
      ∃ v : Fin 42, (v : ℕ) ∈ ([(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)] : List ℕ) ∧
        (wf C.gates (List.ofFn fun i : Fin 42 => decide (i ∈ ({v} : Finset (Fin 42))))).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw ht
      by_cases hw42 : w < 42
      · rw [wf_keep _ _ _ (by rw [hXl]; exact hw42)] at ht
        have e := getD_ofFn xS ⟨w, hw42⟩
        simp only at e
        rw [e, hxS] at ht
        refine ⟨⟨w, hw42⟩, by simpa using ht, ?_⟩
        rw [wf_keep _ _ _ (by rw [hXl]; exact hw42)]
        have e2 := getD_ofFn (fun i : Fin 42 => decide (i ∈ ({⟨w, hw42⟩} : Finset (Fin 42)))) ⟨w, hw42⟩
        simp only at e2
        rw [e2]
        simp
      · obtain ⟨k, rfl⟩ : ∃ k, w = 42 + k := ⟨w - 42, by omega⟩
        have hkj : k < j := by omega
        have hkl : k < C.gates.length := by omega
        have hor : C.gates[k].op = GateOp.or := by
          rcases (legal _ (List.getElem_mem hkl)).1 with h | h
          · exact absurd ⟨C.gates[k], List.getElem?_eq_getElem hkl, h, ht⟩ (hmin k hkj)
          · exact h
        have ov : ∀ x : Fin 42 → Bool, (wf C.gates (List.ofFn x)).getD (42 + k) false = true ↔
            ∃ i ∈ C.gates[k].inputs, (wf (C.gates.take k) (List.ofFn x)).getD i false = true := by
          intro x
          have h := or_val C.gates (List.ofFn x) k hkl hor
          rw [hXl x] at h
          exact h
        obtain ⟨i, hi, hpi⟩ := (ov xS).1 ht
        obtain ⟨hilt, hiw⟩ := pre_true C.gates (List.ofFn xS) k i (le_of_lt hkl) hpi
        rw [hXl] at hilt
        obtain ⟨v, hv, hvw⟩ := ih i (by omega) (by omega) hiw
        refine ⟨v, hv, (ov _).2 ⟨i, hi, ?_⟩⟩
        rw [← wire_take C.gates _ k i (by rw [hXl]; exact hilt) (le_of_lt hkl)]
        exact hvw
  have av : ∀ x : Fin 42 → Bool, (wf C.gates (List.ofFn x)).getD (42 + j) false = true ↔
      ∀ i ∈ C.gates[j].inputs, (wf (C.gates.take j) (List.ofFn x)).getD i false = true := by
    intro x
    have h := and_val C.gates (List.ofFn x) j hjl hgand
    rw [hXl x] at h
    exact h
  have B : ∀ i ∈ C.gates[j].inputs, i < 42 + j ∧ (wf C.gates (List.ofFn xS)).getD i false = true := by
    intro i hi
    have h := pre_true C.gates (List.ofFn xS) j i (le_of_lt hjl) ((av xS).1 hgt i hi)
    rw [hXl] at h
    exact h
  have hlen := (legal _ (List.getElem_mem hjl)).2
  have step : ∀ i ∈ C.gates[j].inputs, ∃ v : Fin 42, (v : ℕ) ∈ ([(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)] : List ℕ) ∧
      (wf C.gates (List.ofFn fun t : Fin 42 => decide (t ∈ ({v} : Finset (Fin 42))))).getD i false = true :=
    fun i hi => A i (B i hi).1 (B i hi).2
  have up : ∀ (v : Fin 42) (T : Finset (Fin 42)), v ∈ T → ∀ i,
      (wf C.gates (List.ofFn fun t : Fin 42 => decide (t ∈ ({v} : Finset (Fin 42))))).getD i false = true →
      (wf C.gates (List.ofFn fun t : Fin 42 => decide (t ∈ T))).getD i false = true := by
    intro v T hv i h
    exact mono2 C.gates legal _ _ (by simp)
      (fun t => ofFn_mono 42 _ _ (fun u hu => by
        simp only [Finset.mem_singleton, decide_eq_true_eq] at hu ⊢
        rw [hu]; exact hv) t) i h
  have key : ∃ T : Finset (Fin 42), (∀ v ∈ T, (v : ℕ) ∈ ([(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)] : List ℕ)) ∧ T.card ≤ 2 ∧
      ∀ i ∈ C.gates[j].inputs,
        (wf C.gates (List.ofFn fun t : Fin 42 => decide (t ∈ T))).getD i false = true := by
    generalize C.gates[j].inputs = ins at step hlen ⊢
    match ins, hlen, step with
    | [], _, _ => exact ⟨∅, by simp, by simp, by simp⟩
    | [a], _, st =>
      obtain ⟨v, hv, hw⟩ := st a (by simp)
      refine ⟨{v}, ?_, by simp, ?_⟩
      · intro t ht
        rw [Finset.mem_singleton.1 ht]; exact hv
      · intro i hi
        rw [List.mem_singleton.1 hi]; exact hw
    | [a, b], _, st =>
      obtain ⟨v, hv, hw⟩ := st a (by simp)
      obtain ⟨u, hu, hw'⟩ := st b (by simp)
      refine ⟨{v, u}, ?_, Finset.card_le_two, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.1 ht with h | h
        · rw [h]; exact hv
        · rw [Finset.mem_singleton.1 h]; exact hu
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h | h
        · rw [h]; exact up v _ (by simp) _ hw
        · rw [h]; exact up u _ (by simp) _ hw'
    | _ :: _ :: _ :: _, hl, _ => simp at hl
  obtain ⟨T, hT1, hT2, hT3⟩ := key
  refine ⟨T, hT1, hT2, j, C.gates[j], List.getElem?_eq_getElem hjl, hgand, ?_⟩
  show (wf C.gates (List.ofFn fun x7 : Fin 42 => decide (x7 ∈ T))).getD (42 + j) false = true
  refine (av _).2 (fun i hi => ?_)
  rw [← wire_take C.gates _ j i (by rw [hXl]; exact (B i hi).1) (le_of_lt hjl)]
  exact hT3 i hi
