import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4403

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def f9 (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5

def f8 (x : Fin 8 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4

def mkInput (k : ℕ) (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 4 || x 6, (List.finRange 9).any fun i => k.testBit ↑i && x i]

def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma runGates_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    runGates (g :: gs) w =
      runGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma runGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    runGates (gs1 ++ gs2) w = runGates gs2 (runGates gs1 w) :=
  List.foldl_append

lemma runGates_length (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    rw [runGates_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt {α : Type} (l r : List α) (d : α) (k : ℕ) (hk : k < l.length) :
    (l ++ r).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_append_singleton_eq {α : Type} (l : List α) (v d : α) (k : ℕ) :
    (l ++ [v]).getD k d = if k < l.length then l.getD k d else if k = l.length then v else d := by
  by_cases h1 : k < l.length
  · simp only [h1, ↓reduceIte]
    exact getD_append_left_lt _ _ _ _ h1
  · have hle : l.length ≤ k := Nat.le_of_not_lt h1
    by_cases h2 : k = l.length
    · subst h2
      simp [List.getD_eq_getElem?_getD]
    · simp [h1, h2, List.getD_eq_getElem?_getD, List.getElem?_append_right hle]
      cases hdiff : k - l.length with
      | zero => omega
      | succ m => simp

lemma getD_of_length_le {α : Type} (l : List α) (d : α) (k : ℕ) (hk : l.length ≤ k) :
    l.getD k d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma getD_ofFn_lt {n : ℕ} (f : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (List.ofFn f).getD k false = f ⟨k, hk⟩ := by
  simp [List.getD_eq_getElem?_getD, hk]

lemma getD_mem {α : Type} (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

def readsWire4 (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => decide (g.inputs.head? = some 4)
  | _ => decide (4 ∈ g.inputs)

lemma gate_eval_agree_ne4 (g : Gate) (hno : readsWire4 g = false)
    (w1 w2 : List Bool) (hagree : ∀ k, k ≠ 4 → w1.getD k false = w2.getD k false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  cases hop : g.op with
  | not =>
    simp only [readsWire4, hop, decide_eq_false_iff_not] at hno
    cases hin : g.inputs with
    | nil => simp [GateOp.eval]
    | cons i is =>
      simp only [hin, List.head?_cons, Option.some.injEq] at hno
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      exact congrArg Bool.not (hagree i hno)
  | and =>
    simp only [readsWire4, hop, decide_eq_false_iff_not] at hno
    congr 1
    exact List.map_congr_left fun i hi => hagree i (fun h => hno (h ▸ hi))
  | or =>
    simp only [readsWire4, hop, decide_eq_false_iff_not] at hno
    congr 1
    exact List.map_congr_left fun i hi => hagree i (fun h => hno (h ▸ hi))
  | mod m =>
    simp only [readsWire4, hop, decide_eq_false_iff_not] at hno
    congr 1
    exact List.map_congr_left fun i hi => hagree i (fun h => hno (h ▸ hi))
  | maj =>
    simp only [readsWire4, hop, decide_eq_false_iff_not] at hno
    congr 1
    exact List.map_congr_left fun i hi => hagree i (fun h => hno (h ▸ hi))

lemma runGates_agree_ne4 (gs : List Gate) (hno : ∀ g ∈ gs, readsWire4 g = false)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hagree : ∀ k, k ≠ 4 → w1.getD k false = w2.getD k false) :
    ∀ k, k ≠ 4 → (runGates gs w1).getD k false = (runGates gs w2).getD k false := by
  induction gs generalizing w1 w2 with
  | nil => exact hagree
  | cons g gs ih =>
    have hg : readsWire4 g = false := hno g (by simp)
    have hgs : ∀ g' ∈ gs, readsWire4 g' = false := fun g' hg' => hno g' (by simp [hg'])
    have hv := gate_eval_agree_ne4 g hg w1 w2 hagree
    rw [runGates_cons, runGates_cons, hv]
    apply ih hgs
    · simp [hlen]
    · intro k hk
      rw [getD_append_singleton_eq, getD_append_singleton_eq, hlen]
      by_cases h1 : k < w2.length
      · simp only [h1, ↓reduceIte]
        exact hagree k hk
      · simp only [h1, ↓reduceIte]

lemma runGates_getD4 (gs : List Gate) (w : List Bool) (hw : 4 < w.length) :
    (runGates gs w).getD 4 false = w.getD 4 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [runGates_cons, ih _ (by simp; omega)]
    exact getD_append_left_lt _ _ _ 4 hw

lemma mkInput_length (k : ℕ) (x : Fin 9 → Bool) :
    (mkInput k x).length = 11 := by
  simp [mkInput]

lemma exists_readsWire4 (k : ℕ) (hk : k ∈ [17, 20, 144]) (C : Circuit)
    (hC : ∀ x : Fin 9 → Bool, C.eval (mkInput k x) = f9 x) :
    ∃ g ∈ C.gates, readsWire4 g = true := by
  by_contra hnone
  have hno : ∀ g ∈ C.gates, readsWire4 g = false := by
    intro g hg
    cases h : readsWire4 g with
    | false => rfl
    | true => exact False.elim (hnone ⟨g, hg, h⟩)
  by_cases hout : C.output = 4
  · let x0 : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 1)
    have hev : C.eval (mkInput k x0) = false := by
      have hlen : 4 < (mkInput k x0).length := by rw [mkInput_length]; omega
      change (runGates C.gates (mkInput k x0)).getD C.output false = false
      rw [hout, runGates_getD4 _ _ hlen]
      have h9 : (mkInput k x0).getD 4 false = x0 ⟨4, by omega⟩ := by
        rw [mkInput, getD_append_left_lt _ _ _ 4 (by simp), getD_ofFn_lt _ 4 (by omega)]
      rw [h9]
      rfl
    have hf : f9 x0 = true := by decide
    have h0 := hC x0
    rw [hev, hf] at h0
    contradiction
  · have hpair : ∃ a b : Fin 9 → Bool, f9 a = false ∧ f9 b = true ∧
        ∀ j : ℕ, j ≠ 4 → (mkInput k a).getD j false = (mkInput k b).getD j false := by
      simp at hk
      rcases hk with rfl | rfl | rfl
      · refine ⟨fun j => decide (j = 3 ∨ j = 6 ∨ j = 0),
          fun j => decide (j = 3 ∨ j = 6 ∨ j = 0 ∨ j = 4), by decide, by decide, ?_⟩
        intro j hj
        by_cases hj11 : j < 11
        · have hf11 : ∀ i : Fin 11, i.val ≠ 4 →
              (mkInput 17 fun j => decide (j = 3 ∨ j = 6 ∨ j = 0)).getD i.val false =
              (mkInput 17 fun j => decide (j = 3 ∨ j = 6 ∨ j = 0 ∨ j = 4)).getD i.val false := by
            decide
          exact hf11 ⟨j, hj11⟩ hj
        · rw [getD_of_length_le _ _ j (by rw [mkInput_length]; omega),
              getD_of_length_le _ _ j (by rw [mkInput_length]; omega)]
      · refine ⟨fun j => decide (j = 0 ∨ j = 6 ∨ j = 2),
          fun j => decide (j = 0 ∨ j = 6 ∨ j = 2 ∨ j = 4), by decide, by decide, ?_⟩
        intro j hj
        by_cases hj11 : j < 11
        · have hf11 : ∀ i : Fin 11, i.val ≠ 4 →
              (mkInput 20 fun j => decide (j = 0 ∨ j = 6 ∨ j = 2)).getD i.val false =
              (mkInput 20 fun j => decide (j = 0 ∨ j = 6 ∨ j = 2 ∨ j = 4)).getD i.val false := by
            decide
          exact hf11 ⟨j, hj11⟩ hj
        · rw [getD_of_length_le _ _ j (by rw [mkInput_length]; omega),
              getD_of_length_le _ _ j (by rw [mkInput_length]; omega)]
      · refine ⟨fun j => decide (j = 3 ∨ j = 6 ∨ j = 7),
          fun j => decide (j = 3 ∨ j = 6 ∨ j = 7 ∨ j = 4), by decide, by decide, ?_⟩
        intro j hj
        by_cases hj11 : j < 11
        · have hf11 : ∀ i : Fin 11, i.val ≠ 4 →
              (mkInput 144 fun j => decide (j = 3 ∨ j = 6 ∨ j = 7)).getD i.val false =
              (mkInput 144 fun j => decide (j = 3 ∨ j = 6 ∨ j = 7 ∨ j = 4)).getD i.val false := by
            decide
          exact hf11 ⟨j, hj11⟩ hj
        · rw [getD_of_length_le _ _ j (by rw [mkInput_length]; omega),
              getD_of_length_le _ _ j (by rw [mkInput_length]; omega)]
    rcases hpair with ⟨a, b, ha, hb, hagree⟩
    have heq : C.eval (mkInput k a) = C.eval (mkInput k b) := by
      change (runGates C.gates (mkInput k a)).getD C.output false =
        (runGates C.gates (mkInput k b)).getD C.output false
      exact runGates_agree_ne4 C.gates hno (mkInput k a) (mkInput k b)
        (by rw [mkInput_length, mkInput_length]) hagree C.output hout
    rw [hC a, hC b, ha, hb] at heq
    contradiction

def lift (y : Fin 8 → Bool) (j : Fin 9) : Bool :=
  if h1 : j.val < 4 then y ⟨j.val, by omega⟩
  else if h2 : j.val = 4 then false
  else y ⟨j.val - 1, by omega⟩

lemma f9_lift (y : Fin 8 → Bool) : f9 (lift y) = f8 y := by
  have h0 : lift y 0 = y 0 := rfl
  have h1 : lift y 1 = y 1 := rfl
  have h2 : lift y 2 = y 2 := rfl
  have h3 : lift y 3 = y 3 := rfl
  have h4 : lift y 4 = false := rfl
  have h5 : lift y 5 = y 4 := rfl
  have h6 : lift y 6 = y 5 := rfl
  have h7 : lift y 7 = y 6 := rfl
  have h8 : lift y 8 = y 7 := rfl
  simp only [f9, f8, h0, h1, h2, h3, h4, h5, h6, h7, h8,
    Bool.and_false, Bool.false_and, Bool.or_false]

def evalSym (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr i => w.getD i false

def partner8 (k : ℕ) : ℕ :=
  if k = 17 then 0 else if k = 20 then 2 else 6

def initEnv (k : ℕ) : List (Bool ⊕ ℕ) :=
  [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
   Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 5, Sum.inr (partner8 k)]

lemma initEnv_length (k : ℕ) : (initEnv k).length = 11 := rfl

lemma initEnv_getD4 (k : ℕ) : (initEnv k).getD 4 (Sum.inl false) = Sum.inl false := rfl

lemma initEnv_bounds (k : ℕ) (w : ℕ) (hw : Sum.inr w ∈ initEnv k) : w < 8 := by
  simp only [initEnv, partner8, List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq,
    reduceCtorEq] at hw
  rcases hw with rfl | rfl | rfl | rfl | h | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | contradiction | omega | (split_ifs <;> omega)

lemma any_testBit_17 (x : Fin 9 → Bool) :
    ((List.finRange 9).any fun i => (17 : ℕ).testBit ↑i && x i) = (x 0 || x 4) := by
  have h : List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  rw [h]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  have hb : (17 : ℕ).testBit 0 = true ∧ (17 : ℕ).testBit 1 = false ∧
      (17 : ℕ).testBit 2 = false ∧ (17 : ℕ).testBit 3 = false ∧
      (17 : ℕ).testBit 4 = true ∧ (17 : ℕ).testBit 5 = false ∧
      (17 : ℕ).testBit 6 = false ∧ (17 : ℕ).testBit 7 = false ∧
      (17 : ℕ).testBit 8 = false := by decide
  simp [hb]

lemma any_testBit_20 (x : Fin 9 → Bool) :
    ((List.finRange 9).any fun i => (20 : ℕ).testBit ↑i && x i) = (x 2 || x 4) := by
  have h : List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  rw [h]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  have hb : (20 : ℕ).testBit 0 = false ∧ (20 : ℕ).testBit 1 = false ∧
      (20 : ℕ).testBit 2 = true ∧ (20 : ℕ).testBit 3 = false ∧
      (20 : ℕ).testBit 4 = true ∧ (20 : ℕ).testBit 5 = false ∧
      (20 : ℕ).testBit 6 = false ∧ (20 : ℕ).testBit 7 = false ∧
      (20 : ℕ).testBit 8 = false := by decide
  simp [hb]

lemma any_testBit_144 (x : Fin 9 → Bool) :
    ((List.finRange 9).any fun i => (144 : ℕ).testBit ↑i && x i) = (x 4 || x 7) := by
  have h : List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  rw [h]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  have hb : (144 : ℕ).testBit 0 = false ∧ (144 : ℕ).testBit 1 = false ∧
      (144 : ℕ).testBit 2 = false ∧ (144 : ℕ).testBit 3 = false ∧
      (144 : ℕ).testBit 4 = true ∧ (144 : ℕ).testBit 5 = false ∧
      (144 : ℕ).testBit 6 = false ∧ (144 : ℕ).testBit 7 = true ∧
      (144 : ℕ).testBit 8 = false := by decide
  simp [hb]

lemma initEnv_eval (k : ℕ) (hk : k ∈ [17, 20, 144]) (y : Fin 8 → Bool) (j : ℕ) :
    evalSym (List.ofFn y) ((initEnv k).getD j (Sum.inl false)) = (mkInput k (lift y)).getD j false := by
  have hl0 : lift y 0 = y 0 := rfl
  have hl2 : lift y 2 = y 2 := rfl
  have hl4 : lift y 4 = false := rfl
  have hl7 : lift y 7 = y 6 := rfl
  match j with
  | 0 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 1 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 2 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 3 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 4 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 5 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 6 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 7 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 8 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 9 => simp [initEnv, evalSym, mkInput, List.getD_eq_getElem?_getD]; rfl
  | 10 =>
    simp at hk
    rcases hk with rfl | rfl | rfl
    · simp only [initEnv, partner8, evalSym, mkInput, List.getD_eq_getElem?_getD,
        any_testBit_17, hl0, hl4, Bool.or_false]
      rfl
    · simp only [initEnv, partner8, evalSym, mkInput, List.getD_eq_getElem?_getD,
        any_testBit_20, hl2, hl4, Bool.or_false]
      rfl
    · simp only [initEnv, partner8, evalSym, mkInput, List.getD_eq_getElem?_getD,
        any_testBit_144, hl4, hl7, Bool.false_or]
      rfl
  | n + 11 =>
    rw [getD_of_length_le (initEnv k) _ (n + 11) (by rw [initEnv_length]; omega)]
    rw [getD_of_length_le (mkInput k (lift y)) _ (n + 11) (by rw [mkInput_length]; omega)]
    rfl

def simpAnd : List (Bool ⊕ ℕ) → ℕ → (Bool ⊕ ℕ) × Option Gate
  | [], _ => (Sum.inl true, none)
  | [a], _ => (a, none)
  | [Sum.inl false, _], _ => (Sum.inl false, none)
  | [_, Sum.inl false], _ => (Sum.inl false, none)
  | [Sum.inl true, b], _ => (b, none)
  | [a, Sum.inl true], _ => (a, none)
  | [Sum.inr u, Sum.inr v], next => (Sum.inr next, some ⟨GateOp.and, [u, v]⟩)
  | _, _ => (Sum.inl false, none)

def simpOr : List (Bool ⊕ ℕ) → ℕ → (Bool ⊕ ℕ) × Option Gate
  | [], _ => (Sum.inl false, none)
  | [a], _ => (a, none)
  | [Sum.inl true, _], _ => (Sum.inl true, none)
  | [_, Sum.inl true], _ => (Sum.inl true, none)
  | [Sum.inl false, b], _ => (b, none)
  | [a, Sum.inl false], _ => (a, none)
  | [Sum.inr u, Sum.inr v], next => (Sum.inr next, some ⟨GateOp.or, [u, v]⟩)
  | _, _ => (Sum.inl false, none)

def simpNot : List (Bool ⊕ ℕ) → ℕ → (Bool ⊕ ℕ) × Option Gate
  | [], _ => (Sum.inl true, none)
  | Sum.inl b :: _, _ => (Sum.inl (!b), none)
  | Sum.inr u :: _, next => (Sum.inr next, some ⟨GateOp.not, [u]⟩)

def simpGate (op : GateOp) (args : List (Bool ⊕ ℕ)) (next : ℕ) : (Bool ⊕ ℕ) × Option Gate :=
  match op with
  | GateOp.and => simpAnd args next
  | GateOp.or => simpOr args next
  | GateOp.not => simpNot args next
  | _ => (Sum.inl false, none)

lemma simpGate_fanInTwo (op : GateOp) (args : List (Bool ⊕ ℕ)) (next : ℕ) (g' : Gate)
    (hg : (simpGate op args next).2 = some g') :
    g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  cases op with
  | and =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpAnd] at hg
    · simp [simpGate, simpAnd] at hg
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpAnd] at hg
      subst hg; simp
    · simp [simpGate, simpAnd] at hg
  | or =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpOr] at hg
    · simp [simpGate, simpOr] at hg
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpOr] at hg
      subst hg; simp
    · simp [simpGate, simpOr] at hg
  | not =>
    rcases args with _ | ⟨a, _⟩
    · simp [simpGate, simpNot] at hg
    · rcases a with ⟨_ | _⟩ | u <;> simp [simpGate, simpNot] at hg
      subst hg; simp
  | mod m => simp [simpGate] at hg
  | maj => simp [simpGate] at hg

lemma simpGate_none_bounds (op : GateOp) (args : List (Bool ⊕ ℕ)) (next : ℕ)
    (hlen : args.length ≤ 2) (hnone : (simpGate op args next).2 = none)
    (w : ℕ) (hw : (simpGate op args next).1 = Sum.inr w) :
    Sum.inr w ∈ args := by
  cases op with
  | and =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpAnd] at hw
    · simp [simpGate, simpAnd] at hw; exact List.mem_singleton.mpr hw.symm
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpAnd] at hnone hw <;> simp [hw]
    · simp at hlen
  | or =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpOr] at hw
    · simp [simpGate, simpOr] at hw; exact List.mem_singleton.mpr hw.symm
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpOr] at hnone hw <;> simp [hw]
    · simp at hlen
  | not =>
    rcases args with _ | ⟨a, _⟩
    · simp [simpGate, simpNot] at hw
    · rcases a with ⟨_ | _⟩ | u <;> simp [simpGate, simpNot] at hnone hw
  | mod m => simp [simpGate] at hw
  | maj => simp [simpGate] at hw

lemma simpGate_some_val (op : GateOp) (args : List (Bool ⊕ ℕ)) (next : ℕ) (g' : Gate)
    (hg : (simpGate op args next).2 = some g') :
    (simpGate op args next).1 = Sum.inr next := by
  cases op with
  | and =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpAnd] at hg
    · simp [simpGate, simpAnd] at hg
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpAnd] at hg ⊢
    · simp [simpGate, simpAnd] at hg
  | or =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpOr] at hg
    · simp [simpGate, simpOr] at hg
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpOr] at hg ⊢
    · simp [simpGate, simpOr] at hg
  | not =>
    rcases args with _ | ⟨a, _⟩
    · simp [simpGate, simpNot] at hg
    · rcases a with ⟨_ | _⟩ | u <;> simp [simpGate, simpNot] at hg ⊢
  | mod m => simp [simpGate] at hg
  | maj => simp [simpGate] at hg

lemma simpGate_none_eval (op : GateOp) (args : List (Bool ⊕ ℕ)) (next : ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : args.length ≤ 2) (hnone : (simpGate op args next).2 = none) (w : List Bool) :
    evalSym w (simpGate op args next).1 = op.eval (args.map (evalSym w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpAnd, evalSym, GateOp.eval]
    · simp [simpGate, simpAnd, evalSym, GateOp.eval]
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpAnd, evalSym, GateOp.eval] at hnone ⊢
    · simp at hlen
  · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpOr, evalSym, GateOp.eval]
    · simp [simpGate, simpOr, evalSym, GateOp.eval]
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpOr, evalSym, GateOp.eval] at hnone ⊢
    · simp at hlen
  · rcases args with _ | ⟨a, _⟩
    · simp [simpGate, simpNot, evalSym, GateOp.eval]
    · rcases a with ⟨_ | _⟩ | u <;>
        simp [simpGate, simpNot, evalSym, GateOp.eval] at hnone ⊢

lemma simpGate_some_eval (op : GateOp) (args : List (Bool ⊕ ℕ)) (w : List Bool) (g' : Gate)
    (hg : (simpGate op args w.length).2 = some g') :
    g'.op.eval (g'.inputs.map fun i => w.getD i false) = op.eval (args.map (evalSym w)) := by
  cases op with
  | and =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpAnd] at hg
    · simp [simpGate, simpAnd] at hg
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpAnd] at hg
      subst hg; simp [GateOp.eval, evalSym]
    · simp [simpGate, simpAnd] at hg
  | or =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [simpGate, simpOr] at hg
    · simp [simpGate, simpOr] at hg
    · rcases a with ⟨_ | _⟩ | u <;> rcases b with ⟨_ | _⟩ | v <;>
        simp [simpGate, simpOr] at hg
      subst hg; simp [GateOp.eval, evalSym]
    · simp [simpGate, simpOr] at hg
  | not =>
    rcases args with _ | ⟨a, _⟩
    · simp [simpGate, simpNot] at hg
    · rcases a with ⟨_ | _⟩ | u <;> simp [simpGate, simpNot] at hg
      subst hg; simp [GateOp.eval, evalSym]
  | mod m => simp [simpGate] at hg
  | maj => simp [simpGate] at hg

lemma simpGate_readsWire4_none (g : Gate) (env : List (Bool ⊕ ℕ)) (next : ℕ)
    (hw4 : env.getD 4 (Sum.inl false) = Sum.inl false)
    (hlen : g.inputs.length ≤ 2) (hread : readsWire4 g = true) :
    (simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false)) next).2 = none := by
  cases hop : g.op with
  | not =>
    simp only [readsWire4, hop, decide_eq_true_eq] at hread
    cases hin : g.inputs with
    | nil => simp [hin] at hread
    | cons i is =>
      simp only [hin, List.head?_cons, Option.some.injEq] at hread
      subst hread
      simp only [List.map_cons, simpGate, simpNot, hw4]
  | and =>
    simp only [readsWire4, hop, decide_eq_true_eq] at hread
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [hin] at hread
    · simp only [hin, List.mem_singleton] at hread
      subst hread
      simp only [List.map_cons, List.map_nil, simpGate, simpAnd]
    · simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hread
      rcases hread with rfl | rfl <;>
        simp only [List.map_cons, List.map_nil, simpGate, simpAnd, hw4]
      cases env.getD a (Sum.inl false) with
      | inl b => cases b <;> rfl
      | inr _ => rfl
    · simp [hin] at hlen
  | or =>
    simp only [readsWire4, hop, decide_eq_true_eq] at hread
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [hin] at hread
    · simp only [hin, List.mem_singleton] at hread
      subst hread
      simp only [List.map_cons, List.map_nil, simpGate, simpOr]
    · simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hread
      rcases hread with rfl | rfl
      · simp only [List.map_cons, List.map_nil, simpGate, simpOr, hw4]
        cases env.getD b (Sum.inl false) with
        | inl x => cases x <;> rfl
        | inr _ => rfl
      · simp only [List.map_cons, List.map_nil, simpGate, simpOr, hw4]
        cases env.getD a (Sum.inl false) with
        | inl x => cases x <;> rfl
        | inr _ => rfl
    · simp [hin] at hlen
  | mod m => simp [simpGate]
  | maj => simp [simpGate]

def foldGates (env : List (Bool ⊕ ℕ)) (outGates : List Gate) :
    List Gate → List (Bool ⊕ ℕ) × List Gate
  | [] => (env, outGates)
  | g :: gs =>
    let args := g.inputs.map fun i => env.getD i (Sum.inl false)
    let res := simpGate g.op args (8 + outGates.length)
    let env' := env ++ [res.1]
    let outGates' := match res.2 with | none => outGates | some g' => outGates ++ [g']
    foldGates env' outGates' gs

lemma foldGates_fanInTwo (env : List (Bool ⊕ ℕ)) (outGates gs : List Gate)
    (hout : ∀ g ∈ outGates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ (foldGates env outGates gs).2,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing env outGates with
  | nil => exact hout
  | cons g gs ih =>
    simp only [foldGates]
    apply ih
    cases hres : (simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
        (8 + outGates.length)).2 with
    | none => exact hout
    | some g' =>
      intro x hx
      simp at hx
      rcases hx with hx | rfl
      · exact hout x hx
      · exact simpGate_fanInTwo _ _ _ _ hres

lemma foldGates_length_le (env : List (Bool ⊕ ℕ)) (outGates gs : List Gate) :
    (foldGates env outGates gs).2.length ≤ outGates.length + gs.length := by
  induction gs generalizing env outGates with
  | nil => simp [foldGates]
  | cons g gs ih =>
    simp only [foldGates]
    cases hres : (simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
        (8 + outGates.length)).2 with
    | none =>
      have h1 := ih
        (env ++ [(simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
          (8 + outGates.length)).1]) outGates
      simp only [List.length_cons]
      omega
    | some g' =>
      have h1 := ih
        (env ++ [(simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
          (8 + outGates.length)).1]) (outGates ++ [g'])
      simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
      omega

lemma foldGates_length_lt (env : List (Bool ⊕ ℕ)) (outGates gs : List Gate)
    (hlen4 : 4 < env.length) (hw4 : env.getD 4 (Sum.inl false) = Sum.inl false)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hwit : ∃ g ∈ gs, readsWire4 g = true) :
    (foldGates env outGates gs).2.length < outGates.length + gs.length := by
  induction gs generalizing env outGates with
  | nil =>
    rcases hwit with ⟨g, hg, _⟩
    simp at hg
  | cons g gs ih =>
    simp only [foldGates]
    have hgfan := hfan g (by simp)
    have hgsfan : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    by_cases hrg : readsWire4 g = true
    · have hnone := simpGate_readsWire4_none g env (8 + outGates.length) hw4 hgfan.2 hrg
      rw [hnone]
      have hle := foldGates_length_le
        (env ++ [(simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
          (8 + outGates.length)).1]) outGates gs
      simp only [List.length_cons]
      omega
    · have hwit' : ∃ g' ∈ gs, readsWire4 g' = true := by
        rcases hwit with ⟨g', hg', hr'⟩
        simp at hg'
        rcases hg' with rfl | hg'
        · exact absurd hr' hrg
        · exact ⟨g', hg', hr'⟩
      have hlen4' : 4 < (env ++ [(simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
          (8 + outGates.length)).1]).length := by simp; omega
      have hw4' : (env ++ [(simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
          (8 + outGates.length)).1]).getD 4 (Sum.inl false) = Sum.inl false := by
        rw [getD_append_left_lt _ _ _ 4 hlen4, hw4]
      cases hres : (simpGate g.op (g.inputs.map fun i => env.getD i (Sum.inl false))
          (8 + outGates.length)).2 with
      | none =>
        have hlt := ih _ outGates hlen4' hw4' hgsfan hwit'
        simp only [List.length_cons]
        omega
      | some g' =>
        have hlt := ih _ (outGates ++ [g']) hlen4' hw4' hgsfan hwit'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlt ⊢
        omega

lemma foldGates_eval (y : Fin 8 → Bool) (env : List (Bool ⊕ ℕ)) (outGates gs : List Gate)
    (oldWires : List Bool)
    (hlen : env.length = oldWires.length)
    (hbounds : ∀ w, Sum.inr w ∈ env → w < 8 + outGates.length)
    (heval : ∀ k, evalSym (runGates outGates (List.ofFn y)) (env.getD k (Sum.inl false)) =
      oldWires.getD k false)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ k, evalSym (runGates (foldGates env outGates gs).2 (List.ofFn y))
      ((foldGates env outGates gs).1.getD k (Sum.inl false)) =
      (runGates gs oldWires).getD k false := by
  induction gs generalizing env outGates oldWires with
  | nil =>
    intro k
    simpa [foldGates, runGates] using heval k
  | cons g gs ih =>
    simp only [foldGates]
    rw [runGates_cons]
    have hgfan := hfan g (by simp)
    have hgsfan : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    let args := g.inputs.map fun i => env.getD i (Sum.inl false)
    let res := simpGate g.op args (8 + outGates.length)
    let newWires := runGates outGates (List.ofFn y)
    have hnwlen : newWires.length = 8 + outGates.length := by
      simp [newWires, runGates_length]
    have hargs_len : args.length ≤ 2 := by
      simp [args, hgfan.2]
    have hargs_eval : g.inputs.map (fun i => oldWires.getD i false) = args.map (evalSym newWires) := by
      dsimp only [args]
      rw [List.map_map]
      exact List.map_congr_left fun i _ => (heval i).symm
    have hargs_bounds : ∀ w, Sum.inr w ∈ args → w < 8 + outGates.length := by
      intro w hw
      simp only [args, List.mem_map] at hw
      rcases hw with ⟨i, _, hi⟩
      by_cases hil : i < env.length
      · apply hbounds
        rw [← hi]
        exact getD_mem env (Sum.inl false) i hil
      · rw [getD_of_length_le env _ i (Nat.le_of_not_lt hil)] at hi
        cases hi
    cases hres : res.2 with
    | none =>
      apply ih
      · simp [hlen]
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | hweq
        · exact hbounds w hw
        · exact hargs_bounds w (simpGate_none_bounds g.op args (8 + outGates.length)
            hargs_len hres w hweq.symm)
      · intro k
        rw [getD_append_singleton_eq, getD_append_singleton_eq, hlen]
        by_cases hk1 : k < oldWires.length
        · simp only [hk1, ↓reduceIte]
          exact heval k
        · by_cases hk2 : k = oldWires.length
          · subst hk2
            simp only [hk1, ↓reduceIte]
            change evalSym newWires res.1 = g.op.eval (g.inputs.map fun i => oldWires.getD i false)
            rw [hargs_eval]
            exact simpGate_none_eval g.op args (8 + outGates.length) hgfan.1 hargs_len hres newWires
          · simp only [hk1, hk2, ↓reduceIte, evalSym]
      · exact hgsfan
    | some g' =>
      apply ih
      · simp [hlen]
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | hweq
        · exact Nat.lt_trans (hbounds w hw) (by simp)
        · have hval := simpGate_some_val g.op args (8 + outGates.length) g' hres
          change res.1 = Sum.inr (8 + outGates.length) at hval
          rw [hval] at hweq
          injection hweq with hw_eq
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
      · intro k
        have hrun' : runGates (outGates ++ [g']) (List.ofFn y) =
            newWires ++ [g'.op.eval (g'.inputs.map fun i => newWires.getD i false)] := by
          rw [runGates_append, runGates_cons]
          rfl
        rw [hrun', getD_append_singleton_eq, getD_append_singleton_eq, hlen]
        by_cases hk1 : k < oldWires.length
        · have hk1' : k < env.length := hlen ▸ hk1
          simp only [hk1, ↓reduceIte]
          have hmem : env.getD k (Sum.inl false) ∈ env := getD_mem env (Sum.inl false) k hk1'
          cases hs : env.getD k (Sum.inl false) with
          | inl b =>
            have hek := heval k
            rw [hs] at hek
            exact hek
          | inr w =>
            have hwlt : w < newWires.length := by
              rw [hnwlen]
              apply hbounds
              rw [← hs]
              exact hmem
            have hek := heval k
            rw [hs] at hek
            simp only [evalSym]
            rw [getD_append_left_lt _ _ _ w hwlt]
            exact hek
        · by_cases hk2 : k = oldWires.length
          · subst hk2
            simp only [hk1, ↓reduceIte]
            have hval := simpGate_some_val g.op args (8 + outGates.length) g' hres
            change res.1 = Sum.inr (8 + outGates.length) at hval
            rw [hval]
            simp only [evalSym]
            rw [getD_append_singleton_eq, hnwlen]
            simp only [lt_self_iff_false, ↓reduceIte]
            rw [hargs_eval]
            have hres' : (simpGate g.op args newWires.length).2 = some g' := by
              rw [hnwlen]
              exact hres
            exact simpGate_some_eval g.op args newWires g' hres'
          · simp only [hk1, hk2, ↓reduceIte, evalSym]
      · exact hgsfan

lemma main_aux (k : ℕ) (hk : k ∈ [17, 20, 144]) (C : Circuit)
    (hfan : FanInTwo C) (hsize : C.size ≤ 13)
    (hC : ∀ x : Fin 9 → Bool, C.eval (mkInput k x) = f9 x) :
    HasCircuitSize 8 f8 12 := by
  have hwit : ∃ g ∈ C.gates, readsWire4 g = true := exists_readsWire4 k hk C hC
  let compiled := foldGates (initEnv k) [] C.gates
  have hfan_out : ∀ g ∈ compiled.2,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    foldGates_fanInTwo (initEnv k) [] C.gates (fun _ hg => by simp at hg)
  have hlen_lt : compiled.2.length < C.gates.length := by
    have hlt := foldGates_length_lt (initEnv k) [] C.gates
      (by rw [initEnv_length]; omega) (initEnv_getD4 k) hfan hwit
    simpa using hlt
  have hlen_le : compiled.2.length ≤ 12 := by
    change C.gates.length ≤ 13 at hsize
    omega
  have heval : ∀ y : Fin 8 → Bool,
      evalSym (runGates compiled.2 (List.ofFn y)) (compiled.1.getD C.output (Sum.inl false)) =
        f8 y := by
    intro y
    have hfold := foldGates_eval y (initEnv k) [] C.gates (mkInput k (lift y))
      (by rw [initEnv_length, mkInput_length])
      (fun w hw => initEnv_bounds k w hw)
      (fun j => initEnv_eval k hk y j)
      hfan C.output
    change evalSym (runGates compiled.2 (List.ofFn y))
      (compiled.1.getD C.output (Sum.inl false)) =
      (runGates C.gates (mkInput k (lift y))).getD C.output false at hfold
    rw [hfold]
    have hce : (runGates C.gates (mkInput k (lift y))).getD C.output false =
        C.eval (mkInput k (lift y)) := rfl
    rw [hce, hC (lift y), f9_lift]
  cases hfinal : compiled.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b with
    | false =>
      have hf := heval (fun _ => true)
      rw [hfinal] at hf
      have hf8 : f8 (fun _ => true) = true := by decide
      simp [evalSym, hf8] at hf
    | true =>
      have hf := heval (fun _ => false)
      rw [hfinal] at hf
      have hf8 : f8 (fun _ => false) = false := by decide
      simp [evalSym, hf8] at hf
  | inr outWire =>
    refine ⟨⟨compiled.2, outWire⟩, hfan_out, hlen_le, ?_⟩
    intro y
    have hf := heval y
    rw [hfinal] at hf
    exact hf

end PEqualNP.Outside.L_meta_4403

theorem PEqualNP.Outside.L_meta_4403 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : ℕ → (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : ℕ) (x3 : Fin (9 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)), (List.finRange (9 : ℕ)).any fun (x4 : Fin (9 : ℕ)) => x2.testBit ↑x4 && x3 x4]; ∀ x3 ∈ [(17 : ℕ), (20 : ℕ), (144 : ℕ)], ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x5.eval (x2 x3 x8) = x1 x8) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x9 : Fin (8 : ℕ) → Bool) => x9 (0 : Fin (8 : ℕ)) && x9 (1 : Fin (8 : ℕ)) || x9 (1 : Fin (8 : ℕ)) && x9 (2 : Fin (8 : ℕ)) || x9 (2 : Fin (8 : ℕ)) && x9 (3 : Fin (8 : ℕ)) || x9 (0 : Fin (8 : ℕ)) && x9 (4 : Fin (8 : ℕ)) || x9 (1 : Fin (8 : ℕ)) && x9 (5 : Fin (8 : ℕ)) || x9 (2 : Fin (8 : ℕ)) && x9 (6 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ)) && x9 (7 : Fin (8 : ℕ)) || x9 (4 : Fin (8 : ℕ)) && x9 (6 : Fin (8 : ℕ)) || x9 (5 : Fin (8 : ℕ)) && x9 (7 : Fin (8 : ℕ)) || x9 (7 : Fin (8 : ℕ)) && x9 (4 : Fin (8 : ℕ))) (12 : ℕ) := by
  intro x1 x2 x3 hk C hfan hsize hC
  exact PEqualNP.Outside.L_meta_4403.main_aux x3 hk C hfan hsize hC
