import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3606
open PEqualNP.CircuitLowerBounds

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

theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem fl_at (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) (k : ℕ)
    (hk : k < gs.length) :
    (fl F gs w).getD (w.length + k) false = F (fl F (gs.take k) w) gs[k] ∧
      ∀ a, a < w.length + k → (fl F gs w).getD a false = (fl F (gs.take k) w).getD a false := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : (fl F (gs.take k) w).length = w.length + k := by
    rw [fl_len, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  have e : fl F gs w = fl F (gs.drop (k + 1))
      (fl F (gs.take k) w ++ [F (fl F (gs.take k) w) gs[k]]) := by
    conv_lhs => rw [hsplit]
    rw [fl_append, fl_cons]
  constructor
  · rw [e, fl_keep _ _ _ _ (by simp; omega), ← hlen]
    simp
  · intro a ha
    rw [e, fl_keep _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]

def EV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem pre_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (U V : List Bool), U.length = V.length →
    (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (fl EV gs U).getD i false = true → (fl EV gs V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g gs ih =>
    intro hgs U V hlen h
    rw [fl_cons, fl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · rw [List.length_append, List.length_append, hlen]; rfl
    · apply app_mono U V _ _ hlen h
      intro i
      cases i with
      | zero => exact eval_mono g.op (hgs g List.mem_cons_self) g.inputs U V h
      | succ j => intro h1; simp at h1

theorem not_form (g : Gate) (hg : g.op = GateOp.not) (P : List Bool) (d : ℕ) (hd : P.length ≤ d) :
    EV P g = !P.getD (g.inputs.headD d) false := by
  unfold EV
  rw [hg]
  cases hin : g.inputs with
  | nil =>
    show (!false) = !P.getD d false
    rw [List.getD_eq_default _ _ hd]
  | cons a t => rfl

theorem mono_mid (T : List Gate) (k : ℕ) (hk : k < T.length)
    (hT : ∀ i (h : i < T.length), i ≠ k → (T[i].op = GateOp.and ∨ T[i].op = GateOp.or))
    (U V : List Bool) (hlen : U.length = V.length)
    (hUV : ∀ i, U.getD i false = true → V.getD i false = true)
    (hv : EV (fl EV (T.take k) U) T[k] = true → EV (fl EV (T.take k) V) T[k] = true) :
    ∀ i, (fl EV T U).getD i false = true → (fl EV T V).getD i false = true := by
  have hsplit : T = T.take k ++ T[k] :: T.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have e : ∀ W, fl EV T W = fl EV (T.drop (k + 1))
      (fl EV (T.take k) W ++ [EV (fl EV (T.take k) W) T[k]]) := by
    intro W
    conv_lhs => rw [hsplit]
    rw [fl_append, fl_cons]
  have htake : ∀ g ∈ T.take k, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, e1⟩ := List.getElem_of_mem hg
    rw [List.getElem_take] at e1
    rw [List.length_take] at hi
    rw [← e1]
    exact hT i (by omega) (by omega)
  have hdrop : ∀ g ∈ T.drop (k + 1), g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, e1⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at e1
    rw [List.length_drop] at hi
    rw [← e1]
    exact hT (k + 1 + i) (by omega) (by omega)
  intro i
  rw [e U, e V]
  apply pre_mono _ hdrop
  · rw [List.length_append, List.length_append, fl_len, fl_len, hlen]; rfl
  · apply app_mono _ _ _ _ (by rw [fl_len, fl_len, hlen]) (pre_mono _ htake U V hlen hUV)
    intro j
    cases j with
    | zero => exact hv
    | succ j => intro h1; simp at h1

end PEqualNP.Outside.L_meta_3606

open PEqualNP.Outside.L_meta_3606 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin x1.gates.length), PEqualNP.MetaComplexity.FanInTwo x1 → x2 < x3 → ↑x3 + (1 : ℕ) = x1.size → x1.output = (9 : ℕ) + ↑x3 → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ (x10 : Fin x1.gates.length), (x1.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.not → x10 = x2 ∨ x10 = x3) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x11 : Fin (9 : ℕ)) => Bool.false) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => Bool.true) = Bool.true → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x13 ∧ x13.size ≤ ↑x2 ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x13 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  intro C q2 q3 hF hlt hsz hout hn2 hn3 honly hf0 hf1
  have hq23 : q2.1 < q3.1 := hlt
  have hTlen : (C.gates.take q3.1).length = q3.1 := by
    rw [List.length_take]; exact Nat.min_eq_left (le_of_lt q3.2)
  have hk : q2.1 < (C.gates.take q3.1).length := by rw [hTlen]; exact hq23
  have hT : ∀ i (h : i < (C.gates.take q3.1).length), i ≠ q2.1 →
      ((C.gates.take q3.1)[i].op = GateOp.and ∨ (C.gates.take q3.1)[i].op = GateOp.or) := by
    intro i h hne
    have hi3 : i < q3.1 := by rw [hTlen] at h; exact h
    have hi : i < C.gates.length := lt_trans hi3 q3.2
    rw [List.getElem_take]
    rcases (hF _ (List.getElem_mem hi)).1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      rcases honly ⟨i, hi⟩ h1 with h2 | h2
      · exact hne (congrArg Fin.val h2)
      · have := congrArg Fin.val h2
        simp at this
        omega
  have hnT : ((C.gates.take q3.1)[q2.1]).op = GateOp.not := by
    rw [List.getElem_take]; exact hn2
  have hn3' : (C.gates[q3.1]).op = GateOp.not := hn3
  obtain ⟨a, ha⟩ : ∃ a, a = (C.gates[q3.1]).inputs.headD (9 + q3.1) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ((C.gates.take q3.1)[q2.1]).inputs.headD (9 + q2.1) := ⟨_, rfl⟩
  obtain ⟨PP, hPP⟩ : ∃ PP : (Fin 9 → Bool) → Bool, ∀ x,
      PP x = (fl EV (C.gates.take q3.1) (List.ofFn x)).getD a false := ⟨_, fun _ => rfl⟩
  obtain ⟨UU, hUU⟩ : ∃ UU : (Fin 9 → Bool) → Bool, ∀ x,
      UU x = (fl EV ((C.gates.take q3.1).take q2.1) (List.ofFn x)).getD b false := ⟨_, fun _ => rfl⟩
  have fX : ∀ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 C x = !PP x := by
    intro x
    have hX : (List.ofFn x).length = 9 := by simp
    have h := (fl_at EV C.gates (List.ofFn x) q3.1 q3.2).1
    rw [hX] at h
    show (fl EV C.gates (List.ofFn x)).getD C.output false = _
    rw [hout, h, hPP, ha]
    exact not_form _ hn3' _ _ (le_of_eq (by rw [fl_len, hTlen, hX]))
  have vX : ∀ x : Fin 9 → Bool,
      EV (fl EV ((C.gates.take q3.1).take q2.1) (List.ofFn x)) (C.gates.take q3.1)[q2.1] = !UU x := by
    intro x
    rw [hUU, hb]
    exact not_form _ hnT _ _ (le_of_eq (by
      rw [fl_len, List.length_take, hTlen, Nat.min_eq_left (le_of_lt hq23)]; simp))
  have M : ∀ x y : Fin 9 → Bool, (∀ v, x v = true → y v = true) →
      (UU y = true → UU x = true) → PP x = true → PP y = true := by
    intro x y hxy hv
    rw [hPP, hPP]
    apply mono_mid _ q2.1 hk hT _ _ (by simp) (ofFn_mono 9 x y hxy)
    rw [vX x, vX y]
    intro h1
    cases hy : UU y with
    | false => rfl
    | true => rw [hv hy] at h1; exact h1
  refine ⟨⟨(C.gates.take q3.1).take q2.1, b⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact hF g (List.mem_of_mem_take (List.mem_of_mem_take hg))
  · show ((C.gates.take q3.1).take q2.1).length ≤ q2.1
    exact List.length_take_le _ _
  · funext x
    show (fl EV ((C.gates.take q3.1).take q2.1) (List.ofFn x)).getD b false
      = PEqualNP.MetaComplexity.circuitFun 9 C x
    rw [← hUU x, fX x]
    have z0 := fX (fun _ => false)
    rw [hf0] at z0
    have o1 := fX (fun _ => true)
    rw [hf1] at o1
    have pz : PP (fun _ => false) = true := by
      cases h : PP (fun _ => false) with
      | true => rfl
      | false => rw [h] at z0; exact absurd z0 (by decide)
    have po : PP (fun _ => true) = false := by
      cases h : PP (fun _ => true) with
      | false => rfl
      | true => rw [h] at o1; exact absurd o1 (by decide)
    have uz : UU (fun _ => false) = false := by
      cases h : UU (fun _ => false) with
      | false => rfl
      | true =>
        have := M (fun _ => false) (fun _ => true) (fun v hv => rfl) (fun _ => h) pz
        rw [po] at this; exact absurd this (by decide)
    cases hu : UU x with
    | true =>
      cases hp : PP x with
      | false => rfl
      | true =>
        have := M x (fun _ => true) (fun v hv => rfl) (fun _ => hu) hp
        rw [po] at this; exact absurd this (by decide)
    | false =>
      have := M (fun _ => false) x (fun v hv => absurd hv (by decide))
        (fun h2 => by rw [hu] at h2; exact absurd h2 (by decide)) pz
      rw [this]; rfl
