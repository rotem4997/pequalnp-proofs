import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4089

open PEqualNP.CircuitLowerBounds

private abbrev diffSet : Finset (Fin 13) := {0, 1, 3, 9}

private def stepVal (r : Fin 3) : Fin 13 :=
  if r = 0 then 1 else if r = 1 then 3 else 9

private def nbrWire (e : Bool × Fin 13 × Fin 3) (d : Fin 13) : ℕ :=
  if e.1 = true then (e.2.1 + d).val else 13 + (e.2.1 - d).val

private def ctrWire (e : Bool × Fin 13 × Fin 3) : ℕ :=
  if e.1 = true then 13 + e.2.1.val else e.2.1.val

private def block0 (e : Bool × Fin 13 × Fin 3) : List Gate :=
  let s := stepVal e.2.2
  [ ⟨.or, [nbrWire e 0, nbrWire e s]⟩
  , ⟨.or, [nbrWire e (3 * s), nbrWire e (9 * s)]⟩
  , ⟨.or, [26, 27]⟩
  , ⟨.and, [ctrWire e, 28]⟩ ]

private def blockStep (e : Bool × Fin 13 × Fin 3) (b : ℕ) : List Gate :=
  let s := stepVal e.2.2
  [ ⟨.or, [nbrWire e 0, nbrWire e s]⟩
  , ⟨.or, [nbrWire e (3 * s), nbrWire e (9 * s)]⟩
  , ⟨.or, [b, b + 1]⟩
  , ⟨.and, [ctrWire e, b + 2]⟩
  , ⟨.or, [b - 1, b + 3]⟩ ]

private def prefixGates (cfg : Fin 9 → Bool × Fin 13 × Fin 3) : ℕ → List Gate
  | 0 => []
  | 1 => block0 (cfg 0)
  | m + 2 =>
    if h : m + 1 < 9 then
      prefixGates cfg (m + 1) ++ blockStep (cfg ⟨m + 1, h⟩) (26 + (5 * (m + 1) - 1))
    else
      prefixGates cfg (m + 1)

private def mkCircuit (cfg : Fin 9 → Bool × Fin 13 × Fin 3) : Circuit :=
  ⟨prefixGates cfg 9, 69⟩

private def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getD_append_lt {α : Type*} (l1 l2 : List α) (d : α) (i : ℕ) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h,
    List.getD_eq_getElem _ _ h]

private theorem getD_append_ge {α : Type*} (l1 l2 : List α) (d : α) (i : ℕ) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  by_cases hlt : i < (l1 ++ l2).length
  · rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right h]
    rw [List.getD_eq_getElem _ _ (by simp at hlt; omega)]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]
    rw [List.getD_eq_default _ _ (by simp at hlt; omega)]

private def inVec (x5 x6 : Finset (Fin 13)) : List Bool :=
  List.ofFn fun (x7 : Fin 26) =>
    Decidable.decide ((∃ x8 ∈ x5, x7 = Fin.castAdd 13 x8) ∨ ∃ x8 ∈ x6, x7 = Fin.natAdd 13 x8)

private theorem inVec_len (x5 x6 : Finset (Fin 13)) : (inVec x5 x6).length = 26 := by
  simp [inVec]

private theorem inVec_getD_left (x5 x6 : Finset (Fin 13)) (a : Fin 13) :
    (inVec x5 x6).getD a.val false = Decidable.decide (a ∈ x5) := by
  have hlt : a.val < 26 := by omega
  rw [List.getD_eq_getElem _ _ (by rw [inVec_len]; exact hlt)]
  simp only [inVec, List.getElem_ofFn]
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨b, hb, heq⟩ | ⟨b, _, heq⟩)
    · have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd] at hv
      exact Fin.ext hv ▸ hb
    · have hv := congrArg Fin.val heq
      simp only [Fin.val_natAdd] at hv
      omega
  · intro ha
    exact Or.inl ⟨a, ha, Fin.ext rfl⟩

private theorem inVec_getD_right (x5 x6 : Finset (Fin 13)) (a : Fin 13) :
    (inVec x5 x6).getD (13 + a.val) false = Decidable.decide (a ∈ x6) := by
  have hlt : 13 + a.val < 26 := by omega
  rw [List.getD_eq_getElem _ _ (by rw [inVec_len]; exact hlt)]
  simp only [inVec, List.getElem_ofFn]
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨b, _, heq⟩ | ⟨b, hb, heq⟩)
    · have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd] at hv
      omega
    · have hv := congrArg Fin.val heq
      simp only [Fin.val_natAdd] at hv
      have hba : a = b := Fin.ext (by omega)
      exact hba ▸ hb
  · intro ha
    exact Or.inr ⟨a, ha, Fin.ext rfl⟩

private abbrev nbrProp (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13)) (d : Fin 13) : Prop :=
  if e.1 = true then e.2.1 + d ∈ x5 else e.2.1 - d ∈ x6

private abbrev ctrProp (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13)) : Prop :=
  if e.1 = true then e.2.1 ∈ x6 else e.2.1 ∈ x5

private abbrev itemProp (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13)) : Prop :=
  ctrProp e x5 x6 ∧ ∃ d ∈ diffSet, nbrProp e x5 x6 d

private theorem diffSet_iff (r : Fin 3) (d : Fin 13) :
    d ∈ diffSet ↔ d = 0 ∨ d = stepVal r ∨ d = 3 * stepVal r ∨ d = 9 * stepVal r := by
  revert r d
  decide

private theorem nbr_getD (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13))
    (w : List Bool) (hw : ∀ j < 26, w.getD j false = (inVec x5 x6).getD j false) (d : Fin 13) :
    w.getD (nbrWire e d) false = Decidable.decide (nbrProp e x5 x6 d) := by
  rcases e with ⟨b1, c, r⟩
  cases b1
  · simp only [nbrWire, nbrProp, Bool.false_eq_true, ↓reduceIte]
    rw [hw _ (by omega), inVec_getD_right]
  · simp only [nbrWire, nbrProp, ↓reduceIte]
    rw [hw _ (by omega), inVec_getD_left]

private theorem ctr_getD (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13))
    (w : List Bool) (hw : ∀ j < 26, w.getD j false = (inVec x5 x6).getD j false) :
    w.getD (ctrWire e) false = Decidable.decide (ctrProp e x5 x6) := by
  rcases e with ⟨b1, c, r⟩
  cases b1
  · simp only [ctrWire, ctrProp, Bool.false_eq_true, ↓reduceIte]
    rw [hw _ (by omega), inVec_getD_left]
  · simp only [ctrWire, ctrProp, ↓reduceIte]
    rw [hw _ (by omega), inVec_getD_right]

private theorem item_or_eq (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13)) :
    (Decidable.decide (ctrProp e x5 x6) &&
      (Decidable.decide (nbrProp e x5 x6 0 ∨ nbrProp e x5 x6 (stepVal e.2.2)) ||
       Decidable.decide (nbrProp e x5 x6 (3 * stepVal e.2.2) ∨ nbrProp e x5 x6 (9 * stepVal e.2.2)))) =
    Decidable.decide (itemProp e x5 x6) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, itemProp]
  constructor
  · rintro ⟨hc, (h0 | h1) | (h2 | h3)⟩
    · exact ⟨hc, 0, (diffSet_iff e.2.2 0).mpr (Or.inl rfl), h0⟩
    · exact ⟨hc, stepVal e.2.2, (diffSet_iff e.2.2 _).mpr (Or.inr (Or.inl rfl)), h1⟩
    · exact ⟨hc, 3 * stepVal e.2.2, (diffSet_iff e.2.2 _).mpr (Or.inr (Or.inr (Or.inl rfl))), h2⟩
    · exact ⟨hc, 9 * stepVal e.2.2, (diffSet_iff e.2.2 _).mpr (Or.inr (Or.inr (Or.inr rfl))), h3⟩
  · rintro ⟨hc, d, hd, hnd⟩
    refine ⟨hc, ?_⟩
    rcases (diffSet_iff e.2.2 d).mp hd with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl hnd)
    · exact Or.inl (Or.inr hnd)
    · exact Or.inr (Or.inl hnd)
    · exact Or.inr (Or.inr hnd)

private theorem block0_mono (e : Bool × Fin 13 × Fin 3) :
    ∀ g ∈ block0 e, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [block0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

private theorem blockStep_mono (e : Bool × Fin 13 × Fin 3) (b : ℕ) :
    ∀ g ∈ blockStep e b, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [blockStep, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem prefixGates_mono (cfg : Fin 9 → Bool × Fin 13 × Fin 3) (m : ℕ) :
    ∀ g ∈ prefixGates cfg m, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction m with
  | zero => simp [prefixGates]
  | succ m ih =>
    cases m with
    | zero => exact block0_mono (cfg 0)
    | succ k =>
      intro g hg
      simp only [prefixGates] at hg
      split_ifs at hg with hlt
      · rcases List.mem_append.mp hg with h1 | h2
        · exact ih g h1
        · exact blockStep_mono _ _ g h2
      · exact ih g hg

private theorem prefixGates_len (cfg : Fin 9 → Bool × Fin 13 × Fin 3) (m : ℕ)
    (h1 : 1 ≤ m) (h9 : m ≤ 9) :
    (prefixGates cfg m).length = 5 * m - 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp [prefixGates, block0]
    | succ k =>
      have hlt : k + 1 < 9 := by omega
      simp only [prefixGates, hlt, ↓reduceDIte, List.length_append, blockStep, List.length_cons,
        List.length_nil]
      have hprev := ih (by omega) (by omega)
      omega

private theorem block0_eval (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13)) :
    let w0 := inVec x5 x6
    let w1 := (block0 e).foldl stepGate w0
    let v0 := Decidable.decide (nbrProp e x5 x6 0 ∨ nbrProp e x5 x6 (stepVal e.2.2))
    let v1 := Decidable.decide (nbrProp e x5 x6 (3 * stepVal e.2.2) ∨ nbrProp e x5 x6 (9 * stepVal e.2.2))
    w1 = w0 ++ [v0, v1, v0 || v1, Decidable.decide (itemProp e x5 x6)] := by
  intro w0 w1 v0 v1
  have hlen : w0.length = 26 := inVec_len x5 x6
  have hw0 : ∀ j < 26, w0.getD j false = (inVec x5 x6).getD j false := fun _ _ => rfl
  have h0 : (block0 e).foldl stepGate w0 =
      stepGate (stepGate (stepGate (stepGate w0
        ⟨.or, [nbrWire e 0, nbrWire e (stepVal e.2.2)]⟩)
        ⟨.or, [nbrWire e (3 * stepVal e.2.2), nbrWire e (9 * stepVal e.2.2)]⟩)
        ⟨.or, [26, 27]⟩)
        ⟨.and, [ctrWire e, 28]⟩ := rfl
  dsimp only [w1]
  rw [h0]
  simp only [stepGate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true, List.append_assoc,
    List.cons_append, List.nil_append]
  have hn0 := nbr_getD e x5 x6 w0 hw0 0
  have hn1 := nbr_getD e x5 x6 w0 hw0 (stepVal e.2.2)
  have hn2 := nbr_getD e x5 x6 w0 hw0 (3 * stepVal e.2.2)
  have hn3 := nbr_getD e x5 x6 w0 hw0 (9 * stepVal e.2.2)
  have hc := ctr_getD e x5 x6 w0 hw0
  have hsub1 : ∀ d : Fin 13, nbrWire e d < w0.length := by
    intro d; rw [hlen]; unfold nbrWire; split_ifs <;> omega
  have hsubC : ctrWire e < w0.length := by
    rw [hlen]; unfold ctrWire; split_ifs <;> omega
  have hv0 : (w0.getD (nbrWire e 0) false || w0.getD (nbrWire e (stepVal e.2.2)) false) = v0 := by
    rw [hn0, hn1]; simp [v0]
  rw [hv0]
  have ha1 : (w0 ++ [v0]).getD (nbrWire e (3 * stepVal e.2.2)) false =
      w0.getD (nbrWire e (3 * stepVal e.2.2)) false := getD_append_lt w0 [v0] false _ (hsub1 _)
  have ha2 : (w0 ++ [v0]).getD (nbrWire e (9 * stepVal e.2.2)) false =
      w0.getD (nbrWire e (9 * stepVal e.2.2)) false := getD_append_lt w0 [v0] false _ (hsub1 _)
  rw [ha1, ha2]
  have hv1 : (w0.getD (nbrWire e (3 * stepVal e.2.2)) false ||
      w0.getD (nbrWire e (9 * stepVal e.2.2)) false) = v1 := by
    rw [hn2, hn3]; simp [v1]
  rw [hv1]
  have hb26 : (w0 ++ [v0, v1]).getD 26 false = v0 := by
    rw [getD_append_ge w0 [v0, v1] false 26 (by omega), hlen]; rfl
  have hb27 : (w0 ++ [v0, v1]).getD 27 false = v1 := by
    rw [getD_append_ge w0 [v0, v1] false 27 (by omega), hlen]; rfl
  rw [hb26, hb27]
  have hc3 : (w0 ++ [v0, v1, v0 || v1]).getD (ctrWire e) false = w0.getD (ctrWire e) false :=
    getD_append_lt w0 [v0, v1, v0 || v1] false _ hsubC
  have hb28 : (w0 ++ [v0, v1, v0 || v1]).getD 28 false = (v0 || v1) := by
    rw [getD_append_ge w0 [v0, v1, v0 || v1] false 28 (by omega), hlen]; rfl
  rw [hc3, hb28, hc, item_or_eq]

private theorem blockStep_eval (e : Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13))
    (w : List Bool) (b : ℕ) (hlen : w.length = b) (hb : 26 ≤ b)
    (hw : ∀ j < 26, w.getD j false = (inVec x5 x6).getD j false) :
    let v0 := Decidable.decide (nbrProp e x5 x6 0 ∨ nbrProp e x5 x6 (stepVal e.2.2))
    let v1 := Decidable.decide (nbrProp e x5 x6 (3 * stepVal e.2.2) ∨ nbrProp e x5 x6 (9 * stepVal e.2.2))
    (blockStep e b).foldl stepGate w =
      w ++ [v0, v1, v0 || v1, Decidable.decide (itemProp e x5 x6),
            w.getD (b - 1) false || Decidable.decide (itemProp e x5 x6)] := by
  intro v0 v1
  have h0 : (blockStep e b).foldl stepGate w =
      stepGate (stepGate (stepGate (stepGate (stepGate w
        ⟨.or, [nbrWire e 0, nbrWire e (stepVal e.2.2)]⟩)
        ⟨.or, [nbrWire e (3 * stepVal e.2.2), nbrWire e (9 * stepVal e.2.2)]⟩)
        ⟨.or, [b, b + 1]⟩)
        ⟨.and, [ctrWire e, b + 2]⟩)
        ⟨.or, [b - 1, b + 3]⟩ := rfl
  rw [h0]
  simp only [stepGate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true, List.append_assoc,
    List.cons_append, List.nil_append]
  have hn0 := nbr_getD e x5 x6 w hw 0
  have hn1 := nbr_getD e x5 x6 w hw (stepVal e.2.2)
  have hn2 := nbr_getD e x5 x6 w hw (3 * stepVal e.2.2)
  have hn3 := nbr_getD e x5 x6 w hw (9 * stepVal e.2.2)
  have hc := ctr_getD e x5 x6 w hw
  have hsub1 : ∀ d : Fin 13, nbrWire e d < w.length := by
    intro d; rw [hlen]; unfold nbrWire; split_ifs <;> omega
  have hsubC : ctrWire e < w.length := by
    rw [hlen]; unfold ctrWire; split_ifs <;> omega
  have hv0 : (w.getD (nbrWire e 0) false || w.getD (nbrWire e (stepVal e.2.2)) false) = v0 := by
    rw [hn0, hn1]; simp [v0]
  rw [hv0]
  have ha1 : (w ++ [v0]).getD (nbrWire e (3 * stepVal e.2.2)) false =
      w.getD (nbrWire e (3 * stepVal e.2.2)) false := getD_append_lt w [v0] false _ (hsub1 _)
  have ha2 : (w ++ [v0]).getD (nbrWire e (9 * stepVal e.2.2)) false =
      w.getD (nbrWire e (9 * stepVal e.2.2)) false := getD_append_lt w [v0] false _ (hsub1 _)
  rw [ha1, ha2]
  have hv1 : (w.getD (nbrWire e (3 * stepVal e.2.2)) false ||
      w.getD (nbrWire e (9 * stepVal e.2.2)) false) = v1 := by
    rw [hn2, hn3]; simp [v1]
  rw [hv1]
  have hbb0 : (w ++ [v0, v1]).getD b false = v0 := by
    rw [getD_append_ge w [v0, v1] false b (by omega), hlen, Nat.sub_self]; rfl
  have hbb1 : (w ++ [v0, v1]).getD (b + 1) false = v1 := by
    rw [getD_append_ge w [v0, v1] false (b + 1) (by omega), hlen, Nat.add_sub_cancel_left]; rfl
  rw [hbb0, hbb1]
  have hc3 : (w ++ [v0, v1, v0 || v1]).getD (ctrWire e) false = w.getD (ctrWire e) false :=
    getD_append_lt w [v0, v1, v0 || v1] false _ hsubC
  have hbb2 : (w ++ [v0, v1, v0 || v1]).getD (b + 2) false = (v0 || v1) := by
    rw [getD_append_ge w [v0, v1, v0 || v1] false (b + 2) (by omega), hlen, Nat.add_sub_cancel_left]
    rfl
  rw [hc3, hbb2, hc, item_or_eq]
  have hprev : (w ++ [v0, v1, v0 || v1, Decidable.decide (itemProp e x5 x6)]).getD (b - 1) false =
      w.getD (b - 1) false := getD_append_lt w _ false (b - 1) (by omega)
  have hbb3 : (w ++ [v0, v1, v0 || v1, Decidable.decide (itemProp e x5 x6)]).getD (b + 3) false =
      Decidable.decide (itemProp e x5 x6) := by
    rw [getD_append_ge w _ false (b + 3) (by omega), hlen, Nat.add_sub_cancel_left]; rfl
  rw [hprev, hbb3]

private theorem prefix_inv (cfg : Fin 9 → Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13))
    (m : ℕ) (h1 : 1 ≤ m) (h9 : m ≤ 9) :
    let w := (prefixGates cfg m).foldl stepGate (inVec x5 x6)
    w.length = 26 + (5 * m - 1) ∧
    (∀ j < 26, w.getD j false = (inVec x5 x6).getD j false) ∧
    (∀ i : Fin 9, i.val < m →
      let x10 := 26 + (5 * i.val - 1)
      let e := cfg i
      let s := stepVal e.2.2
      w.getD x10 false = Decidable.decide (nbrProp e x5 x6 0 ∨ nbrProp e x5 x6 s) ∧
      w.getD (x10 + 1) false = Decidable.decide (nbrProp e x5 x6 (3 * s) ∨ nbrProp e x5 x6 (9 * s)) ∧
      w.getD (x10 + 2) false = (w.getD x10 false || w.getD (x10 + 1) false)) ∧
    w.getD (26 + (5 * m - 1) - 1) false =
      Decidable.decide (∃ i : Fin 9, i.val < m ∧ itemProp (cfg i) x5 x6) := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      dsimp only
      have hev := block0_eval (cfg 0) x5 x6
      dsimp only at hev
      have hpg1 : prefixGates cfg (0 + 1) = block0 (cfg 0) := rfl
      rw [hpg1, hev]
      have hlen0 := inVec_len x5 x6
      refine ⟨by simp [hlen0], ?_, ?_, ?_⟩
      · intro j hj
        exact getD_append_lt _ _ false j (by omega)
      · intro i hi
        have hi0 : i = 0 := Fin.ext (by omega)
        subst hi0
        refine ⟨?_, ?_, ?_⟩
        · rw [show 26 + (5 * (0 : Fin 9).val - 1) = 26 by rfl]
          rw [getD_append_ge _ _ false 26 (by omega), hlen0]; rfl
        · rw [show 26 + (5 * (0 : Fin 9).val - 1) + 1 = 27 by rfl]
          rw [getD_append_ge _ _ false 27 (by omega), hlen0]; rfl
        · rw [show 26 + (5 * (0 : Fin 9).val - 1) = 26 by rfl]
          rw [getD_append_ge _ _ false 26 (by omega), getD_append_ge _ _ false 27 (by omega),
            getD_append_ge _ _ false 28 (by omega), hlen0]; rfl
      · rw [show 26 + (5 * 1 - 1) - 1 = 29 by omega]
        rw [getD_append_ge _ _ false 29 (by omega), hlen0]
        change Decidable.decide (itemProp (cfg 0) x5 x6) = _
        apply decide_eq_decide.mpr
        constructor
        · intro h; exact ⟨0, by omega, h⟩
        · rintro ⟨i, hi, hp⟩
          have hi0 : i = 0 := Fin.ext (by omega)
          exact hi0 ▸ hp
    | succ k =>
      have hlt : k + 1 < 9 := by omega
      obtain ⟨ihLen, ihIn, ihBlocks, ihAcc⟩ := ih (by omega) (by omega)
      let wPrev := (prefixGates cfg (k + 1)).foldl stepGate (inVec x5 x6)
      let b := 26 + (5 * (k + 1) - 1)
      let idx : Fin 9 := ⟨k + 1, hlt⟩
      have hfold : (prefixGates cfg (k + 2)).foldl stepGate (inVec x5 x6) =
          (blockStep (cfg idx) b).foldl stepGate wPrev := by
        simp only [prefixGates, hlt, ↓reduceDIte, List.foldl_append, wPrev, b, idx]
      have hev := blockStep_eval (cfg idx) x5 x6 wPrev b ihLen (by omega) ihIn
      dsimp only at hev ⊢
      rw [hfold, hev]
      let v0 := Decidable.decide (nbrProp (cfg idx) x5 x6 0 ∨ nbrProp (cfg idx) x5 x6 (stepVal (cfg idx).2.2))
      let v1 := Decidable.decide (nbrProp (cfg idx) x5 x6 (3 * stepVal (cfg idx).2.2) ∨ nbrProp (cfg idx) x5 x6 (9 * stepVal (cfg idx).2.2))
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        rw [ihLen]
        omega
      · intro j hj
        rw [getD_append_lt _ _ false j (by rw [ihLen]; omega)]
        exact ihIn j hj
      · intro i hi
        by_cases hilt : i.val < k + 1
        · have hx10 : 26 + (5 * i.val - 1) + 2 < b := by
            dsimp only [b]; omega
          rw [getD_append_lt _ _ false (26 + (5 * i.val - 1)) (by rw [ihLen]; omega)]
          rw [getD_append_lt _ _ false (26 + (5 * i.val - 1) + 1) (by rw [ihLen]; omega)]
          rw [getD_append_lt _ _ false (26 + (5 * i.val - 1) + 2) (by rw [ihLen]; omega)]
          exact ihBlocks i hilt
        · have hieq : i = idx := Fin.ext (by dsimp only [idx]; omega)
          subst hieq
          have hb0 : wPrev.length ≤ b := by rw [ihLen]
          have hb1 : wPrev.length ≤ b + 1 := by rw [ihLen]; omega
          have hb2 : wPrev.length ≤ b + 2 := by rw [ihLen]; omega
          refine ⟨?_, ?_, ?_⟩
          · rw [getD_append_ge _ _ false b hb0, ihLen, Nat.sub_self]; rfl
          · rw [getD_append_ge _ _ false (b + 1) hb1, ihLen, Nat.add_sub_cancel_left]; rfl
          · rw [getD_append_ge _ _ false b hb0, getD_append_ge _ _ false (b + 1) hb1,
              getD_append_ge _ _ false (b + 2) hb2, ihLen, Nat.sub_self,
              Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]; rfl
      · have hpos : 26 + (5 * (k + 2) - 1) - 1 = b + 4 := by dsimp only [b]; omega
        rw [hpos]
        rw [getD_append_ge _ _ false (b + 4) (by rw [ihLen]; omega), ihLen, Nat.add_sub_cancel_left]
        change (wPrev.getD (b - 1) false || Decidable.decide (itemProp (cfg idx) x5 x6)) = _
        rw [ihAcc]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨i, hi, hp⟩ | hp)
          · exact ⟨i, by omega, hp⟩
          · exact ⟨idx, by dsimp only [idx]; omega, hp⟩
        · rintro ⟨i, hi, hp⟩
          by_cases hilt : i.val < k + 1
          · exact Or.inl ⟨i, hilt, hp⟩
          · have hieq : i = idx := Fin.ext (by dsimp only [idx]; omega)
            exact Or.inr (hieq ▸ hp)

private theorem itemProp_iff (cfg : Fin 9 → Bool × Fin 13 × Fin 3) (x5 x6 : Finset (Fin 13)) :
    (∃ i : Fin 9, itemProp (cfg i) x5 x6) ↔
    (∃ x8 ∈ x5, ∃ x9 ∈ x6, x8 - x9 ∈ diffSet ∧
      ∃ i : Fin 9, if (cfg i).1 = true then (cfg i).2.1 = x9 else (cfg i).2.1 = x8) := by
  constructor
  · rintro ⟨i, hc, d, hd, hn⟩
    cases h1 : (cfg i).1
    · simp only [ctrProp, nbrProp, h1, Bool.false_eq_true, ↓reduceIte] at hc hn
      refine ⟨(cfg i).2.1, hc, (cfg i).2.1 - d, hn, ?_, i, by simp [h1]⟩
      simpa only [sub_sub_cancel] using hd
    · simp only [ctrProp, nbrProp, h1, ↓reduceIte] at hc hn
      refine ⟨(cfg i).2.1 + d, hn, (cfg i).2.1, hc, ?_, i, by simp [h1]⟩
      simpa only [add_sub_cancel_left] using hd
  · rintro ⟨x8, hx8, x9, hx9, hdiff, i, hmatch⟩
    refine ⟨i, ?_, x8 - x9, hdiff, ?_⟩
    · cases h1 : (cfg i).1
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmatch
        simp only [ctrProp, h1, Bool.false_eq_true, ↓reduceIte, hmatch]; exact hx8
      · simp only [h1, ↓reduceIte] at hmatch
        simp only [ctrProp, h1, ↓reduceIte, hmatch]; exact hx9
    · cases h1 : (cfg i).1
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmatch
        simp only [nbrProp, h1, Bool.false_eq_true, ↓reduceIte, hmatch, sub_sub_cancel]; exact hx9
      · simp only [h1, ↓reduceIte] at hmatch
        simp only [nbrProp, h1, ↓reduceIte, hmatch, add_sub_cancel]; exact hx8

private theorem main_proof (cfg : Fin 9 → Bool × Fin 13 × Fin 3) :
    ∃ (C : Circuit),
      PEqualNP.MetaComplexity.Monotone2 C ∧
      C.size = 44 ∧
      C.output < 70 ∧
      ∀ (x5 x6 : Finset (Fin 13)),
        let x7 := inVec x5 x6
        ((C.wires x7).length = 70 ∧
         (∀ (x6_1 : Fin 13),
           (C.wires x7).getD x6_1.val false = Decidable.decide (x6_1 ∈ x5) ∧
           (C.wires x7).getD (13 + x6_1.val) false = Decidable.decide (x6_1 ∈ x6)) ∧
         ∀ (i : Fin 9),
           let x10 := 26 + (5 * i.val - 1)
           let s := stepVal (cfg i).2.2
           (C.wires x7).getD x10 false = Decidable.decide (nbrProp (cfg i) x5 x6 0 ∨ nbrProp (cfg i) x5 x6 s) ∧
           (C.wires x7).getD (x10 + 1) false = Decidable.decide (nbrProp (cfg i) x5 x6 (3 * s) ∨ nbrProp (cfg i) x5 x6 (9 * s)) ∧
           (C.wires x7).getD (x10 + 2) false = ((C.wires x7).getD x10 false || (C.wires x7).getD (x10 + 1) false)) ∧
        C.eval x7 = Decidable.decide (∃ x8 ∈ x5, ∃ x9 ∈ x6, x8 - x9 ∈ diffSet ∧
          ∃ (i : Fin 9), if (cfg i).1 = true then (cfg i).2.1 = x9 else (cfg i).2.1 = x8) := by
  refine ⟨mkCircuit cfg, prefixGates_mono cfg 9, prefixGates_len cfg 9 (by omega) (by omega),
    by change 69 < 70; omega, ?_⟩
  intro x5 x6
  obtain ⟨hLen, hIn, hBlocks, hAcc⟩ := prefix_inv cfg x5 x6 9 (by omega) (by omega)
  refine ⟨⟨hLen, ?_, fun i => hBlocks i i.isLt⟩, ?_⟩
  · intro a
    exact ⟨by change ((prefixGates cfg 9).foldl stepGate (inVec x5 x6)).getD a.val false = _;
              rw [hIn a.val (by omega), inVec_getD_left],
           by change ((prefixGates cfg 9).foldl stepGate (inVec x5 x6)).getD (13 + a.val) false = _;
              rw [hIn (13 + a.val) (by omega), inVec_getD_right]⟩
  · change ((prefixGates cfg 9).foldl stepGate (inVec x5 x6)).getD 69 false = _
    rw [show (69 : ℕ) = 26 + (5 * 9 - 1) - 1 by omega, hAcc]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨i, _, hp⟩
      exact (itemProp_iff cfg x5 x6).mp ⟨i, hp⟩
    · intro h
      obtain ⟨i, hp⟩ := (itemProp_iff cfg x5 x6).mpr h
      exact ⟨i, i.isLt, hp⟩

end PEqualNP.Outside.L_meta_4089

theorem PEqualNP.Outside.L_meta_4089 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool → Prop := fun (x2 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : List Bool) =>   x5.length = (70 : ℕ) ∧     (∀ (x6 : Fin (13 : ℕ)), x5.getD (↑x6) Bool.false = Decidable.decide (x6 ∈ x3) ∧ x5.getD ((13 : ℕ) + ↑x6) Bool.false = Decidable.decide (x6 ∈ x4)) ∧       ∀ (x6 : Fin (9 : ℕ)),         have x7 : Fin (13 : ℕ) := (x2 x6).2.1;         have x8 : Fin (13 : ℕ) := if (x2 x6).2.2 = (0 : Fin (3 : ℕ)) then (1 : Fin (13 : ℕ)) else if (x2 x6).2.2 = (1 : Fin (3 : ℕ)) then (3 : Fin (13 : ℕ)) else (9 : Fin (13 : ℕ));         let x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => if (x2 x6).1 = Bool.true then x7 + x9 ∈ x3 else x7 - x9 ∈ x4;         have x10 : ℕ := (26 : ℕ) + ((5 : ℕ) * ↑x6 - (1 : ℕ));         x5.getD x10 Bool.false = Decidable.decide (x9 (0 : Fin (13 : ℕ)) ∨ x9 x8) ∧ x5.getD (x10 + (1 : ℕ)) Bool.false = Decidable.decide (x9 ((3 : Fin (13 : ℕ)) * x8) ∨ x9 ((9 : Fin (13 : ℕ)) * x8)) ∧ x5.getD (x10 + (2 : ℕ)) Bool.false = (x5.getD x10 Bool.false || x5.getD (x10 + (1 : ℕ)) Bool.false); ∀ (x3 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)),   ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.Monotone2 x4 ∧       x4.size = (44 : ℕ) ∧         x4.output < (70 : ℕ) ∧           ∀ (x5 x6 : Finset (Fin (13 : ℕ))),             have x7 : List Bool := List.ofFn fun (x7 : Fin (26 : ℕ)) => Decidable.decide ((∃ x8 ∈ x5, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ x8 ∈ x6, x7 = Fin.natAdd (13 : ℕ) x8);             x2 x3 x5 x6 (x4.wires x7) ∧ x4.eval x7 = Decidable.decide (∃ x8 ∈ x5, ∃ x9 ∈ x6, x8 - x9 ∈ x1 ∧ ∃ (x10 : Fin (9 : ℕ)), if (x3 x10).1 = Bool.true then (x3 x10).2.1 = x9 else (x3 x10).2.1 = x8) :=
  PEqualNP.Outside.L_meta_4089.main_proof
