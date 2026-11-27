import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6392_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepWire]; omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private def W (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

private lemma W_input (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26) :
    W C (List.ofFn x) w = x ⟨w, hw⟩ := by
  unfold W
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) w (by simp [hw])]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp [hw]), Option.getD_some, List.getElem_ofFn]

private lemma W_gate (C : Circuit) (hrb : ReadsBack 26 C) (x : List Bool) (hx : x.length = 26)
    (k : ℕ) (hk : k < C.gates.length) :
    W C x (26 + k) = C.gates[k].op.eval (C.gates[k].inputs.map (W C x)) := by
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set w0 := (C.gates.take k).foldl stepWire x with hw0
  have hw0_len : w0.length = 26 + k := by
    simp [w0, foldl_stepWire_length, hx, List.length_take]; omega
  have hW : W C x (26 + k) = C.gates[k].op.eval (C.gates[k].inputs.map fun i => w0.getD i false) := by
    unfold W
    conv_lhs => rw [wires_eq_foldl, hsplit, List.foldl_append, List.foldl_cons, ← hw0]
    rw [foldl_stepWire_getD_lt _ _ (26 + k) (by simp [stepWire, hw0_len])]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hW]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hilt : i < 26 + k := hrb k hk i (by simp [gateAt, List.getD_eq_getElem?_getD, hk, hi])
  unfold W
  conv_rhs => rw [wires_eq_foldl, hsplit, List.foldl_append]
  exact (foldl_stepWire_getD_lt _ w0 i (by omega)).symm

private def starBlock (t : ℕ) : List Gate :=
  [ ⟨GateOp.or, [t, (t + 1) % 13]⟩,
    ⟨GateOp.or, [(t + 3) % 13, (t + 9) % 13]⟩,
    ⟨GateOp.or, [26 + 4 * t, 26 + 4 * t + 1]⟩,
    ⟨GateOp.and, [13 + t, 26 + 4 * t + 2]⟩ ]

private def starGates : List Gate :=
  (List.range 13).flatMap starBlock

private def orChain : List Gate :=
  ⟨GateOp.or, [29, 33]⟩ ::
    (List.range 11).map fun k => ⟨GateOp.or, [78 + k, 37 + 4 * k]⟩

private def Cstar : Circuit :=
  ⟨starGates ++ orChain, 89⟩

private lemma Cstar_size : Cstar.size = 64 := by decide

private lemma Cstar_isAO2 : IsAO2 26 Cstar := by decide

private def starVal (x : Fin 26 → Bool) (t : Fin 13) : Bool :=
  x (Fin.natAdd 13 t) &&
    ((x (Fin.castAdd 13 t) || x (Fin.castAdd 13 (t + 1))) ||
      (x (Fin.castAdd 13 (t + 3)) || x (Fin.castAdd 13 (t + 9))))

private lemma Cstar_gate_star (t : Fin 13) :
    Cstar.gates[4 * t.val]'(by have := t.isLt; change 4 * t.val < Cstar.size; rw [Cstar_size]; omega) =
      ⟨GateOp.or, [t.val, (t.val + 1) % 13]⟩ ∧
    Cstar.gates[4 * t.val + 1]'(by have := t.isLt; change 4 * t.val + 1 < Cstar.size; rw [Cstar_size]; omega) =
      ⟨GateOp.or, [(t.val + 3) % 13, (t.val + 9) % 13]⟩ ∧
    Cstar.gates[4 * t.val + 2]'(by have := t.isLt; change 4 * t.val + 2 < Cstar.size; rw [Cstar_size]; omega) =
      ⟨GateOp.or, [26 + 4 * t.val, 26 + 4 * t.val + 1]⟩ ∧
    Cstar.gates[4 * t.val + 3]'(by have := t.isLt; change 4 * t.val + 3 < Cstar.size; rw [Cstar_size]; omega) =
      ⟨GateOp.and, [13 + t.val, 26 + 4 * t.val + 2]⟩ := by
  fin_cases t <;> exact ⟨rfl, rfl, rfl, rfl⟩

private lemma Cstar_gate_or0 :
    Cstar.gates[52]'(by change 52 < Cstar.size; rw [Cstar_size]; omega) = ⟨GateOp.or, [29, 33]⟩ := rfl

private lemma Cstar_gate_orS (k : Fin 11) :
    Cstar.gates[53 + k.val]'(by have := k.isLt; change 53 + k.val < Cstar.size; rw [Cstar_size]; omega) =
      ⟨GateOp.or, [78 + k.val, 37 + 4 * k.val]⟩ := by
  fin_cases k <;> rfl

private lemma W_Cstar_star (x : Fin 26 → Bool) (t : Fin 13) :
    W Cstar (List.ofFn x) (29 + 4 * t.val) = starVal x t := by
  have hrb : ReadsBack 26 Cstar := Cstar_isAO2.2.1
  have hx : (List.ofFn x).length = 26 := by simp
  have ht := t.isLt
  obtain ⟨hg0, hg1, hg2, hg3⟩ := Cstar_gate_star t
  have h0 : W Cstar (List.ofFn x) (26 + 4 * t.val) =
      (x (Fin.castAdd 13 t) || x (Fin.castAdd 13 (t + 1))) := by
    rw [W_gate Cstar hrb (List.ofFn x) hx (4 * t.val) (by change 4 * t.val < Cstar.size; rw [Cstar_size]; omega), hg0]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [W_input Cstar x t.val (by omega), W_input Cstar x ((t.val + 1) % 13) (by omega)]
    rfl
  have h1 : W Cstar (List.ofFn x) (26 + 4 * t.val + 1) =
      (x (Fin.castAdd 13 (t + 3)) || x (Fin.castAdd 13 (t + 9))) := by
    rw [show 26 + 4 * t.val + 1 = 26 + (4 * t.val + 1) by omega]
    rw [W_gate Cstar hrb (List.ofFn x) hx (4 * t.val + 1) (by change 4 * t.val + 1 < Cstar.size; rw [Cstar_size]; omega), hg1]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [W_input Cstar x ((t.val + 3) % 13) (by omega), W_input Cstar x ((t.val + 9) % 13) (by omega)]
    rfl
  have h2 : W Cstar (List.ofFn x) (26 + 4 * t.val + 2) =
      ((x (Fin.castAdd 13 t) || x (Fin.castAdd 13 (t + 1))) ||
        (x (Fin.castAdd 13 (t + 3)) || x (Fin.castAdd 13 (t + 9)))) := by
    rw [show 26 + 4 * t.val + 2 = 26 + (4 * t.val + 2) by omega]
    rw [W_gate Cstar hrb (List.ofFn x) hx (4 * t.val + 2) (by change 4 * t.val + 2 < Cstar.size; rw [Cstar_size]; omega), hg2]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [h0, h1]
  rw [show 29 + 4 * t.val = 26 + (4 * t.val + 3) by omega]
  rw [W_gate Cstar hrb (List.ofFn x) hx (4 * t.val + 3) (by change 4 * t.val + 3 < Cstar.size; rw [Cstar_size]; omega), hg3]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq]
  rw [W_input Cstar x (13 + t.val) (by omega), h2]
  rfl

private lemma W_Cstar_chain (x : Fin 26 → Bool) :
    ∀ m, m < 12 →
      (W Cstar (List.ofFn x) (78 + m) = true ↔ ∃ t : Fin 13, t.val ≤ m + 1 ∧ starVal x t = true) := by
  have hrb : ReadsBack 26 Cstar := Cstar_isAO2.2.1
  have hx : (List.ofFn x).length = 26 := by simp
  intro m
  induction m with
  | zero =>
    intro _
    rw [show 78 + 0 = 26 + 52 by omega]
    rw [W_gate Cstar hrb (List.ofFn x) hx 52 (by change 52 < Cstar.size; rw [Cstar_size]; omega), Cstar_gate_or0]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, id_eq]
    have hs0 : W Cstar (List.ofFn x) 29 = starVal x 0 := by simpa using W_Cstar_star x 0
    have hs1 : W Cstar (List.ofFn x) 33 = starVal x 1 := by simpa using W_Cstar_star x 1
    rw [hs0, hs1]
    constructor
    · rintro (h | h)
      · exact ⟨0, by decide, h⟩
      · exact ⟨1, by decide, h⟩
    · rintro ⟨t, ht, hst⟩
      have : t = 0 ∨ t = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h0 | h1
        · left; ext; exact h0
        · right; ext; exact h1
      rcases this with rfl | rfl
      · exact Or.inl hst
      · exact Or.inr hst
  | succ m ih =>
    intro hm
    have hm11 : m < 11 := by omega
    rw [show 78 + (m + 1) = 26 + (53 + m) by omega]
    rw [W_gate Cstar hrb (List.ofFn x) hx (53 + m) (by change 53 + m < Cstar.size; rw [Cstar_size]; omega),
        Cstar_gate_orS ⟨m, hm11⟩]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, id_eq]
    have hst : W Cstar (List.ofFn x) (37 + 4 * m) = starVal x ⟨m + 2, by omega⟩ := by
      have := W_Cstar_star x ⟨m + 2, by omega⟩
      simpa [show 29 + 4 * (m + 2) = 37 + 4 * m by omega] using this
    rw [ih (by omega), hst]
    constructor
    · rintro (⟨t, ht, h⟩ | h)
      · exact ⟨t, by omega, h⟩
      · exact ⟨⟨m + 2, by omega⟩, by simp, h⟩
    · rintro ⟨t, ht, h⟩
      by_cases hlt : t.val ≤ m + 1
      · exact Or.inl ⟨t, hlt, h⟩
      · right
        have heq : t = ⟨m + 2, by omega⟩ := by ext; simp; omega
        rwa [← heq]

private lemma Cstar_eval_eq (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hG : ∀ (u v : Fin 26), G.Adj u v ↔
      ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        (u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∨
          v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) :
    circuitFun 26 Cstar = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  have h1 : circuitFun 26 Cstar x = true ↔ ∃ t : Fin 13, starVal x t = true := by
    change W Cstar (List.ofFn x) 89 = true ↔ _
    rw [show (89 : ℕ) = 78 + 11 by rfl, W_Cstar_chain x 11 (by omega)]
    constructor
    · rintro ⟨t, _, ht⟩; exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩; exact ⟨t, by have := t.isLt; omega, ht⟩
  rw [h1]
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht⟩
    simp only [starVal, Bool.and_eq_true, Bool.or_eq_true] at ht
    rcases ht with ⟨hyt, (hp | hp) | (hp | hp)⟩
    · exact ⟨Fin.castAdd 13 t, Fin.natAdd 13 t, (hG _ _).mpr ⟨t, t, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩, hp, hyt⟩
    · exact ⟨Fin.castAdd 13 (t + 1), Fin.natAdd 13 t, (hG _ _).mpr ⟨t + 1, t, Or.inr (Or.inl rfl), Or.inl ⟨rfl, rfl⟩⟩, hp, hyt⟩
    · exact ⟨Fin.castAdd 13 (t + 3), Fin.natAdd 13 t, (hG _ _).mpr ⟨t + 3, t, Or.inr (Or.inr (Or.inl rfl)), Or.inl ⟨rfl, rfl⟩⟩, hp, hyt⟩
    · exact ⟨Fin.castAdd 13 (t + 9), Fin.natAdd 13 t, (hG _ _).mpr ⟨t + 9, t, Or.inr (Or.inr (Or.inr rfl)), Or.inl ⟨rfl, rfl⟩⟩, hp, hyt⟩
  · rintro ⟨u, v, huv, hxu, hxv⟩
    obtain ⟨p, l, hinc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hG u v).mp huv
    · refine ⟨l, ?_⟩
      simp only [starVal, Bool.and_eq_true, Bool.or_eq_true, hxv, true_and]
      rcases hinc with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxu)
      · exact Or.inl (Or.inr hxu)
      · exact Or.inr (Or.inl hxu)
      · exact Or.inr (Or.inr hxu)
    · refine ⟨l, ?_⟩
      simp only [starVal, Bool.and_eq_true, Bool.or_eq_true, hxu, true_and]
      rcases hinc with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxv)
      · exact Or.inl (Or.inr hxv)
      · exact Or.inr (Or.inl hxv)
      · exact Or.inr (Or.inr hxv)

private lemma main (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit)
    (hG : ∀ (u v : Fin 26), G.Adj u v ↔
      ∃ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        (u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∨
          v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l))
    (hleast : IsLeastAO G C) :
    C.size ≤ 64 := by
  have hle := hleast.2.2 Cstar Cstar_isAO2 (Cstar_eval_eq G hG)
  rw [Cstar_size] at hle
  exact hle

end PEqualNP.Outside.L_meta_6392_aux

theorem PEqualNP.Outside.L_meta_6392 :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → x3.size ≤ (64 : ℕ) :=
  PEqualNP.Outside.L_meta_6392_aux.main
