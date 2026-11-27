import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18849_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ixList : List (Fin 26) :=
  [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

def remapWire (w : ℕ) : ℕ :=
  if w < 21 then (ixList.getD w 0).val else w + 5

def remapGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map remapWire⟩

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]; omega

theorem getD_append_lt (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega), List.getElem_append_left hi,
      List.getD_eq_getElem _ _ hi]

theorem getD_snoc (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

theorem foldl_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [wstep]; omega)]
    exact getD_append_lt w _ i hi

theorem remapWire_lt (k w : ℕ) (hw : w < 21 + k) : remapWire w < 26 + k := by
  unfold remapWire
  split
  · have := (ixList.getD w 0).isLt; omega
  · omega

theorem foldl_remap (gs : List Gate) (x : Fin 26 → Bool) :
    ∀ w : ℕ, ((gs.map remapGate).foldl wstep (List.ofFn x)).getD (remapWire w) false =
      (gs.foldl wstep (ixList.map x)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil, List.foldl_nil]
    unfold remapWire
    split
    · rename_i hw
      have hlen1 : (List.ofFn x).length = 26 := List.length_ofFn
      have hix_len : ixList.length = 21 := rfl
      have hw_ix : w < ixList.length := by rw [hix_len]; exact hw
      have hw_map : w < (ixList.map x).length := by rw [List.length_map]; exact hw_ix
      rw [List.getD_eq_getElem _ _ (by rw [hlen1]; exact (ixList.getD w 0).isLt),
          List.getElem_ofFn,
          List.getD_eq_getElem _ _ hw_map,
          List.getElem_map,
          List.getD_eq_getElem _ _ hw_ix]
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp [ixList]; omega)]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl1 : ((gs.map remapGate).foldl wstep (List.ofFn x)).length = 26 + gs.length := by
      rw [foldl_len, List.length_ofFn, List.length_map]
    have hl2 : (gs.foldl wstep (ixList.map x)).length = 21 + gs.length := by
      rw [foldl_len]; simp [ixList]
    have hval : (remapGate g).op.eval ((remapGate g).inputs.map fun i =>
        ((gs.map remapGate).foldl wstep (List.ofFn x)).getD i false) =
        g.op.eval (g.inputs.map fun i => (gs.foldl wstep (ixList.map x)).getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih i
    by_cases hw : w < 21 + gs.length
    · have hrw : remapWire w < 26 + gs.length := remapWire_lt gs.length w hw
      rw [wstep, wstep, getD_append_lt _ _ _ (by omega), getD_append_lt _ _ _ (by omega)]
      exact ih w
    · by_cases heq : w = 21 + gs.length
      · subst heq
        have hrw : remapWire (21 + gs.length) = 26 + gs.length := by
          unfold remapWire; rw [ite_eq_right (by omega)]; omega
        rw [wstep, wstep, hrw, ← hl1, getD_snoc, ← hl2, getD_snoc, hval]
      · have hrw : remapWire w = w + 5 := by
          unfold remapWire; rw [ite_eq_right (by omega)]
        rw [wstep, wstep, hrw,
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl1]; omega),
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hl2]; omega)]

def extraGates (m : ℕ) : List Gate :=
  [ ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [16, 22]⟩,
    ⟨GateOp.or, [m + 0, m + 1]⟩,
    ⟨GateOp.and, [0, m + 2]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [21, 25]⟩,
    ⟨GateOp.or, [m + 4, m + 5]⟩,
    ⟨GateOp.and, [1, m + 6]⟩,
    ⟨GateOp.or, [13, 19]⟩,
    ⟨GateOp.or, [23, 24]⟩,
    ⟨GateOp.or, [m + 8, m + 9]⟩,
    ⟨GateOp.and, [3, m + 10]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.or, [m + 12, m + 13]⟩,
    ⟨GateOp.and, [9, m + 14]⟩,
    ⟨GateOp.or, [m + 3, m + 7]⟩,
    ⟨GateOp.or, [m + 11, m + 15]⟩,
    ⟨GateOp.or, [m + 16, m + 17]⟩ ]

theorem step_or (w : List Bool) (a b : ℕ) :
    wstep w ⟨GateOp.or, [a, b]⟩ = w ++ [w.getD a false || w.getD b false] := by
  simp [wstep, GateOp.eval]

theorem step_and (w : List Bool) (a b : ℕ) :
    wstep w ⟨GateOp.and, [a, b]⟩ = w ++ [w.getD a false && w.getD b false] := by
  simp [wstep, GateOp.eval]

theorem getD_append_add (w tail : List Bool) (k : ℕ) :
    (w ++ tail).getD (w.length + k) false = tail.getD k false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

theorem extra_eval (w : List Bool) (hw : 26 ≤ w.length) :
    ((extraGates w.length).foldl wstep w).getD (w.length + 18) false =
      (((w.getD 0 false && ((w.getD 13 false || w.getD 14 false) || (w.getD 16 false || w.getD 22 false))) ||
        (w.getD 1 false && ((w.getD 13 false || w.getD 15 false) || (w.getD 21 false || w.getD 25 false)))) ||
       ((w.getD 3 false && ((w.getD 13 false || w.getD 19 false) || (w.getD 23 false || w.getD 24 false))) ||
        (w.getD 9 false && ((w.getD 13 false || w.getD 17 false) || (w.getD 18 false || w.getD 20 false))))) := by
  set m := w.length
  let g0 := w.getD 13 false || w.getD 14 false
  let g1 := w.getD 16 false || w.getD 22 false
  let g2 := g0 || g1
  let g3 := w.getD 0 false && g2
  let g4 := w.getD 13 false || w.getD 15 false
  let g5 := w.getD 21 false || w.getD 25 false
  let g6 := g4 || g5
  let g7 := w.getD 1 false && g6
  let g8 := w.getD 13 false || w.getD 19 false
  let g9 := w.getD 23 false || w.getD 24 false
  let g10 := g8 || g9
  let g11 := w.getD 3 false && g10
  let g12 := w.getD 13 false || w.getD 17 false
  let g13 := w.getD 18 false || w.getD 20 false
  let g14 := g12 || g13
  let g15 := w.getD 9 false && g14
  let g16 := g3 || g7
  let g17 := g11 || g15
  let g18 := g16 || g17
  have hfold : (extraGates m).foldl wstep w =
      w ++ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18] := by
    have gl : ∀ (t : List Bool) (i : ℕ), i < m → (w ++ t).getD i false = w.getD i false :=
      fun t i hi => getD_append_lt w t i hi
    have gr : ∀ (t : List Bool) (k : ℕ), (w ++ t).getD (m + k) false = t.getD k false :=
      fun t k => getD_append_add w t k
    unfold extraGates
    simp only [List.foldl_cons, List.foldl_nil, step_or, step_and, List.append_assoc,
      List.cons_append, List.nil_append, gl _ _ (by omega : 0 < m), gl _ _ (by omega : 1 < m),
      gl _ _ (by omega : 3 < m), gl _ _ (by omega : 9 < m), gl _ _ (by omega : 13 < m),
      gl _ _ (by omega : 15 < m), gl _ _ (by omega : 16 < m),
      gl _ _ (by omega : 17 < m), gl _ _ (by omega : 18 < m), gl _ _ (by omega : 19 < m),
      gl _ _ (by omega : 20 < m), gl _ _ (by omega : 21 < m), gl _ _ (by omega : 22 < m),
      gl _ _ (by omega : 23 < m), gl _ _ (by omega : 24 < m), gl _ _ (by omega : 25 < m),
      gr, List.getD_cons_zero, List.getD_cons_succ]
    rfl
  rw [hfold, getD_append_add]
  rfl

theorem d_iff (x : Fin 26 → Bool) :
    (((x 0 && ((x 13 || x 14) || (x 16 || x 22))) ||
      (x 1 && ((x 13 || x 15) || (x 21 || x 25)))) ||
     ((x 3 && ((x 13 || x 19) || (x 23 || x 24))) ||
      (x 9 && ((x 13 || x 17) || (x 18 || x 20))))) =
    decide (∃ p ∈ ({0, 1, 3, 9} : Finset (Fin 13)), ∃ l : Fin 13,
      (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
  have hcheck : ∀ (p : Fin 13) (l : Fin 13),
      p ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      ((p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ↔
        (p = 0 ∧ (l = 0 ∨ l = 1 ∨ l = 3 ∨ l = 9)) ∨
        (p = 1 ∧ (l = 0 ∨ l = 2 ∨ l = 8 ∨ l = 12)) ∨
        (p = 3 ∧ (l = 0 ∨ l = 6 ∨ l = 10 ∨ l = 11)) ∨
        (p = 9 ∧ (l = 0 ∨ l = 4 ∨ l = 5 ∨ l = 7))) := by
    decide
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with (⟨h0, hl⟩ | ⟨h1, hl⟩) | (⟨h3, hl⟩ | ⟨h9, hl⟩)
    · rcases hl with (hl | hl) | (hl | hl)
      · exact ⟨0, by decide, 0, by decide, h0, hl⟩
      · exact ⟨0, by decide, 1, by decide, h0, hl⟩
      · exact ⟨0, by decide, 3, by decide, h0, hl⟩
      · exact ⟨0, by decide, 9, by decide, h0, hl⟩
    · rcases hl with (hl | hl) | (hl | hl)
      · exact ⟨1, by decide, 0, by decide, h1, hl⟩
      · exact ⟨1, by decide, 2, by decide, h1, hl⟩
      · exact ⟨1, by decide, 8, by decide, h1, hl⟩
      · exact ⟨1, by decide, 12, by decide, h1, hl⟩
    · rcases hl with (hl | hl) | (hl | hl)
      · exact ⟨3, by decide, 0, by decide, h3, hl⟩
      · exact ⟨3, by decide, 6, by decide, h3, hl⟩
      · exact ⟨3, by decide, 10, by decide, h3, hl⟩
      · exact ⟨3, by decide, 11, by decide, h3, hl⟩
    · rcases hl with (hl | hl) | (hl | hl)
      · exact ⟨9, by decide, 0, by decide, h9, hl⟩
      · exact ⟨9, by decide, 4, by decide, h9, hl⟩
      · exact ⟨9, by decide, 5, by decide, h9, hl⟩
      · exact ⟨9, by decide, 7, by decide, h9, hl⟩
  · rintro ⟨p, hp, l, hnear, hxp, hxl⟩
    have hc := (hcheck p l hp).mp hnear
    rcases hc with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
    · left; left; refine ⟨hxp, ?_⟩
      rcases hl with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)
    · left; right; refine ⟨hxp, ?_⟩
      rcases hl with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)
    · right; left; refine ⟨hxp, ?_⟩
      rcases hl with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)
    · right; right; refine ⟨hxp, ?_⟩
      rcases hl with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl hxl)
      · exact Or.inl (Or.inr hxl)
      · exact Or.inr (Or.inl hxl)
      · exact Or.inr (Or.inr hxl)

theorem main_proof :
    let D : Finset (Fin 13) := {0, 1, 3, 9}
    let ix : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
    let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
    ∀ B : Circuit, Monotone2 B → B.size ≤ 43 → B.output < 21 + B.size →
      ∃ E : Circuit, Monotone2 E ∧ E.size ≤ B.size + 19 ∧
        ∃ a b : ℕ, a < b ∧
          ∀ x : Fin 26 → Bool,
            ((E.wires (List.ofFn x)).getD a false || (E.wires (List.ofFn x)).getD b false) =
              (B.eval (ix.map x) || decide (∃ p ∈ D, ∃ l : Fin 13, near p l ∧
                x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) := by
  dsimp only
  intro B hB _ hout
  let m : ℕ := 26 + B.size
  let E : Circuit := ⟨B.gates.map remapGate ++ extraGates m, m + 18⟩
  refine ⟨E, ?_, ?_, remapWire B.output, m + 18, ?_, ?_⟩
  · intro g hg
    simp only [E, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩ | hg
    · exact ⟨(hB g' hg').1, by simp [remapGate, (hB g' hg').2]⟩
    · simp only [extraGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                     rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by simp, by simp⟩
  · simp only [E, Circuit.size, List.length_append, List.length_map, extraGates, List.length_cons,
      List.length_nil]
    omega
  · have hlt : remapWire B.output < m := remapWire_lt B.size B.output hout
    omega
  · intro x
    let wB : List Bool := (B.gates.map remapGate).foldl wstep (List.ofFn x)
    have hwB_len : wB.length = m := by
      simp only [wB, m, foldl_len, List.length_ofFn, List.length_map]; rfl
    have hE_wires : E.wires (List.ofFn x) = (extraGates m).foldl wstep wB := by
      change (B.gates.map remapGate ++ extraGates m).foldl wstep (List.ofFn x) = _
      rw [List.foldl_append]
    have ha : (E.wires (List.ofFn x)).getD (remapWire B.output) false = B.eval (ixList.map x) := by
      rw [hE_wires]
      have hlt : remapWire B.output < wB.length := by rw [hwB_len]; exact remapWire_lt B.size B.output hout
      rw [foldl_prefix _ wB _ hlt]
      exact foldl_remap B.gates x B.output
    have hwB_in : ∀ (k : ℕ) (hk : k < 26), wB.getD k false = x ⟨k, hk⟩ := by
      intro k hk
      rw [show wB = (B.gates.map remapGate).foldl wstep (List.ofFn x) from rfl,
          foldl_prefix _ (List.ofFn x) k (by simp; omega),
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    have hb : (E.wires (List.ofFn x)).getD (m + 18) false =
        decide (∃ p ∈ ({0, 1, 3, 9} : Finset (Fin 13)), ∃ l : Fin 13,
          (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
      rw [hE_wires, ← hwB_len, extra_eval wB (by rw [hwB_len]; omega)]
      simp only [hwB_in 0 (by omega), hwB_in 1 (by omega), hwB_in 3 (by omega), hwB_in 9 (by omega),
        hwB_in 13 (by omega), hwB_in 14 (by omega), hwB_in 15 (by omega), hwB_in 16 (by omega),
        hwB_in 17 (by omega), hwB_in 18 (by omega), hwB_in 19 (by omega), hwB_in 20 (by omega),
        hwB_in 21 (by omega), hwB_in 22 (by omega), hwB_in 23 (by omega), hwB_in 24 (by omega),
        hwB_in 25 (by omega)]
      exact d_iff x
    rw [ha, hb]
    rfl

end PEqualNP.Outside.L_meta_18849_aux

theorem PEqualNP.Outside.L_meta_18849 : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))]; let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size ≤ (43 : ℕ) → x4.output < (21 : ℕ) + x4.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x4.size + (19 : ℕ) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x9 < x10 ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ((x8.wires (List.ofFn x11)).getD x9 Bool.false || (x8.wires (List.ofFn x11)).getD x10 Bool.false) = (x4.eval (List.map x11 x2) || Decidable.decide (∃ x12 ∈ x1, ∃ (x13 : Fin (13 : ℕ)), x3 x12 x13 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true)))  := by
  exact PEqualNP.Outside.L_meta_18849_aux.main_proof
