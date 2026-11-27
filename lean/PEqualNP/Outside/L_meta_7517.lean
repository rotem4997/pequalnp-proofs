import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7517

open PEqualNP.CircuitLowerBounds

def lval (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | GateOp.or  => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def lstep (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  w ++ [lval g.op (g.inputs.map fun i => w.getD i (false, false))]

def linit (isLine : ℕ → Bool) (x : List Bool) : List (Bool × Bool) :=
  (x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)

theorem lp_eq (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C isLine x = C.gates.foldl lstep (linit isLine x) := rfl

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem getD_snoc {α : Type} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_append_left h, if_pos h]
  · rw [List.getElem?_append_right (by omega), if_neg h]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [if_neg h2]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

theorem linit_getD (isLine : ℕ → Bool) (x : List Bool) (i : ℕ) :
    (linit isLine x).getD i (false, false) =
      if isLine i then (false, x.getD i false) else (x.getD i false, false) := by
  unfold linit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_zipIdx]
  cases x[i]? <;> simp

theorem linit_length (isLine : ℕ → Bool) (x : List Bool) : (linit isLine x).length = x.length := by
  simp [linit]

theorem wpre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl wstep w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    simp only [List.foldl_cons]
    rw [ih _ _ (by simp [wstep]; omega)]
    unfold wstep
    rw [getD_snoc, if_pos h]

theorem wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wstep_getD (w : List Bool) (g : Gate) (i : ℕ) : (wstep w g).getD i false =
    if i < w.length then w.getD i false else
      if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold wstep; exact getD_snoc _ _ _ _

theorem lstep_len (w : List (Bool × Bool)) (g : Gate) : (lstep w g).length = w.length + 1 := by
  simp [lstep]

theorem lstep_getD (w : List (Bool × Bool)) (g : Gate) (i : ℕ) : (lstep w g).getD i (false, false) =
    if i < w.length then w.getD i (false, false) else
      if i = w.length then lval g.op (g.inputs.map fun i => w.getD i (false, false))
      else (false, false) := by
  unfold lstep; exact getD_snoc _ _ _ _

theorem wlen : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl wstep w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    rw [ih]; simp [wstep]; omega

theorem key (C : Circuit) (n : ℕ) (isLine : ℕ → Bool) (x0 V0 : List Bool) (x4 : ℕ → Bool)
    (hx0 : x0.length = n) (hV0 : V0.length = n)
    (hAO : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRB : ∀ j < C.gates.length,
      ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, i < n + j)
    (hbase : ∀ i < n, (linit isLine x0).getD i (false, false) = (V0.getD i false, x4 i))
    (hstep : ∀ k < C.size,
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and →
        x4 (n + k) = ((C.wires V0).getD (PEqualNP.TopForm.opnd C k 0) false &&
          x4 (PEqualNP.TopForm.opnd C k 1) ||
          x4 (PEqualNP.TopForm.opnd C k 0) &&
          (C.wires V0).getD (PEqualNP.TopForm.opnd C k 1) false)) ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or →
        x4 (n + k) = (x4 (PEqualNP.TopForm.opnd C k 0) || x4 (PEqualNP.TopForm.opnd C k 1)))) :
    ∀ k ≤ C.gates.length, ((C.gates.take k).foldl lstep (linit isLine x0)).length = n + k ∧
      ∀ i < n + k, ((C.gates.take k).foldl lstep (linit isLine x0)).getD i (false, false) =
        ((C.wires V0).getD i false, x4 i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [linit_length, hx0], ?_⟩
    intro i hi
    simp only [List.take_zero, List.foldl_nil]
    rw [hbase i (by omega), wires_eq, wpre _ _ _ (by omega)]
  | succ k ih =>
    intro hk
    have hkl : k < C.gates.length := by omega
    obtain ⟨hl, hv⟩ := ih (by omega)
    rw [List.take_succ, List.getElem?_eq_getElem hkl, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hkl]
    obtain ⟨hop, h2⟩ := hAO C.gates[k] (List.getElem_mem hkl)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
    have ha : a < n + k := hRB k hkl a (by rw [hg, hab]; simp)
    have hb : b < n + k := hRB k hkl b (by rw [hg, hab]; simp)
    have hoa : PEqualNP.TopForm.opnd C k 0 = a := by
      unfold PEqualNP.TopForm.opnd; rw [hg, hab]; rfl
    have hob : PEqualNP.TopForm.opnd C k 1 = b := by
      unfold PEqualNP.TopForm.opnd; rw [hg, hab]; rfl
    have e : C.wires V0 = (C.gates.drop (k + 1)).foldl wstep
        (wstep ((C.gates.take k).foldl wstep V0) C.gates[k]) := by
      rw [wires_eq]
      conv_lhs => rw [← List.take_append_drop (k + 1) C.gates]
      rw [List.foldl_append, List.take_succ, List.getElem?_eq_getElem hkl, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hVkl : ((C.gates.take k).foldl wstep V0).length = n + k := by
      rw [wlen, hV0, List.length_take]; omega
    have hpre : ∀ i < n + k, (C.wires V0).getD i false =
        ((C.gates.take k).foldl wstep V0).getD i false := by
      intro i hi
      rw [e, wpre _ _ _ (by rw [wstep_len]; omega)]
      rw [wstep_getD, if_pos (by omega)]
    have hVk : (C.wires V0).getD (n + k) false =
        C.gates[k].op.eval [(C.wires V0).getD a false, (C.wires V0).getD b false] := by
      rw [hpre a ha, hpre b hb, e, wpre _ _ _ (by rw [wstep_len]; omega)]
      rw [wstep_getD, if_neg (by omega), if_pos (by omega), hab]
      rfl
    refine ⟨by rw [lstep_len, hl, Nat.add_assoc], ?_⟩
    intro i hi
    rw [lstep_getD, hl]
    split_ifs with h1 h3
    · exact hv i h1
    · subst h3
      rw [hab]
      simp only [List.map_cons, List.map_nil]
      rw [hv a ha, hv b hb]
      obtain ⟨hand, hor⟩ := hstep k hkl
      rw [hg, hoa, hob] at hand hor
      rcases hop with hop | hop
      · rw [hVk, hand hop, hop]
        simp [lval, GateOp.eval]
      · rw [hVk, hor hop, hop]
        simp [lval, GateOp.eval]
    · omega

end PEqualNP.Outside.L_meta_7517

theorem PEqualNP.Outside.L_meta_7517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →     ∀ (x3 : Bool) (x4 : ℕ → Bool),       have x5 : List Bool := x1.wires (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = if x3 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));       (∀ x6 < (14 : ℕ), x4 x6 = Decidable.decide (x6 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) →         (∀ x7 < x1.size,             have x9 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7;             have x10 : ℕ := PEqualNP.TopForm.opnd x1 x7 (0 : Fin (2 : ℕ));             have x11 : ℕ := PEqualNP.TopForm.opnd x1 x7 (1 : Fin (2 : ℕ));             (x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((14 : ℕ) + x7) = (x5.getD x10 Bool.false && x4 x11 || x4 x10 && x5.getD x11 Bool.false)) ∧ (x9.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((14 : ℕ) + x7) = (x4 x10 || x4 x11))) →           x4 x1.output = Bool.false → PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x9 : ℕ) => x9 == if x3 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.false := by
  intro C hAO x3 x4 x5 hin hstep hout
  have hAO' : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩
  have K := PEqualNP.Outside.L_meta_7517.key C 14
    (fun x9 => x9 == if x3 = true then 7 else 0)
    ((List.range 14).map fun i => i == 0 || i == 7)
    (List.ofFn fun (x5 : Fin 14) => decide (x5 = if x3 = true then (0 : Fin 14) else (7 : Fin 14)))
    x4 (by simp) (by simp) hAO' hAO.2.1 ?_ hstep C.gates.length le_rfl
  · rw [List.take_of_length_le (le_refl _)] at K
    unfold PEqualNP.ReadK.lineSingle
    rw [PEqualNP.Outside.L_meta_7517.lp_eq]
    by_cases ho : C.output < 14 + C.gates.length
    · rw [K.2 _ ho]; exact hout
    · rw [List.getD_eq_default _ _ (by rw [K.1]; omega)]
  · intro i hi
    rw [PEqualNP.Outside.L_meta_7517.linit_getD, hin i hi,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    cases x3 <;> interval_cases i <;> simp [Fin.ext_iff]
