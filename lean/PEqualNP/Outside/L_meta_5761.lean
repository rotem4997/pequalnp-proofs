import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5761

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

private def scan {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun a g => a ++ [f a g]) w

private theorem scan_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate)
    (w : List α) : scan f (g :: gs) w = scan f gs (w ++ [f w g]) := rfl

private theorem scan_append {α : Type} (f : List α → Gate → α) (xs ys : List Gate)
    (w : List α) : scan f (xs ++ ys) w = scan f ys (scan f xs w) := by
  simp only [scan, List.foldl_append]

private theorem scan_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan f gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [scan]
  | cons g gs ih => rw [scan_cons, ih]; simp; omega

private theorem scan_earlier {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (k : ℕ) (hk : k < w.length) :
    (scan f gs w).getD k d = w.getD k d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hk

private theorem scan_at_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length) (a b : ℕ)
    (ha : a < w.length + j) (hb : b < w.length + j) (op : α → α → α)
    (hf : ∀ z, f z gs[j] = op (z.getD a d) (z.getD b d)) :
    (scan f gs w).getD (w.length + j) d =
      op ((scan f gs w).getD a d) ((scan f gs w).getD b d) := by
  let pre := scan f (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan f gs w = scan f (gs[j] :: gs.drop (j + 1)) pre := by
    have ht := List.take_append_drop j gs
    conv_lhs => rw [← ht, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan f gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_earlier f _ pre d i (by omega)
  rw [hpre a ha, hpre b hb, hs, scan_cons, scan_earlier f _ _ d _ (by simp [hp]),
    List.getD_append_right _ _ _ _ (by omega)]
  simpa [hp] using hf pre

private def wval (N : ℕ) (D : Circuit) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (D.wires (List.ofFn z)).getD w false

private theorem wval_input (N : ℕ) (D : Circuit) (z : Fin N → Bool) (i : ℕ) (hi : i < N) :
    wval N D z i = z ⟨i, hi⟩ := by
  change (scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
    D.gates (List.ofFn z)).getD i false = _
  rw [scan_earlier _ _ _ _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private theorem wval_ge (N : ℕ) (D : Circuit) (z : Fin N → Bool) (w : ℕ)
    (hw : N + D.size ≤ w) : wval N D z w = false := by
  change (scan (fun a g => g.op.eval (g.inputs.map fun idx => a.getD idx false))
    D.gates (List.ofFn z)).getD w false = false
  apply List.getD_eq_default
  rw [scan_length, List.length_ofFn]
  exact hw

private theorem gateAt_eq (D : Circuit) (j : ℕ) (hj : j < D.size) :
    gateAt D j = D.gates[j] := by
  change D.gates.getD j ⟨GateOp.or, []⟩ = D.gates[j]
  exact List.getD_eq_getElem _ _ hj

private theorem ao2_gate_spec (N : ℕ) (D : Circuit) (hAO : IsAO2 N D)
    (j : ℕ) (hj : j < D.size) :
    ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) ∧
    (gateAt D j).inputs = [opnd D j 0, opnd D j 1] ∧
    opnd D j 0 < N + j ∧ opnd D j 1 < N + j ∧
    ∀ z : Fin N → Bool,
      wval N D z (N + j) =
        (gateAt D j).op.eval [wval N D z (opnd D j 0), wval N D z (opnd D j 1)] := by
  have hmem : D.gates[j] ∈ D.gates := List.getElem_mem hj
  have hga : gateAt D j = D.gates[j] := gateAt_eq D j hj
  have hop : (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or := by
    rw [hga]
    exact hAO.1 D.gates[j] hmem
  have hlen : (gateAt D j).inputs.length = 2 := by
    rw [hga]
    exact hAO.2.2 D.gates[j] hmem
  rcases hinp : (gateAt D j).inputs with _ | ⟨a, rest⟩
  · rw [hinp] at hlen; simp at hlen
  · rcases rest with _ | ⟨b, rest2⟩
    · rw [hinp] at hlen; simp at hlen
    · rcases rest2 with _ | ⟨c, rest3⟩
      · have ha0 : opnd D j 0 = a := by simp [opnd, hinp]
        have hb0 : opnd D j 1 = b := by simp [opnd, hinp]
        have ha_lt : a < N + j := hAO.2.1 j hj a (by rw [hinp]; simp)
        have hb_lt : b < N + j := hAO.2.1 j hj b (by rw [hinp]; simp)
        refine ⟨hop, by rw [ha0, hb0], by rwa [ha0], by rwa [hb0], fun z => ?_⟩
        rw [ha0, hb0]
        change (scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
          D.gates (List.ofFn z)).getD (N + j) false =
          (gateAt D j).op.eval
            [(scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
              D.gates (List.ofFn z)).getD a false,
             (scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
              D.gates (List.ofFn z)).getD b false]
        have hlen_in : (List.ofFn z).length = N := List.length_ofFn
        have hstep := scan_at_gate
          (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
          D.gates (List.ofFn z) false j hj a b
          (by rw [hlen_in]; exact ha_lt) (by rw [hlen_in]; exact hb_lt)
          (fun x y => (gateAt D j).op.eval [x, y])
          (fun w => by rw [← hga, hinp]; rfl)
        simpa only [hlen_in] using hstep
      · rw [hinp] at hlen; simp at hlen

private theorem eval_and (x y : Bool) : GateOp.and.eval [x, y] = (x && y) := by
  cases x <;> cases y <;> rfl

private theorem eval_or (x y : Bool) : GateOp.or.eval [x, y] = (x || y) := by
  cases x <;> cases y <;> rfl

private def scanPts (n m : ℕ) (D : Circuit) : List (Finset (Fin n)) :=
  letI : DecidableEq GateOp := gateOpDecEq
  scan (fun acc g =>
    if g.op = GateOp.or then
      acc.getD (g.inputs.getD 0 0) ∅ ∪ acc.getD (g.inputs.getD 1 0) ∅
    else ∅)
    D.gates ((List.range (n + m)).map fun i => if h : i < n then {⟨i, h⟩} else ∅)

private def scanLines (n m : ℕ) (D : Circuit) : List (Finset (Fin m)) :=
  letI : DecidableEq GateOp := gateOpDecEq
  scan (fun acc g =>
    if g.op = GateOp.or then
      acc.getD (g.inputs.getD 0 0) ∅ ∪ acc.getD (g.inputs.getD 1 0) ∅
    else ∅)
    D.gates ((List.range (n + m)).map fun i =>
      if h : n ≤ i ∧ i < n + m then {⟨i - n, by omega⟩} else ∅)

private def wirePts (n m : ℕ) (D : Circuit) (x : ℕ) : Finset (Fin n) :=
  (scanPts n m D).getD x ∅

private def wireLines (n m : ℕ) (D : Circuit) (x : ℕ) : Finset (Fin m) :=
  (scanLines n m D).getD x ∅

private theorem wirePts_input (n m : ℕ) (D : Circuit) (i : ℕ) (hi : i < n + m) :
    wirePts n m D i = if h : i < n then {⟨i, h⟩} else ∅ := by
  unfold wirePts scanPts
  rw [scan_earlier _ _ _ _ _ (by simp [hi]),
    List.getD_eq_getElem _ _ (by simp [hi])]
  simp

private theorem wireLines_input (n m : ℕ) (D : Circuit) (i : ℕ) (hi : i < n + m) :
    wireLines n m D i = if h : n ≤ i ∧ i < n + m then {⟨i - n, by omega⟩} else ∅ := by
  unfold wireLines scanLines
  rw [scan_earlier _ _ _ _ _ (by simp [hi]),
    List.getD_eq_getElem _ _ (by simp [hi])]
  simp

private theorem wirePts_or_gate (n m : ℕ) (D : Circuit) (hAO : IsAO2 (n + m) D)
    (j : ℕ) (hj : j < D.size) (hor : (gateAt D j).op = GateOp.or) :
    wirePts n m D (n + m + j) =
      wirePts n m D (opnd D j 0) ∪ wirePts n m D (opnd D j 1) := by
  obtain ⟨_, _, ha, hb, _⟩ := ao2_gate_spec (n + m) D hAO j hj
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold wirePts scanPts
  have hga : gateAt D j = D.gates[j] := gateAt_eq D j hj
  have hlen : ((List.range (n + m)).map fun i =>
      if h : i < n then ({⟨i, h⟩} : Finset (Fin n)) else ∅).length = n + m := by simp
  have hstep := scan_at_gate
    (fun acc (g : Gate) =>
      if g.op = GateOp.or then
        acc.getD (g.inputs.getD 0 0) ∅ ∪ acc.getD (g.inputs.getD 1 0) ∅
      else ∅)
    D.gates _ (∅ : Finset (Fin n)) j hj (opnd D j 0) (opnd D j 1)
    (by rw [hlen]; exact ha) (by rw [hlen]; exact hb) (· ∪ ·)
    (fun z => by
      have hop' : D.gates[j].op = GateOp.or := by rw [← hga]; exact hor
      simp only [hop', ↓reduceIte]
      change z.getD ((D.gates[j]).inputs.getD 0 0) ∅ ∪ z.getD ((D.gates[j]).inputs.getD 1 0) ∅ = _
      rw [← hga]; rfl)
  simpa only [hlen] using hstep

private theorem wireLines_or_gate (n m : ℕ) (D : Circuit) (hAO : IsAO2 (n + m) D)
    (j : ℕ) (hj : j < D.size) (hor : (gateAt D j).op = GateOp.or) :
    wireLines n m D (n + m + j) =
      wireLines n m D (opnd D j 0) ∪ wireLines n m D (opnd D j 1) := by
  obtain ⟨_, _, ha, hb, _⟩ := ao2_gate_spec (n + m) D hAO j hj
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold wireLines scanLines
  have hga : gateAt D j = D.gates[j] := gateAt_eq D j hj
  have hlen : ((List.range (n + m)).map fun i =>
      if h : n ≤ i ∧ i < n + m then ({⟨i - n, by omega⟩} : Finset (Fin m)) else ∅).length = n + m := by simp
  have hstep := scan_at_gate
    (fun acc (g : Gate) =>
      if g.op = GateOp.or then
        acc.getD (g.inputs.getD 0 0) ∅ ∪ acc.getD (g.inputs.getD 1 0) ∅
      else ∅)
    D.gates _ (∅ : Finset (Fin m)) j hj (opnd D j 0) (opnd D j 1)
    (by rw [hlen]; exact ha) (by rw [hlen]; exact hb) (· ∪ ·)
    (fun z => by
      have hop' : D.gates[j].op = GateOp.or := by rw [← hga]; exact hor
      simp only [hop', ↓reduceIte]
      change z.getD ((D.gates[j]).inputs.getD 0 0) ∅ ∪ z.getD ((D.gates[j]).inputs.getD 1 0) ∅ = _
      rw [← hga]; rfl)
  simpa only [hlen] using hstep

private def OrStep (n m : ℕ) (D : Circuit) (x y : ℕ) : Prop :=
  ∃ j < D.size, y = n + m + j ∧ (gateAt D j).op = GateOp.or ∧ x ∈ (gateAt D j).inputs

private def OrPath (n m : ℕ) (D : Circuit) (x y : ℕ) : Prop :=
  Relation.ReflTransGen (OrStep n m D) x y

private theorem orPath_sound (n m : ℕ) (D : Circuit) (hAO : IsAO2 (n + m) D)
    (z : Fin (n + m) → Bool) {x y : ℕ} (hpath : OrPath n m D x y)
    (hx : wval (n + m) D z x = true) : wval (n + m) D z y = true := by
  induction hpath with
  | refl => exact hx
  | tail _ hstep ih =>
    rcases hstep with ⟨j, hj, rfl, hor, hmem⟩
    obtain ⟨_, hinp, _, _, hev⟩ := ao2_gate_spec (n + m) D hAO j hj
    rw [hev z, hor, eval_or, Bool.or_eq_true]
    rw [hinp] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl ih
    · exact Or.inr ih

private theorem orPath_U_closed (n m : ℕ) (D : Circuit) (U : Finset ℕ)
    (hAO : IsAO2 (n + m) D)
    (hU : ∀ w ∈ U, w < n + m ∨
      ∃ j < D.size, w = n + m + j ∧ (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ U)
    {x y : ℕ} (hpath : OrPath n m D x y) :
    y ∈ U → x ∈ U ∧ wirePts n m D x ⊆ wirePts n m D y ∧ wireLines n m D x ⊆ wireLines n m D y := by
  induction hpath with
  | refl => intro hy; exact ⟨hy, Finset.Subset.rfl, Finset.Subset.rfl⟩
  | tail _ hstep ih =>
    intro hz
    rcases hstep with ⟨j, hj, rfl, hor, hmem⟩
    rcases hU (n + m + j) hz with hlt | ⟨i, _, hi_eq, _, hi_in⟩
    · omega
    · have hij : i = j := by omega
      subst i
      have hyU : _ ∈ U := hi_in _ hmem
      obtain ⟨hxU, hsubP, hsubL⟩ := ih hyU
      obtain ⟨_, hinp, _, _, _⟩ := ao2_gate_spec (n + m) D hAO j hj
      rw [hinp] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      refine ⟨hxU, hsubP.trans ?_, hsubL.trans ?_⟩
      · rw [wirePts_or_gate n m D hAO j hj hor]
        rcases hmem with rfl | rfl
        · exact Finset.subset_union_left
        · exact Finset.subset_union_right
      · rw [wireLines_or_gate n m D hAO j hj hor]
        rcases hmem with rfl | rfl
        · exact Finset.subset_union_left
        · exact Finset.subset_union_right

private theorem wval_mem_U (n m : ℕ) (D : Circuit) (U : Finset ℕ)
    (hAO : IsAO2 (n + m) D)
    (hU : ∀ w ∈ U, w < n + m ∨
      ∃ j < D.size, w = n + m + j ∧ (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ U) :
    ∀ x, x ∈ U →
      (∀ z : Fin (n + m) → Bool,
        wval (n + m) D z x = true ↔
          (∃ p ∈ wirePts n m D x, z (Fin.castAdd m p) = true) ∨
          (∃ l ∈ wireLines n m D x, z (Fin.natAdd n l) = true)) ∧
      ((wirePts n m D x).Nonempty ∨ (wireLines n m D x).Nonempty) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hxU
    rcases hU x hxU with hlt | ⟨j, hj, rfl, hor, hsub⟩
    · by_cases hxn : x < n
      · have hpts : wirePts n m D x = {⟨x, hxn⟩} := by
          rw [wirePts_input n m D x hlt]; simp [hxn]
        have hlines : wireLines n m D x = ∅ := by
          rw [wireLines_input n m D x hlt]
          have hnot : ¬ (n ≤ x ∧ x < n + m) := by omega
          simp [hnot]
        refine ⟨fun z => ?_, Or.inl (by rw [hpts]; exact Finset.singleton_nonempty _)⟩
        rw [wval_input (n + m) D z x hlt, hpts, hlines]
        simp only [Finset.mem_singleton, exists_eq_left, Finset.notMem_empty, false_and,
          exists_false, or_false]
        have hfin : (⟨x, hlt⟩ : Fin (n + m)) = Fin.castAdd m ⟨x, hxn⟩ := by ext; rfl
        rw [hfin]
      · have hge : n ≤ x ∧ x < n + m := ⟨by omega, hlt⟩
        have hpts : wirePts n m D x = ∅ := by
          rw [wirePts_input n m D x hlt]; simp [hxn]
        have hlines : wireLines n m D x = {⟨x - n, by omega⟩} := by
          rw [wireLines_input n m D x hlt]; simp [hge]
        refine ⟨fun z => ?_, Or.inr (by rw [hlines]; exact Finset.singleton_nonempty _)⟩
        rw [wval_input (n + m) D z x hlt, hpts, hlines]
        simp only [Finset.notMem_empty, false_and, exists_false, false_or,
          Finset.mem_singleton, exists_eq_left]
        have hfin : (⟨x, hlt⟩ : Fin (n + m)) = Fin.natAdd n ⟨x - n, by omega⟩ := by
          ext; dsimp; omega
        rw [hfin]
    · obtain ⟨_, hinp, ha_lt, hb_lt, hev⟩ := ao2_gate_spec (n + m) D hAO j hj
      have haU : opnd D j 0 ∈ U := hsub _ (by rw [hinp]; simp)
      have hbU : opnd D j 1 ∈ U := hsub _ (by rw [hinp]; simp)
      obtain ⟨iha_ev, iha_ne⟩ := ih (opnd D j 0) ha_lt haU
      obtain ⟨ihb_ev, _⟩ := ih (opnd D j 1) hb_lt hbU
      have hP := wirePts_or_gate n m D hAO j hj hor
      have hL := wireLines_or_gate n m D hAO j hj hor
      constructor
      · intro z
        rw [hev z, hor, eval_or, Bool.or_eq_true, iha_ev z, ihb_ev z, hP, hL]
        constructor
        · rintro ((⟨p, hp, hzp⟩ | ⟨l, hl, hzl⟩) | (⟨p, hp, hzp⟩ | ⟨l, hl, hzl⟩))
          · exact Or.inl ⟨p, Finset.mem_union_left _ hp, hzp⟩
          · exact Or.inr ⟨l, Finset.mem_union_left _ hl, hzl⟩
          · exact Or.inl ⟨p, Finset.mem_union_right _ hp, hzp⟩
          · exact Or.inr ⟨l, Finset.mem_union_right _ hl, hzl⟩
        · rintro (⟨p, hp, hzp⟩ | ⟨l, hl, hzl⟩)
          · rcases Finset.mem_union.mp hp with hp | hp
            · exact Or.inl (Or.inl ⟨p, hp, hzp⟩)
            · exact Or.inr (Or.inl ⟨p, hp, hzp⟩)
          · rcases Finset.mem_union.mp hl with hl | hl
            · exact Or.inl (Or.inr ⟨l, hl, hzl⟩)
            · exact Or.inr (Or.inr ⟨l, hl, hzl⟩)
      · rw [hP, hL]
        rcases iha_ne with ⟨p, hp⟩ | ⟨l, hl⟩
        · exact Or.inl ⟨p, Finset.mem_union_left _ hp⟩
        · exact Or.inr ⟨l, Finset.mem_union_left _ hl⟩

private theorem card_le_one_input_pts (n m : ℕ) (D : Circuit) (x : ℕ) (hx : x < n + m) :
    (wirePts n m D x).card ≤ 1 := by
  rw [wirePts_input n m D x hx]
  split_ifs <;> simp

private theorem card_le_one_input_lines (n m : ℕ) (D : Circuit) (x : ℕ) (hx : x < n + m) :
    (wireLines n m D x).card ≤ 1 := by
  rw [wireLines_input n m D x hx]
  split_ifs <;> simp

private theorem exists_two_of_two_le_card {α : Type} {s : Finset α} (h : 2 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  have hlt : 1 < s.card := by omega
  exact Finset.one_lt_card.mp hlt

private theorem main (n m : ℕ) (E : Finset (Fin n × Fin m)) (D : Circuit) (U : Finset ℕ)
    (hC4 : ∀ (p q : Fin n) (l r : Fin m), p ≠ q → l ≠ r →
      ¬ ((p, l) ∈ E ∧ (p, r) ∈ E ∧ (q, l) ∈ E ∧ (q, r) ∈ E))
    (hAO : IsAO2 (n + m) D)
    (hEval : ∀ z : Fin (n + m) → Bool,
      circuitFun (n + m) D z =
        decide (∃ (p : Fin n) (l : Fin m),
          (p, l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true))
    (hU : ∀ w ∈ U, w < n + m ∨
      ∃ j < D.size, w = n + m + j ∧ (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ U)
    (hAndU : ∀ j < D.size, (gateAt D j).op = GateOp.and → ∀ u ∈ (gateAt D j).inputs, u ∈ U) :
    have k : ℕ := n + m + D.size
    ∃ (A : Finset (Fin n ⊕ Fin m)) (R : Fin n ⊕ Fin m → Finset ℕ)
      (T : Fin n ⊕ Fin m → Finset ℕ) (F : Fin n ⊕ Fin m → ℕ → Finset (Fin n × Fin m))
      (a b : ℕ → ℕ) (t : ℕ),
      have W : Fin n ⊕ Fin m → Finset (Fin n × Fin m) := fun c => (R c).biUnion (F c)
      (∀ e ∈ E, ∃ c ∈ A, e ∈ W c) ∧
      (∀ c ∈ A, ∀ e ∈ W c, c = Sum.inl e.1 ∨ c = Sum.inr e.2) ∧
      (∀ c ∈ A, R c ⊆ Finset.range k ∧ T c ⊆ Finset.range k ∧
        (∀ x < k, x ∉ T c → (F c x).card ≤ 1) ∧
        ∀ x ∈ T c, a x < x ∧ b x < x ∧ F c x = F c (a x) ∪ F c (b x)) ∧
      A.card ≤ t ∧ ∑ c ∈ A, (R c).card ≤ t ∧ 2 * t + ∑ c ∈ A, (T c).card ≤ D.size + 1 := by
  classical
  dsimp only
  let k : ℕ := n + m + D.size
  by_cases hEempty : E = ∅
  · subst hEempty
    refine ⟨∅, fun _ => ∅, fun _ => ∅, fun _ _ => ∅, fun _ => 0, fun _ => 0, 0, ?_⟩
    simp
  have hEne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEempty
  -- Helper: D.eval is false on any input where all line bits or all point bits are false
  have eval_false_pts : ∀ z : Fin (n + m) → Bool,
      (∀ l : Fin m, z (Fin.natAdd n l) = false) → circuitFun (n + m) D z = false := by
    intro z hno
    rw [hEval z, decide_eq_false_iff_not]
    rintro ⟨p, l, _, _, hl⟩
    rw [hno l] at hl; cases hl
  have eval_false_lines : ∀ z : Fin (n + m) → Bool,
      (∀ p : Fin n, z (Fin.castAdd m p) = false) → circuitFun (n + m) D z = false := by
    intro z hno
    rw [hEval z, decide_eq_false_iff_not]
    rintro ⟨p, l, _, hp, _⟩
    rw [hno p] at hp; cases hp
  have eval_false_single : ∀ v : Fin (n + m),
      circuitFun (n + m) D (fun i => decide (i = v)) = false := by
    intro v
    by_cases hv : v.val < n
    · apply eval_false_pts
      intro l
      simp only [decide_eq_false_iff_not]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    · apply eval_false_lines
      intro p
      simp only [decide_eq_false_iff_not]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
  have not_orPath_lt : ∀ x < n + m, ¬ OrPath n m D x D.output := by
    intro x hx hpath
    let v : Fin (n + m) := ⟨x, hx⟩
    let z : Fin (n + m) → Bool := fun i => decide (i = v)
    have hwx : wval (n + m) D z x = true := by
      rw [wval_input (n + m) D z x hx]
      simp [z, v]
    have hout : circuitFun (n + m) D z = true := orPath_sound n m D hAO z hpath hwx
    rw [eval_false_single v] at hout
    cases hout
  have not_orPath_U : ∀ x ∈ U, ¬ OrPath n m D x D.output := by
    intro x hxU hpath
    obtain ⟨hev, hne⟩ := wval_mem_U n m D U hAO hU x hxU
    rcases hne with ⟨p, hp⟩ | ⟨l, hl⟩
    · let v : Fin (n + m) := Fin.castAdd m p
      let z : Fin (n + m) → Bool := fun i => decide (i = v)
      have hwx : wval (n + m) D z x = true := (hev z).mpr (Or.inl ⟨p, hp, by simp [z, v]⟩)
      have hout : circuitFun (n + m) D z = true := orPath_sound n m D hAO z hpath hwx
      rw [eval_false_single v] at hout; cases hout
    · let v : Fin (n + m) := Fin.natAdd n l
      let z : Fin (n + m) → Bool := fun i => decide (i = v)
      have hwx : wval (n + m) D z x = true := (hev z).mpr (Or.inr ⟨l, hl, by simp [z, v]⟩)
      have hout : circuitFun (n + m) D z = true := orPath_sound n m D hAO z hpath hwx
      rw [eval_false_single v] at hout; cases hout
  -- Output wire is an actual gate n + m + out
  have hout_ge : n + m ≤ D.output := by
    by_contra hlt
    exact not_orPath_lt D.output (by omega) Relation.ReflTransGen.refl
  have hout_lt : D.output < n + m + D.size := by
    by_contra hge
    obtain ⟨⟨p0, l0⟩, he0⟩ := hEne
    let z : Fin (n + m) → Bool :=
      fun i => decide (i = Fin.castAdd m p0 ∨ i = Fin.natAdd n l0)
    have ht : circuitFun (n + m) D z = true := by
      rw [hEval z, decide_eq_true_eq]
      exact ⟨p0, l0, he0, by simp [z], by simp [z]⟩
    have hf : wval (n + m) D z D.output = false := wval_ge (n + m) D z D.output (by omega)
    change wval (n + m) D z D.output = true at ht
    rw [hf] at ht; cases ht
  let out : ℕ := D.output - (n + m)
  have hout_idx : out < D.size := by omega
  have hout_eq : D.output = n + m + out := by omega
  -- Define S_AND, TopOR, U_gates
  let S_AND : Finset ℕ := (Finset.range D.size).filter fun j =>
    (gateAt D j).op = GateOp.and ∧ OrPath n m D (n + m + j) D.output
  let TopOR : Finset ℕ := (Finset.range D.size).filter fun j =>
    (gateAt D j).op = GateOp.or ∧ OrPath n m D (n + m + j) D.output
  let U_gates : Finset ℕ := (Finset.range D.size).filter fun j => n + m + j ∈ U
  have hDisj_AT : Disjoint S_AND TopOR := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2.1
    have h2 := (Finset.mem_filter.mp hj2).2.1
    rw [h1] at h2; cases h2
  have hDisj_AU : Disjoint S_AND U_gates := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hpath := (Finset.mem_filter.mp hj1).2.2
    have hmemU := (Finset.mem_filter.mp hj2).2
    exact not_orPath_U (n + m + j) hmemU hpath
  have hDisj_TU : Disjoint TopOR U_gates := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hpath := (Finset.mem_filter.mp hj1).2.2
    have hmemU := (Finset.mem_filter.mp hj2).2
    exact not_orPath_U (n + m + j) hmemU hpath
  have hSum_gates : S_AND.card + TopOR.card + U_gates.card ≤ D.size := by
    have hsub : S_AND ∪ TopOR ∪ U_gates ⊆ Finset.range D.size := by
      intro j hj
      simp only [Finset.mem_union] at hj
      rcases hj with (h | h) | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    have hdisj1 : Disjoint (S_AND ∪ TopOR) U_gates := Finset.disjoint_union_left.mpr ⟨hDisj_AU, hDisj_TU⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hDisj_AT,
      Finset.card_range] at hcard
    exact hcard
  -- Prove S_AND.card ≤ TopOR.card + 1 via injection into TopOR × Fin 2
  have hAnd_le_TopOR : S_AND.card ≤ TopOR.card + 1 := by
    have hout_mem : out ∈ S_AND ∪ TopOR := by
      obtain ⟨hop, _, _, _, _⟩ := ao2_gate_spec (n + m) D hAO out hout_idx
      have hpath : OrPath n m D (n + m + out) D.output := by
        rw [← hout_eq]; exact Relation.ReflTransGen.refl
      rcases hop with hand | hor
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hout_idx, hand, hpath⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hout_idx, hor, hpath⟩)
    have hstep_exists : ∀ j ∈ (S_AND ∪ TopOR).erase out,
        ∃ p : ℕ × Fin 2, p ∈ TopOR ×ˢ (Finset.univ : Finset (Fin 2)) ∧
          opnd D p.1 p.2 = n + m + j := by
      intro j hj
      have hne : j ≠ out := (Finset.mem_erase.mp hj).1
      have hjmem := (Finset.mem_erase.mp hj).2
      have hpath : OrPath n m D (n + m + j) D.output := by
        rcases Finset.mem_union.mp hjmem with h | h
        · exact (Finset.mem_filter.mp h).2.2
        · exact (Finset.mem_filter.mp h).2.2
      have hne_w : n + m + j ≠ D.output := by omega
      rcases Relation.ReflTransGen.cases_head hpath with hEq | ⟨y, hstep, hrest⟩
      · exact (hne_w hEq).elim
      · rcases hstep with ⟨g, hg_lt, rfl, hg_or, hg_in⟩
        obtain ⟨_, hinp, _, _, _⟩ := ao2_gate_spec (n + m) D hAO g hg_lt
        rw [hinp] at hg_in
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg_in
        have hg_top : g ∈ TopOR :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg_lt, hg_or, hrest⟩
        rcases hg_in with h0 | h1
        · exact ⟨(g, 0), Finset.mem_product.mpr ⟨hg_top, Finset.mem_univ _⟩, h0.symm⟩
        · exact ⟨(g, 1), Finset.mem_product.mpr ⟨hg_top, Finset.mem_univ _⟩, h1.symm⟩
    let phi : ℕ → ℕ × Fin 2 := fun j =>
      if h : j ∈ (S_AND ∪ TopOR).erase out then Classical.choose (hstep_exists j h) else (0, 0)
    have hcard_le : ((S_AND ∪ TopOR).erase out).card ≤ (TopOR ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      apply Finset.card_le_card_of_injOn phi
      · intro j hj
        have hj' : j ∈ (S_AND ∪ TopOR).erase out := Finset.mem_coe.mp hj
        simp only [phi, hj', ↓reduceDIte]
        exact Finset.mem_coe.mpr (Classical.choose_spec (hstep_exists j hj')).1
      · intro j1 hj1 j2 hj2 heq
        have hj1' : j1 ∈ (S_AND ∪ TopOR).erase out := Finset.mem_coe.mp hj1
        have hj2' : j2 ∈ (S_AND ∪ TopOR).erase out := Finset.mem_coe.mp hj2
        simp only [phi, hj1', hj2', ↓reduceDIte] at heq
        have h1 := (Classical.choose_spec (hstep_exists j1 hj1')).2
        have h2 := (Classical.choose_spec (hstep_exists j2 hj2')).2
        rw [heq] at h1
        have hsum : n + m + j1 = n + m + j2 := h1.symm.trans h2
        omega
    rw [Finset.card_erase_of_mem hout_mem, Finset.card_union_of_disjoint hDisj_AT,
      Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard_le
    have hpos : 1 ≤ S_AND.card + TopOR.card := by
      have := Finset.one_le_card.mpr ⟨out, hout_mem⟩
      rwa [Finset.card_union_of_disjoint hDisj_AT] at this
    omega
  -- Trace any true wire on OrPath back to an AND gate in S_AND
  have trace_to_and : ∀ (z : Fin (n + m) → Bool) (w : ℕ),
      OrPath n m D w D.output → wval (n + m) D z w = true →
      ∃ j ∈ S_AND, wval (n + m) D z (n + m + j) = true := by
    intro z w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hpath hw
      by_cases hlt : w < n + m
      · exact (not_orPath_lt w hlt hpath).elim
      by_cases hge : n + m + D.size ≤ w
      · rw [wval_ge (n + m) D z w hge] at hw; cases hw
      let j := w - (n + m)
      have hj : j < D.size := by omega
      have hwj : w = n + m + j := by omega
      rw [hwj] at hpath hw
      obtain ⟨hop, hinp, ha_lt, hb_lt, hev⟩ := ao2_gate_spec (n + m) D hAO j hj
      rcases hop with hand | hor
      · exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hand, hpath⟩, hw⟩
      · rw [hev z, hor, eval_or, Bool.or_eq_true] at hw
        rcases hw with ha | hb
        · have hstep : OrStep n m D (opnd D j 0) (n + m + j) :=
            ⟨j, hj, rfl, hor, by rw [hinp]; simp⟩
          exact ih (opnd D j 0) (by omega) (Relation.ReflTransGen.head hstep hpath) ha
        · have hstep : OrStep n m D (opnd D j 1) (n + m + j) :=
            ⟨j, hj, rfl, hor, by rw [hinp]; simp⟩
          exact ih (opnd D j 1) (by omega) (Relation.ReflTransGen.head hstep hpath) hb
  -- Analyze every AND gate j ∈ S_AND: pure-point side vs pure-line side, and star property
  have and_star : ∀ j ∈ S_AND,
      ∃ (c : Fin n ⊕ Fin m) (r : ℕ),
        r ∈ U ∧ r < k ∧
        (match c with
         | Sum.inl p => wirePts n m D r = ∅ ∧ (∀ l ∈ wireLines n m D r, (p, l) ∈ E) ∧
             (∀ p' l', wval (n + m) D (fun i => decide (i = Fin.castAdd m p' ∨ i = Fin.natAdd n l')) (n + m + j) = true →
               p' = p ∧ l' ∈ wireLines n m D r)
         | Sum.inr l => wireLines n m D r = ∅ ∧ (∀ p ∈ wirePts n m D r, (p, l) ∈ E) ∧
             (∀ p' l', wval (n + m) D (fun i => decide (i = Fin.castAdd m p' ∨ i = Fin.natAdd n l')) (n + m + j) = true →
               l' = l ∧ p' ∈ wirePts n m D r)) := by
    intro j hj
    have hj_lt : j < D.size := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_and : (gateAt D j).op = GateOp.and := (Finset.mem_filter.mp hj).2.1
    have hj_path : OrPath n m D (n + m + j) D.output := (Finset.mem_filter.mp hj).2.2
    obtain ⟨_, hinp, hu_lt, hv_lt, hev⟩ := ao2_gate_spec (n + m) D hAO j hj_lt
    let u := opnd D j 0
    let v := opnd D j 1
    have huU : u ∈ U := hAndU j hj_lt hj_and u (by rw [hinp]; simp [u])
    have hvU : v ∈ U := hAndU j hj_lt hj_and v (by rw [hinp]; simp [v])
    obtain ⟨hu_ev, hu_ne⟩ := wval_mem_U n m D U hAO hU u huU
    obtain ⟨hv_ev, hv_ne⟩ := wval_mem_U n m D U hAO hU v hvU
    have hev_and : ∀ z : Fin (n + m) → Bool,
        wval (n + m) D z (n + m + j) = true ↔ wval (n + m) D z u = true ∧ wval (n + m) D z v = true := by
      intro z; rw [hev z, hj_and, eval_and, Bool.and_eq_true]
    have hno_both_pts : wirePts n m D u = ∅ ∨ wirePts n m D v = ∅ := by
      by_contra h
      push Not at h
      obtain ⟨p1, hp1⟩ := h.1
      obtain ⟨p2, hp2⟩ := h.2
      let z : Fin (n + m) → Bool := fun i => decide (i = Fin.castAdd m p1 ∨ i = Fin.castAdd m p2)
      have hwu : wval (n + m) D z u = true := (hu_ev z).mpr (Or.inl ⟨p1, hp1, by simp [z]⟩)
      have hwv : wval (n + m) D z v = true := (hv_ev z).mpr (Or.inl ⟨p2, hp2, by simp [z]⟩)
      have hwj : wval (n + m) D z (n + m + j) = true := (hev_and z).mpr ⟨hwu, hwv⟩
      have hout : circuitFun (n + m) D z = true := orPath_sound n m D hAO z hj_path hwj
      have hfalse : circuitFun (n + m) D z = false := by
        apply eval_false_pts
        intro l
        simp only [z, decide_eq_false_iff_not, not_or]
        constructor <;> intro heq <;> have hval := congrArg Fin.val heq <;> simp at hval <;> omega
      rw [hfalse] at hout; cases hout
    have hno_both_lines : wireLines n m D u = ∅ ∨ wireLines n m D v = ∅ := by
      by_contra h
      push Not at h
      obtain ⟨l1, hl1⟩ := h.1
      obtain ⟨l2, hl2⟩ := h.2
      let z : Fin (n + m) → Bool := fun i => decide (i = Fin.natAdd n l1 ∨ i = Fin.natAdd n l2)
      have hwu : wval (n + m) D z u = true := (hu_ev z).mpr (Or.inr ⟨l1, hl1, by simp [z]⟩)
      have hwv : wval (n + m) D z v = true := (hv_ev z).mpr (Or.inr ⟨l2, hl2, by simp [z]⟩)
      have hwj : wval (n + m) D z (n + m + j) = true := (hev_and z).mpr ⟨hwu, hwv⟩
      have hout : circuitFun (n + m) D z = true := orPath_sound n m D hAO z hj_path hwj
      have hfalse : circuitFun (n + m) D z = false := by
        apply eval_false_lines
        intro p
        simp only [z, decide_eq_false_iff_not, not_or]
        constructor <;> intro heq <;> have hval := congrArg Fin.val heq <;> simp at hval <;> omega
      rw [hfalse] at hout; cases hout
    -- Extract pure point wire pw and pure line wire lw
    have hsplit : ∃ (pw lw : ℕ),
        ((pw = u ∧ lw = v) ∨ (pw = v ∧ lw = u)) ∧
        wireLines n m D pw = ∅ ∧ (wirePts n m D pw).Nonempty ∧
        wirePts n m D lw = ∅ ∧ (wireLines n m D lw).Nonempty := by
      rcases hu_ne with hup | hul
      · have hvp : wirePts n m D v = ∅ := hno_both_pts.resolve_left (Finset.nonempty_iff_ne_empty.mp hup)
        have hvl : (wireLines n m D v).Nonempty := hv_ne.resolve_left (by simp [hvp])
        have hul0 : wireLines n m D u = ∅ := hno_both_lines.resolve_right (Finset.nonempty_iff_ne_empty.mp hvl)
        exact ⟨u, v, Or.inl ⟨rfl, rfl⟩, hul0, hup, hvp, hvl⟩
      · have hvl : wireLines n m D v = ∅ := hno_both_lines.resolve_left (Finset.nonempty_iff_ne_empty.mp hul)
        have hvp : (wirePts n m D v).Nonempty := hv_ne.resolve_right (by simp [hvl])
        have hup0 : wirePts n m D u = ∅ := hno_both_pts.resolve_right (Finset.nonempty_iff_ne_empty.mp hvp)
        exact ⟨v, u, Or.inr ⟨rfl, rfl⟩, hvl, hvp, hup0, hul⟩
    obtain ⟨pw, lw, hor_uv, hpwL, hpwP, hlwP, hlwL⟩ := hsplit
    have hpwU : pw ∈ U := by rcases hor_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hlwU : lw ∈ U := by rcases hor_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hpw_lt : pw < k := by rcases hor_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    have hlw_lt : lw < k := by rcases hor_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    have hev_pair : ∀ (p' : Fin n) (l' : Fin m),
        let z : Fin (n + m) → Bool := fun i => decide (i = Fin.castAdd m p' ∨ i = Fin.natAdd n l')
        wval (n + m) D z (n + m + j) = true ↔ p' ∈ wirePts n m D pw ∧ l' ∈ wireLines n m D lw := by
      intro p' l' z
      have hpw_ev := (wval_mem_U n m D U hAO hU pw hpwU).1 z
      have hlw_ev := (wval_mem_U n m D U hAO hU lw hlwU).1 z
      have hp_iff : wval (n + m) D z pw = true ↔ p' ∈ wirePts n m D pw := by
        rw [hpw_ev, hpwL]
        simp only [Finset.notMem_empty, false_and, exists_false, or_false]
        constructor
        · rintro ⟨p, hp, hzp⟩
          simp only [z, decide_eq_true_eq] at hzp
          rcases hzp with heq | heq
          · have : p = p' := Fin.ext (by simpa using congrArg Fin.val heq)
            rwa [← this]
          · have hval := congrArg Fin.val heq; simp at hval; omega
        · intro hp'; exact ⟨p', hp', by simp [z]⟩
      have hl_iff : wval (n + m) D z lw = true ↔ l' ∈ wireLines n m D lw := by
        rw [hlw_ev, hlwP]
        simp only [Finset.notMem_empty, false_and, exists_false, false_or]
        constructor
        · rintro ⟨l, hl, hzl⟩
          simp only [z, decide_eq_true_eq] at hzl
          rcases hzl with heq | heq
          · have hval := congrArg Fin.val heq; simp at hval; omega
          · have : l = l' := Fin.ext (by simpa using congrArg Fin.val heq)
            rwa [← this]
        · intro hl'; exact ⟨l', hl', by simp [z]⟩
      rw [hev_and z]
      rcases hor_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact and_congr hp_iff hl_iff
      · rw [and_comm]; exact and_congr hp_iff hl_iff
    have hbiclique : ∀ p ∈ wirePts n m D pw, ∀ l ∈ wireLines n m D lw, (p, l) ∈ E := by
      intro p hp l hl
      let z : Fin (n + m) → Bool := fun i => decide (i = Fin.castAdd m p ∨ i = Fin.natAdd n l)
      have hwj : wval (n + m) D z (n + m + j) = true := (hev_pair p l).mpr ⟨hp, hl⟩
      have hout : circuitFun (n + m) D z = true := orPath_sound n m D hAO z hj_path hwj
      rw [hEval z, decide_eq_true_eq] at hout
      obtain ⟨p', l', he', hp', hl'⟩ := hout
      simp only [z, decide_eq_true_eq] at hp' hl'
      have hp_eq : p' = p := by
        rcases hp' with h | h
        · exact Fin.ext (by simpa using congrArg Fin.val h)
        · have hv := congrArg Fin.val h; simp at hv; omega
      have hl_eq : l' = l := by
        rcases hl' with h | h
        · have hv := congrArg Fin.val h; simp at hv; omega
        · exact Fin.ext (by simpa using congrArg Fin.val h)
      rwa [← hp_eq, ← hl_eq]
    -- By C4-freeness, either |wirePts pw| ≤ 1 or |wireLines lw| ≤ 1
    have hstar : (wirePts n m D pw).card ≤ 1 ∨ (wireLines n m D lw).card ≤ 1 := by
      by_contra h
      push Not at h
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := exists_two_of_two_le_card h.1
      obtain ⟨l1, hl1, l2, hl2, hlne⟩ := exists_two_of_two_le_card h.2
      exact hC4 p1 p2 l1 l2 hpne hlne
        ⟨hbiclique p1 hp1 l1 hl1, hbiclique p1 hp1 l2 hl2,
         hbiclique p2 hp2 l1 hl1, hbiclique p2 hp2 l2 hl2⟩
    rcases hstar with hple | hlle
    · obtain ⟨p0, hp0⟩ := hpwP
      have huniq : ∀ p ∈ wirePts n m D pw, p = p0 := by
        intro p hp
        exact Finset.card_le_one.mp hple p hp p0 hp0
      refine ⟨Sum.inl p0, lw, hlwU, hlw_lt, hlwP, fun l hl => hbiclique p0 hp0 l hl, ?_⟩
      intro p' l' hw
      obtain ⟨hp', hl'⟩ := (hev_pair p' l').mp hw
      exact ⟨huniq p' hp', hl'⟩
    · obtain ⟨l0, hl0⟩ := hlwL
      have huniq : ∀ l ∈ wireLines n m D lw, l = l0 := by
        intro l hl
        exact Finset.card_le_one.mp hlle l hl l0 hl0
      refine ⟨Sum.inr l0, pw, hpwU, hpw_lt, hpwL, fun p hp => hbiclique p hp l0 hl0, ?_⟩
      intro p' l' hw
      obtain ⟨hp', hl'⟩ := (hev_pair p' l').mp hw
      exact ⟨huniq l' hl', hp'⟩
  -- Choose center(j) and rootWire(j) for each j ∈ S_AND
  let center : ℕ → Fin n ⊕ Fin m := fun j =>
    if h : j ∈ S_AND then Classical.choose (and_star j h) else Sum.inl ⟨0, by
      obtain ⟨⟨p0, _⟩, _⟩ := hEne; exact p0.pos⟩
  let rootWire : ℕ → ℕ := fun j =>
    if h : j ∈ S_AND then Classical.choose (Classical.choose_spec (and_star j h)) else 0
  have hcr_spec : ∀ j (hj : j ∈ S_AND),
      rootWire j ∈ U ∧ rootWire j < k ∧
      (match center j with
       | Sum.inl p => wirePts n m D (rootWire j) = ∅ ∧
           (∀ l ∈ wireLines n m D (rootWire j), (p, l) ∈ E) ∧
           (∀ p' l', wval (n + m) D (fun i => decide (i = Fin.castAdd m p' ∨ i = Fin.natAdd n l')) (n + m + j) = true →
             p' = p ∧ l' ∈ wireLines n m D (rootWire j))
       | Sum.inr l => wireLines n m D (rootWire j) = ∅ ∧
           (∀ p ∈ wirePts n m D (rootWire j), (p, l) ∈ E) ∧
           (∀ p' l', wval (n + m) D (fun i => decide (i = Fin.castAdd m p' ∨ i = Fin.natAdd n l')) (n + m + j) = true →
             l' = l ∧ p' ∈ wirePts n m D (rootWire j))) := by
    intro j hj
    simp only [center, rootWire, hj, ↓reduceDIte]
    exact Classical.choose_spec (Classical.choose_spec (and_star j hj))
  -- Build A, R, inCone, F, T, a, b, t
  let A : Finset (Fin n ⊕ Fin m) := S_AND.image center
  let R : Fin n ⊕ Fin m → Finset ℕ := fun c => (S_AND.filter fun j => center j = c).image rootWire
  let inCone : Fin n ⊕ Fin m → ℕ → Prop := fun c x => ∃ r ∈ R c, OrPath n m D x r
  let F : Fin n ⊕ Fin m → ℕ → Finset (Fin n × Fin m) := fun c x =>
    if inCone c x then
      match c with
      | Sum.inl p => (wireLines n m D x).image fun l => (p, l)
      | Sum.inr l => (wirePts n m D x).image fun p => (p, l)
    else ∅
  let T : Fin n ⊕ Fin m → Finset ℕ := fun c =>
    (Finset.range k).filter fun x => n + m ≤ x ∧ inCone c x ∧ 2 ≤ (F c x).card
  let aFn : ℕ → ℕ := fun x => opnd D (x - (n + m)) 0
  let bFn : ℕ → ℕ := fun x => opnd D (x - (n + m)) 1
  -- Properties of R c
  have hR_spec : ∀ c r, r ∈ R c →
      r ∈ U ∧ r < k ∧
      (match c with
       | Sum.inl p => wirePts n m D r = ∅ ∧ ∀ l ∈ wireLines n m D r, (p, l) ∈ E
       | Sum.inr l => wireLines n m D r = ∅ ∧ ∀ p ∈ wirePts n m D r, (p, l) ∈ E) := by
    intro c r hr
    obtain ⟨j, hjf, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hj, hcj⟩ := Finset.mem_filter.mp hjf
    have hs := hcr_spec j hj
    rw [hcj] at hs
    refine ⟨hs.1, hs.2.1, ?_⟩
    cases c with
    | inl p => exact ⟨hs.2.2.1, hs.2.2.2.1⟩
    | inr l => exact ⟨hs.2.2.1, hs.2.2.2.1⟩
  -- Pairwise disjointness of T c for distinct c ∈ A
  have hT_disj : Set.PairwiseDisjoint (A : Set (Fin n ⊕ Fin m)) T := by
    intro c1 hc1 c2 hc2 hne
    change Disjoint (T c1) (T c2)
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    obtain ⟨r1, hr1, hp1⟩ := h1.2.1
    obtain ⟨r2, hr2, hp2⟩ := h2.2.1
    obtain ⟨hr1U, _, hr1_prop⟩ := hR_spec c1 r1 hr1
    obtain ⟨hr2U, _, hr2_prop⟩ := hR_spec c2 r2 hr2
    obtain ⟨_, hsubP1, hsubL1⟩ := orPath_U_closed n m D U hAO hU hp1 hr1U
    obtain ⟨_, hsubP2, hsubL2⟩ := orPath_U_closed n m D U hAO hU hp2 hr2U
    cases c1 with
    | inl p1 =>
      cases c2 with
      | inl p2 =>
        have hpne : p1 ≠ p2 := fun h => hne (congrArg Sum.inl h)
        have hcL : 2 ≤ (wireLines n m D x).card := by
          have hcard := h1.2.2
          simp only [F, h1.2.1, ↓reduceIte] at hcard
          exact hcard.trans Finset.card_image_le
        obtain ⟨l1, hl1, l2, hl2, hlne⟩ := exists_two_of_two_le_card hcL
        exact hC4 p1 p2 l1 l2 hpne hlne
          ⟨hr1_prop.2 l1 (hsubL1 hl1), hr1_prop.2 l2 (hsubL1 hl2),
           hr2_prop.2 l1 (hsubL2 hl1), hr2_prop.2 l2 (hsubL2 hl2)⟩
      | inr l2 =>
        have hPempty : wirePts n m D x = ∅ :=
          Finset.subset_empty.mp (hsubP1.trans (by rw [hr1_prop.1]))
        have hcard := h2.2.2
        simp only [F, h2.2.1, ↓reduceIte, hPempty, Finset.image_empty, Finset.card_empty] at hcard
        omega
    | inr l1 =>
      cases c2 with
      | inl p2 =>
        have hLempty : wireLines n m D x = ∅ :=
          Finset.subset_empty.mp (hsubL1.trans (by rw [hr1_prop.1]))
        have hcard := h2.2.2
        simp only [F, h2.2.1, ↓reduceIte, hLempty, Finset.image_empty, Finset.card_empty] at hcard
        omega
      | inr l2 =>
        have hlne : l1 ≠ l2 := fun h => hne (congrArg Sum.inr h)
        have hcP : 2 ≤ (wirePts n m D x).card := by
          have hcard := h1.2.2
          simp only [F, h1.2.1, ↓reduceIte] at hcard
          exact hcard.trans Finset.card_image_le
        obtain ⟨p1, hp1, p2, hp2, hpne⟩ := exists_two_of_two_le_card hcP
        exact hC4 p1 p2 l1 l2 hpne hlne
          ⟨hr1_prop.2 p1 (hsubP1 hp1), hr2_prop.2 p1 (hsubP2 hp1),
           hr1_prop.2 p2 (hsubP1 hp2), hr2_prop.2 p2 (hsubP2 hp2)⟩
  -- Sum of T cards ≤ U_gates.card
  have hT_sum : ∑ c ∈ A, (T c).card ≤ U_gates.card := by
    rw [← Finset.card_biUnion hT_disj]
    apply Finset.card_le_card_of_injOn (fun x => x - (n + m))
    · intro x hx
      dsimp only
      obtain ⟨c, _, hxT⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
      have hxr : x < n + m + D.size := Finset.mem_range.mp (Finset.mem_filter.mp hxT).1
      have hge := (Finset.mem_filter.mp hxT).2.1
      obtain ⟨r, hr, hpath⟩ := (Finset.mem_filter.mp hxT).2.2.1
      have hrU := (hR_spec c r hr).1
      have hxU := (orPath_U_closed n m D U hAO hU hpath hrU).1
      have hsub_eq : n + m + (x - (n + m)) = x := by omega
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rwa [hsub_eq]⟩)
    · intro x1 hx1 x2 hx2 heq
      dsimp only at heq
      obtain ⟨_, _, hx1T⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx1)
      obtain ⟨_, _, hx2T⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx2)
      have h1 := (Finset.mem_filter.mp hx1T).2.1
      have h2 := (Finset.mem_filter.mp hx2T).2.1
      omega
  -- Assemble all conjuncts
  refine ⟨A, R, T, F, aFn, bFn, S_AND.card, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Cover every e ∈ E
    intro ⟨p, l⟩ he
    let z : Fin (n + m) → Bool := fun i => decide (i = Fin.castAdd m p ∨ i = Fin.natAdd n l)
    have hout : circuitFun (n + m) D z = true := by
      rw [hEval z, decide_eq_true_eq]
      exact ⟨p, l, he, by simp [z], by simp [z]⟩
    obtain ⟨j, hj, hwj⟩ := trace_to_and z D.output Relation.ReflTransGen.refl hout
    refine ⟨center j, Finset.mem_image_of_mem center hj, ?_⟩
    apply Finset.mem_biUnion.mpr
    have hr_mem : rootWire j ∈ R (center j) :=
      Finset.mem_image_of_mem rootWire (Finset.mem_filter.mpr ⟨hj, rfl⟩)
    refine ⟨rootWire j, hr_mem, ?_⟩
    have hin : inCone (center j) (rootWire j) := ⟨rootWire j, hr_mem, Relation.ReflTransGen.refl⟩
    have hs := (hcr_spec j hj).2.2
    simp only [F, hin, ↓reduceIte]
    cases hc : center j with
    | inl p0 =>
      rw [hc] at hs
      obtain ⟨rfl, hl_mem⟩ := hs.2.2 p l hwj
      exact Finset.mem_image_of_mem _ hl_mem
    | inr l0 =>
      rw [hc] at hs
      obtain ⟨rfl, hp_mem⟩ := hs.2.2 p l hwj
      exact Finset.mem_image_of_mem _ hp_mem
  · -- Star property
    intro c _ e he
    obtain ⟨r, _, hfe⟩ := Finset.mem_biUnion.mp he
    simp only [F] at hfe
    split_ifs at hfe with hin
    · cases c with
      | inl p =>
        obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hfe
        exact Or.inl rfl
      | inr l =>
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hfe
        exact Or.inr rfl
    · simp at hfe
  · -- Local certificate for each c ∈ A
    intro c _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      exact Finset.mem_range.mpr (hR_spec c r hr).2.1
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro x hxk hxT
      by_cases hin : inCone c x
      · by_cases hlt : x < n + m
        · simp only [F, hin, ↓reduceIte]
          cases c with
          | inl p => exact Finset.card_image_le.trans (card_le_one_input_lines n m D x hlt)
          | inr l => exact Finset.card_image_le.trans (card_le_one_input_pts n m D x hlt)
        · have hge : n + m ≤ x := by omega
          by_contra hnot
          have h2 : 2 ≤ (F c x).card := by omega
          exact hxT (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxk, hge, hin, h2⟩)
      · simp [F, hin]
    · intro x hxT
      have hxk : x < k := Finset.mem_range.mp (Finset.mem_filter.mp hxT).1
      have hge : n + m ≤ x := (Finset.mem_filter.mp hxT).2.1
      have hin : inCone c x := (Finset.mem_filter.mp hxT).2.2.1
      have ⟨r, hr, hpath⟩ := hin
      have hrU : r ∈ U := (hR_spec c r hr).1
      have hxU : x ∈ U := (orPath_U_closed n m D U hAO hU hpath hrU).1
      rcases hU x hxU with hlt | ⟨j, hj, hxj, hor, _⟩
      · omega
      have hsub_j : x - (n + m) = j := by omega
      obtain ⟨_, hinp, ha_lt, hb_lt, _⟩ := ao2_gate_spec (n + m) D hAO j hj
      have ha_eq : aFn x = opnd D j 0 := by simp [aFn, hsub_j]
      have hb_eq : bFn x = opnd D j 1 := by simp [bFn, hsub_j]
      have ha_in : inCone c (aFn x) := by
        refine ⟨r, hr, Relation.ReflTransGen.head ?_ hpath⟩
        exact ⟨j, hj, hxj, hor, by rw [ha_eq, hinp]; simp⟩
      have hb_in : inCone c (bFn x) := by
        refine ⟨r, hr, Relation.ReflTransGen.head ?_ hpath⟩
        exact ⟨j, hj, hxj, hor, by rw [hb_eq, hinp]; simp⟩
      refine ⟨by omega, by omega, ?_⟩
      simp only [F, hin, ha_in, hb_in, ↓reduceIte]
      cases c with
      | inl p =>
        dsimp only
        rw [ha_eq, hb_eq, hxj, wireLines_or_gate n m D hAO j hj hor, Finset.image_union]
      | inr l =>
        dsimp only
        rw [ha_eq, hb_eq, hxj, wirePts_or_gate n m D hAO j hj hor, Finset.image_union]
  · -- A.card ≤ S_AND.card
    exact Finset.card_image_le
  · -- ∑ c ∈ A, (R c).card ≤ S_AND.card
    calc
      ∑ c ∈ A, (R c).card ≤ ∑ c ∈ A, (S_AND.filter fun j => center j = c).card := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le
      _ = S_AND.card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext j
          simp only [Finset.mem_biUnion, Finset.mem_filter, A, Finset.mem_image]
          constructor
          · rintro ⟨_, _, hj, _⟩; exact hj
          · intro hj; exact ⟨center j, ⟨j, hj, rfl⟩, hj, rfl⟩
        · intro c1 _ c2 _ hne
          change Disjoint (S_AND.filter fun j => center j = c1) (S_AND.filter fun j => center j = c2)
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          have h1 := (Finset.mem_filter.mp hj1).2
          have h2 := (Finset.mem_filter.mp hj2).2
          exact hne (h1.symm.trans h2)
  · -- 2 * S_AND.card + ∑ c ∈ A, (T c).card ≤ D.size + 1
    omega

end PEqualNP.Outside.L_meta_5761

theorem PEqualNP.Outside.L_meta_5761 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ),   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →         have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x4;         (∀ x10 ∈ x5, x10 < x1 + x2 ∨ ∃ x12 < x4.size, x10 = x1 + x2 + x12 ∧ (x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x9 x12).inputs, x13 ∈ x5) →           (∀ x11 < x4.size, (x9 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x14 ∈ (x9 x11).inputs, x14 ∈ x5) →             have x12 : ℕ := x1 + x2 + x4.size;             ∃ (x13 : Finset (Fin x1 ⊕ Fin x2)) (x14 : Fin x1 ⊕ Fin x2 → Finset ℕ) (x15 : Fin x1 ⊕ Fin x2 → Finset ℕ) (x16 : Fin x1 ⊕ Fin x2 → ℕ → Finset (Fin x1 × Fin x2)) (x17 : ℕ → ℕ) (x18 : ℕ → ℕ) (x19 : ℕ),               have x20 : Fin x1 ⊕ Fin x2 → Finset (Fin x1 × Fin x2) := fun (x20 : Fin x1 ⊕ Fin x2) => (x14 x20).biUnion (x16 x20);               (∀ x21 ∈ x3, ∃ x23 ∈ x13, x21 ∈ x20 x23) ∧ (∀ x21 ∈ x13, ∀ x23 ∈ x20 x21, x21 = Sum.inl x23.1 ∨ x21 = Sum.inr x23.2) ∧ (∀ x21 ∈ x13, x14 x21 ⊆ Finset.range x12 ∧ x15 x21 ⊆ Finset.range x12 ∧ (∀ x23 < x12, x23 ∉ x15 x21 → (x16 x21 x23).card ≤ (1 : ℕ)) ∧ ∀ x23 ∈ x15 x21, x17 x23 < x23 ∧ x18 x23 < x23 ∧ x16 x21 x23 = x16 x21 (x17 x23) ∪ x16 x21 (x18 x23)) ∧ x13.card ≤ x19 ∧ ∑ x21 ∈ x13, (x14 x21).card ≤ x19 ∧ (2 : ℕ) * x19 + ∑ x21 ∈ x13, (x15 x21).card ≤ x4.size + (1 : ℕ) := by
  exact PEqualNP.Outside.L_meta_5761.main
