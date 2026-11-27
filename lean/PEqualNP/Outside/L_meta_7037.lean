import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7037
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

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

def prodF {n : ℕ} (A B : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  A.biUnion fun a => B.image fun b => a ∪ b

def DD (n : ℕ) (C : Circuit) : ℕ → Finset (Finset (Fin n)) :=
  WellFounded.fix Nat.lt_wfRel.wf (fun w rec =>
    if h : w < n then {{⟨w, h⟩}}
    else match C.gates[w - n]? with
      | none => ∅
      | some g => match g.inputs with
        | [a, b] => if hab : a < w ∧ b < w then
            (if g.op.eval [false, true] = true then rec a hab.1 ∪ rec b hab.2
             else prodF (rec a hab.1) (rec b hab.2))
          else ∅
        | _ => ∅)

theorem DD_eq (n : ℕ) (C : Circuit) (w : ℕ) : DD n C w =
    (if h : w < n then {{⟨w, h⟩}}
    else match C.gates[w - n]? with
      | none => ∅
      | some g => match g.inputs with
        | [a, b] => if hab : a < w ∧ b < w then
            (if g.op.eval [false, true] = true then DD n C a ∪ DD n C b
             else prodF (DD n C a) (DD n C b))
          else ∅
        | _ => ∅) := by
  unfold DD
  rw [WellFounded.fix_eq]

theorem DD_gate (n : ℕ) (C : Circuit) (j a b : ℕ) (hjl : j < C.gates.length)
    (hab : C.gates[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    DD n C (n + j) = if C.gates[j].op.eval [false, true] = true then DD n C a ∪ DD n C b
      else prodF (DD n C a) (DD n C b) := by
  rw [DD_eq, dif_neg (by omega)]
  have e : C.gates[n + j - n]? = some C.gates[j] := by
    rw [Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hjl
  rw [e]
  simp only [hab]
  rw [dif_pos ⟨ha, hb⟩]

end PEqualNP.Outside.L_meta_7037

open PEqualNP.Outside.L_meta_7037 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7037 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then x5 x8 ∪ x5 x9 else (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9)) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∃ x9 ∈ x5 x8, ∀ x10 ∈ x9, x6.getD (↑x10) Bool.false = Bool.true := by
  intro n C hm hrb
  refine ⟨DD n C, ?_, ?_, ?_⟩
  · intro i
    rw [DD_eq, dif_pos i.isLt]
  · intro j hj
    have hjl : j < C.gates.length := hj
    obtain ⟨a, b, hab, halt, hblt⟩ := hrb j C.gates[j] (List.getElem?_eq_getElem hjl)
    refine ⟨a, b, hab, halt, hblt, ?_⟩
    exact DD_gate n C j a b hjl hab (by omega) hblt
  · intro x hx w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      show (wf C.gates x).getD w false = true ↔ _
      by_cases hw : w < n
      · rw [DD_eq, dif_pos hw, wf_keep _ _ _ (by omega)]
        simp
      · by_cases hj : w - n < C.gates.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hjl : j < C.gates.length := by omega
          obtain ⟨a, b, hab, halt, hblt⟩ := hrb j C.gates[j] (List.getElem?_eq_getElem hjl)
          have hval : (wf C.gates x).getD (n + j) false
              = C.gates[j].op.eval [(wf C.gates x).getD a false, (wf C.gates x).getD b false] := by
            have h := gate_full C.gates x j hjl (by
              intro i hi
              rw [hab] at hi
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              omega)
            rw [hx, hab] at h
            simpa using h
          have iha : (wf C.gates x).getD a false = true ↔
              ∃ t ∈ DD n C a, ∀ i ∈ t, x.getD (i : ℕ) false = true := ih a (by omega)
          have ihb : (wf C.gates x).getD b false = true ↔
              ∃ t ∈ DD n C b, ∀ i ∈ t, x.getD (i : ℕ) false = true := ih b (by omega)
          rw [DD_gate n C j a b hjl hab (by omega) hblt, hval]
          rcases (hm _ (List.getElem_mem hjl)).1 with hop | hop
          · have hop' : C.gates[j].op = GateOp.and := hop
            rw [hop', if_neg (by simp [GateOp.eval])]
            constructor
            · intro h
              have h' : (wf C.gates x).getD a false = true ∧ (wf C.gates x).getD b false = true := by
                simpa [GateOp.eval] using h
              obtain ⟨ta, hta, hat⟩ := iha.1 h'.1
              obtain ⟨tb, htb, hbt⟩ := ihb.1 h'.2
              exact ⟨ta ∪ tb, Finset.mem_biUnion.2 ⟨ta, hta, Finset.mem_image.2 ⟨tb, htb, rfl⟩⟩,
                fun i hi => (Finset.mem_union.1 hi).elim (hat i) (hbt i)⟩
            · rintro ⟨t, ht, hall⟩
              obtain ⟨ta, hta, ht'⟩ := Finset.mem_biUnion.1 ht
              obtain ⟨tb, htb, rfl⟩ := Finset.mem_image.1 ht'
              have ha := iha.2 ⟨ta, hta, fun i hi => hall i (Finset.mem_union_left _ hi)⟩
              have hb := ihb.2 ⟨tb, htb, fun i hi => hall i (Finset.mem_union_right _ hi)⟩
              rw [ha, hb]
              rfl
          · have hop' : C.gates[j].op = GateOp.or := hop
            rw [hop', if_pos (by simp [GateOp.eval])]
            constructor
            · intro h
              have h' : (wf C.gates x).getD a false = true ∨ (wf C.gates x).getD b false = true := by
                simpa [GateOp.eval] using h
              rcases h' with h1 | h1
              · obtain ⟨t, ht, hall⟩ := iha.1 h1
                exact ⟨t, Finset.mem_union_left _ ht, hall⟩
              · obtain ⟨t, ht, hall⟩ := ihb.1 h1
                exact ⟨t, Finset.mem_union_right _ ht, hall⟩
            · rintro ⟨t, ht, hall⟩
              rcases Finset.mem_union.1 ht with h1 | h1
              · have h2 := iha.2 ⟨t, h1, hall⟩
                rw [h2]
                simp [GateOp.eval]
              · have h2 := ihb.2 ⟨t, h1, hall⟩
                rw [h2]
                simp [GateOp.eval]
        · rw [DD_eq, dif_neg hw]
          have e : C.gates[w - n]? = none := List.getElem?_eq_none (by omega)
          rw [e, List.getD_eq_default _ _ (by rw [wf_len]; omega)]
          simp
