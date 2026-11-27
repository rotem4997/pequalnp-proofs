import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1837

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

theorem cf_mono_fn {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n C y = true :=
  eval_mono_fn C.gates (fun g hg' => (hg g hg').1) x y hxy C.output h

theorem off {N : ℕ} (T B : Finset (Fin N)) (hB : ∀ t ∈ B, t ∉ T) (t : Fin N) :
    (if t ∈ T then false else decide (t ∈ B)) = decide (t ∈ B) := by
  by_cases h : t ∈ T
  · rw [if_pos h]
    exact (decide_eq_false (fun hb => hB t hb h)).symm
  · rw [if_neg h]

theorem mix {N : ℕ} (T B Z U : Finset (Fin N)) (hZ : Z ⊆ T) (hB : ∀ t ∈ B, t ∉ T)
    (hU : ∀ t, t ∈ U ↔ t ∈ Z ∨ t ∈ B) (t : Fin N) :
    (if t ∈ T then decide (t ∈ Z) else decide (t ∈ B)) = decide (t ∈ U) := by
  by_cases h : t ∈ T
  · rw [if_pos h]
    have hb : t ∉ B := fun hb => hB t hb h
    exact decide_eq_decide.mpr ⟨fun hz => (hU t).mpr (Or.inl hz), fun hu => ((hU t).mp hu).resolve_right hb⟩
  · rw [if_neg h]
    have hz : t ∉ Z := fun hz => h (hZ hz)
    exact decide_eq_decide.mpr ⟨fun hb => (hU t).mpr (Or.inr hb), fun hu => ((hU t).mp hu).resolve_left hz⟩

theorem up {N : ℕ} (T B : Finset (Fin N)) (a : Fin N) (ha : a ∈ T) (t : Fin N)
    (h : decide (t ∈ ({a} : Finset (Fin N))) = true) :
    (if t ∈ T then decide (t ∈ ({a} : Finset (Fin N))) else decide (t ∈ B)) = true := by
  have ht : t = a := Finset.mem_singleton.mp (of_decide_eq_true h)
  rw [ht, if_pos ha]
  exact decide_eq_true (Finset.mem_singleton.mpr rfl)

end PEqualNP.Outside.L_meta_1837

open PEqualNP.Outside.L_meta_1837 in
theorem PEqualNP.Outside.L_meta_1837 : (∀ (Nlv15 mlv15 : ℕ) (Clv15 : PEqualNP.CircuitLowerBounds.Circuit) (Slv15 Wlv15 : Finset (Fin Nlv15)) (pilv15 nulv15 : Fin Nlv15 → Bool) (sglv15 : ℕ → Fin 2), ((∀ glv15 ∈ Clv15.gates, (glv15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Clv15) → Set.ncard {jlv15 : ℕ | jlv15 < Clv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15 0 = 0) ∨ (∀ hlv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15 0 = 0))} ≤ mlv15 + 1 → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15x1 : Fin Clv15.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x1 0 = 0) ∨ (∀ hlv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val))) Clv15.output) (Fin.append (fun plv15 : Fin Nlv15 => if plv15 ∈ Slv15 then (fun ulv15 : Fin Nlv15 => false) plv15 else pilv15 plv15) (fun llv15 : Fin Nlv15 => if llv15 ∈ Wlv15 then (fun ulv15x1 : Fin Nlv15 => false) llv15 else nulv15 llv15)) = true → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x1 : Fin Nlv15 => if plv15x1 ∈ Slv15 then (fun ulv15x2 : Fin Nlv15 => false) plv15x1 else pilv15 plv15x1) (fun llv15x1 : Fin Nlv15 => if llv15x1 ∈ Wlv15 then (fun ulv15x3 : Fin Nlv15 => false) llv15x1 else nulv15 llv15x1)) = false → (∃ xlv15 ylv15 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x2 : Fin Nlv15 => if plv15x2 ∈ Slv15 then xlv15 plv15x2 else pilv15 plv15x2) (fun llv15x2 : Fin Nlv15 => if llv15x2 ∈ Wlv15 then ylv15 llv15x2 else nulv15 llv15x2)) = true) → ∃ Dlv15 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15x1 ∈ Dlv15.gates, (glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Dlv15) ∧ Set.ncard {jlv15x2 : ℕ | jlv15x2 < Dlv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x2 0 = 0) ∨ (∀ hlv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x2 0 = 0))} ≤ mlv15 ∧ Dlv15.size ≤ Clv15.size ∧ (0 < Dlv15.gates.length ∧ (∀ jlv15x3 < Dlv15.gates.length, ∀ ilv15x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x3).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x3 : Fin Nlv15 => (plv15x3 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x3 : Fin Nlv15 => Nlv15 + (llv15x3 : ℕ)) (Wlv15)ᶜ)).getD ilv15x3 0 = 0) ∧ (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x4 : Fin Nlv15 => (plv15x4 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x4 : Fin Nlv15 => Nlv15 + (llv15x4 : ℕ)) (Wlv15)ᶜ)).getD Dlv15.output 0 = 0) ∧ ∀ xlv15x1 ylv15x1 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Dlv15 (Fin.append xlv15x1 ylv15x1) = PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x5 : Fin Nlv15 => if plv15x5 ∈ Slv15 then xlv15x1 plv15x5 else pilv15 plv15x5) (fun llv15x5 : Fin Nlv15 => if llv15x5 ∈ Wlv15 then ylv15x1 llv15x5 else nulv15 llv15x5))) → ∀ (Nlv15b Klv15b mlv15b : ℕ) (Ilv15b : Fin Nlv15b → Fin Nlv15b → Prop) [DecidableRel Ilv15b] (Clv15b : PEqualNP.CircuitLowerBounds.Circuit) (Slv15b Wlv15b Xlv15b : Finset (Fin Nlv15b)) (wlv15b : Fin Nlv15b) (sglv15b : ℕ → Fin 2) (Splv15b Wplv15b : Finset (Fin Nlv15b)), ((∀ glv15b ∈ Clv15b.gates, (glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Clv15b) → Set.ncard {jlv15b : ℕ | jlv15b < Clv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15b 0 = 0) ∨ (∀ hlv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15b 0 = 0))} ≤ mlv15b + 1 → ((0 < Clv15b.gates.length ∧ (∀ jlv15bx1 < Clv15b.gates.length, ∀ ilv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx1).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx5 : Fin Nlv15b => (plv15bx5 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx4 : Fin Nlv15b => Nlv15b + (llv15bx4 : ℕ)) (Wlv15b)ᶜ)).getD ilv15bx1 0 = 0) ∧ (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx6 : Fin Nlv15b => (plv15bx6 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx5 : Fin Nlv15b => Nlv15b + (llv15bx5 : ℕ)) (Wlv15b)ᶜ)).getD Clv15b.output 0 = 0) ∧ (∀ plv15bx3 ∈ Slv15b, ∀ llv15bx2 ∈ Wlv15b, Ilv15b plv15bx3 llv15bx2 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx7 : Fin Nlv15b => decide (plv15bx7 ∈ ({plv15bx3} : Finset (Fin Nlv15b)))) (fun llv15bx6 : Fin Nlv15b => decide (llv15bx6 ∈ ({llv15bx2} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx1 Ylv15b : Finset (Fin Nlv15b), Xlv15bx1 ⊆ Slv15b → Ylv15b ⊆ Wlv15b → Ylv15b.card ≤ Klv15b + 1 → (∀ plv15bx4 ∈ Xlv15bx1, ∀ llv15bx3 ∈ Ylv15b, ¬ Ilv15b plv15bx4 llv15bx3) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx8 : Fin Nlv15b => decide (plv15bx8 ∈ Xlv15bx1)) (fun llv15bx7 : Fin Nlv15b => decide (llv15bx7 ∈ Ylv15b))) = false)) → wlv15b ∈ Wlv15b → Xlv15b ⊆ Slv15b → (∀ plv15bx1 ∈ Xlv15b, ¬ Ilv15b plv15bx1 wlv15b) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15bx2 : Fin Clv15b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx2 0 = 0) ∨ (∀ hlv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val))) Clv15b.output) (Fin.append (fun plv15bx9 : Fin Nlv15b => decide (plv15bx9 ∈ Xlv15b)) (fun llv15bx8 : Fin Nlv15b => decide (llv15bx8 ∈ ({wlv15b} : Finset (Fin Nlv15b))))) = true → Splv15b = Slv15b.filter (fun ulv15b : Fin Nlv15b => ¬ Ilv15b ulv15b wlv15b ∧ ulv15b ∉ Xlv15b) → Wplv15b = Wlv15b.filter (fun llv15bx1 : Fin Nlv15b => llv15bx1 ≠ wlv15b ∧ ∀ plv15bx2 ∈ Xlv15b, ¬ Ilv15b plv15bx2 llv15bx1) → (∃ plv15b ∈ Splv15b, ∃ llv15b ∈ Wplv15b, Ilv15b plv15b llv15b) → ∃ Dlv15b : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15bx1 ∈ Dlv15b.gates, (glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15bx1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Dlv15b) ∧ Set.ncard {jlv15bx3 : ℕ | jlv15bx3 < Dlv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx3 0 = 0) ∨ (∀ hlv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx2 0 = 0))} ≤ mlv15b ∧ Dlv15b.size ≤ Clv15b.size ∧ ((0 < Dlv15b.gates.length ∧ (∀ jlv15bx4 < Dlv15b.gates.length, ∀ ilv15bx4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx4).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx12 : Fin Nlv15b => (plv15bx12 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx11 : Fin Nlv15b => Nlv15b + (llv15bx11 : ℕ)) (Wplv15b)ᶜ)).getD ilv15bx4 0 = 0) ∧ (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx13 : Fin Nlv15b => (plv15bx13 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx12 : Fin Nlv15b => Nlv15b + (llv15bx12 : ℕ)) (Wplv15b)ᶜ)).getD Dlv15b.output 0 = 0) ∧ (∀ plv15bx10 ∈ Splv15b, ∀ llv15bx9 ∈ Wplv15b, Ilv15b plv15bx10 llv15bx9 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx14 : Fin Nlv15b => decide (plv15bx14 ∈ ({plv15bx10} : Finset (Fin Nlv15b)))) (fun llv15bx13 : Fin Nlv15b => decide (llv15bx13 ∈ ({llv15bx9} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx2 Ylv15bx1 : Finset (Fin Nlv15b), Xlv15bx2 ⊆ Splv15b → Ylv15bx1 ⊆ Wplv15b → Ylv15bx1.card ≤ Klv15b → (∀ plv15bx11 ∈ Xlv15bx2, ∀ llv15bx10 ∈ Ylv15bx1, ¬ Ilv15b plv15bx11 llv15bx10) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx15 : Fin Nlv15b => decide (plv15bx15 ∈ Xlv15bx2)) (fun llv15bx14 : Fin Nlv15b => decide (llv15bx14 ∈ Ylv15bx1))) = false)) := by
  intro hKill N K m I instI C S W X w sg S' W' hC hcross hrest hw hX hXw hview hS' hW' hinc
  obtain ⟨hread, hacc, hrej⟩ := hrest
  have hS'mem : ∀ u, u ∈ S' ↔ u ∈ S ∧ (¬ I u w ∧ u ∉ X) := fun u => by rw [hS', Finset.mem_filter]
  have hW'mem : ∀ l, l ∈ W' ↔ l ∈ W ∧ (l ≠ w ∧ ∀ p ∈ X, ¬ I p l) := fun l => by rw [hW', Finset.mem_filter]
  have hXS' : ∀ t ∈ X, t ∉ S' := fun t ht hS => ((hS'mem t).mp hS).2.2 ht
  have hwW' : ∀ t ∈ ({w} : Finset (Fin N)), t ∉ W' :=
    fun t ht hW => ((hW'mem t).mp hW).2.1 (Finset.mem_singleton.mp ht)
  have hmono : ∀ p ∈ S', ∀ l ∈ W', I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (Fin.append (fun u => if u ∈ S' then decide (u ∈ ({p} : Finset (Fin N))) else decide (u ∈ X)) (fun t => if t ∈ W' then decide (t ∈ ({l} : Finset (Fin N))) else decide (t ∈ ({w} : Finset (Fin N))))) = true := by
    intro p hp l hl hpl
    refine cf_mono_fn C hC.1 _ _ ?_ (hacc p ((hS'mem p).mp hp).1 l ((hW'mem l).mp hl).1 hpl)
    intro v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) v
    · rw [Fin.append_left, Fin.append_left]
      exact up S' X p hp i
    · rw [Fin.append_right, Fin.append_right]
      exact up W' {w} l hl i
  obtain ⟨D, hD, hDc, hDs, hDr, hDfun⟩ := hKill N m C S' W' (fun u => decide (u ∈ X)) (fun l => decide (l ∈ ({w} : Finset (Fin N)))) sg hC hcross
    (Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) _) (congrArg₂ Fin.append (funext fun u => off S' X hXS' u) (funext fun t => off W' {w} hwW' t))) hview)
    (Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) C) (congrArg₂ Fin.append (funext fun u => off S' X hXS' u) (funext fun t => off W' {w} hwW' t)))
      (hrej X {w} hX (Finset.singleton_subset_iff.mpr hw) (by rw [Finset.card_singleton]; omega)
        (fun p hp l hl => by rw [Finset.mem_singleton.mp hl]; exact hXw p hp)))
    (by
      obtain ⟨p, hp, l, hl, hpl⟩ := hinc
      exact ⟨fun u => decide (u ∈ ({p} : Finset (Fin N))), fun t => decide (t ∈ ({l} : Finset (Fin N))), hmono p hp l hl hpl⟩)
  refine ⟨D, hD, hDc, hDs, ⟨hDr, ?_, ?_⟩⟩
  · intro p hp l hl hpl
    exact (hDfun _ _).trans (hmono p hp l hl hpl)
  · intro X2 Y hX2 hY hYc hXY
    refine (hDfun _ _).trans (Eq.trans (congrArg (PEqualNP.MetaComplexity.circuitFun (N + N) C) (congrArg₂ Fin.append (funext fun u => mix S' X X2 (X2 ∪ X) hX2 hXS' (fun _ => Finset.mem_union) u) (funext fun t => mix W' {w} Y (Y ∪ {w}) hY hwW' (fun _ => Finset.mem_union) t))) (hrej (X2 ∪ X) (Y ∪ {w}) ?_ ?_ ?_ ?_))
    · exact Finset.union_subset (fun u hu => ((hS'mem u).mp (hX2 hu)).1) hX
    · exact Finset.union_subset (fun t ht => ((hW'mem t).mp (hY ht)).1) (Finset.singleton_subset_iff.mpr hw)
    · refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_singleton]
      omega
    · intro p hp l hl
      rcases Finset.mem_union.mp hp with h | h <;> rcases Finset.mem_union.mp hl with h' | h'
      · exact hXY p h l h'
      · rw [Finset.mem_singleton.mp h']
        exact ((hS'mem p).mp (hX2 h)).2.1
      · exact ((hW'mem l).mp (hY h')).2.2 p h
      · rw [Finset.mem_singleton.mp h']
        exact hXw p h
