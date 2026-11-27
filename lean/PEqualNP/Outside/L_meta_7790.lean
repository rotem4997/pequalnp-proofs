import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7790

open PEqualNP.CircuitLowerBounds

def fm (s t : Equiv.Perm (Fin 13)) (i : ℕ) : ℕ :=
  if h : i < 13 then ((s ⟨i, h⟩ : Fin 13) : ℕ)
  else if h2 : i < 26 then 13 + ((t ⟨i - 13, by omega⟩ : Fin 13) : ℕ) else i

theorem fm_lt (s t : Equiv.Perm (Fin 13)) (i : ℕ) (hi : i < 26) : fm s t i < 26 := by
  unfold fm
  split_ifs with h1 h2
  · have := (s ⟨i, h1⟩).isLt; omega
  · have := (t ⟨i - 13, by omega⟩).isLt; omega

theorem fm_ge (s t : Equiv.Perm (Fin 13)) (i : ℕ) (hi : 26 ≤ i) : fm s t i = i := by
  unfold fm
  rw [dif_neg (by omega), dif_neg (by omega)]

def mg (s t : Equiv.Perm (Fin 13)) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (fm s t) }

def relab (s t : Equiv.Perm (Fin 13)) (C : Circuit) : Circuit :=
  { gates := C.gates.map (mg s t), output := fm s t C.output }

theorem base (s t : Equiv.Perm (Fin 13)) (X Y : Finset (Fin 13)) (i : ℕ) :
    (PEqualNP.GenericRejection.incidenceInput (Finset.map (Equiv.toEmbedding s) X)
      (Finset.map (Equiv.toEmbedding t) Y)).getD (fm s t i) false
      = (PEqualNP.GenericRejection.incidenceInput X Y).getD i false := by
  unfold PEqualNP.GenericRejection.incidenceInput
  by_cases h1 : i < 13
  · have hf : fm s t i = ((s ⟨i, h1⟩ : Fin 13) : ℕ) := by unfold fm; rw [dif_pos h1]
    rw [hf]
    have ha := (s ⟨i, h1⟩).isLt
    rw [List.getD_append _ _ _ _ (by simp <;> omega), List.getD_append _ _ _ _ (by simp <;> omega)]
    rw [List.getD_eq_getElem _ _ (by simp <;> omega), List.getD_eq_getElem _ _ (by simp <;> omega)]
    simp only [List.getElem_ofFn, Fin.eta, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  · by_cases h2 : i < 26
    · have hf : fm s t i = 13 + ((t ⟨i - 13, by omega⟩ : Fin 13) : ℕ) := by
        unfold fm; rw [dif_neg h1, dif_pos h2]
      rw [hf]
      have ha := (t ⟨i - 13, by omega⟩).isLt
      rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp <;> omega)]
      rw [List.getD_eq_getElem _ _ (by simp <;> omega), List.getD_eq_getElem _ _ (by simp <;> omega)]
      simp only [List.length_ofFn, List.getElem_ofFn]
      have e1 : 13 + ((t ⟨i - 13, by omega⟩ : Fin 13) : ℕ) - 13 = ((t ⟨i - 13, by omega⟩ : Fin 13) : ℕ) := by omega
      simp only [e1, Fin.eta, Finset.mem_map_equiv, Equiv.toEmbedding_apply]
      simp
    · rw [fm_ge s t i (by omega)]
      rw [List.getD_eq_default _ _ (by simp <;> omega), List.getD_eq_default _ _ (by simp <;> omega)]

theorem step_eq (s t : Equiv.Perm (Fin 13)) (w5 w2 : List Bool) (a : Bool)
    (hl : 26 ≤ w2.length) (hle : w5.length = w2.length)
    (h : ∀ i, w5.getD (fm s t i) false = w2.getD i false) (i : ℕ) :
    (w5 ++ [a]).getD (fm s t i) false = (w2 ++ [a]).getD i false := by
  by_cases hi : i < 26
  · have := fm_lt s t i hi
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact h i
  · have hf := fm_ge s t i (by omega)
    have hi' := h i
    rw [hf] at hi' ⊢
    by_cases hlt : i < w2.length
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hi'
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        hle]

theorem fold_rel (s t : Equiv.Perm (Fin 13)) (gs : List Gate) : ∀ (w5 w2 : List Bool),
    26 ≤ w2.length → w5.length = w2.length →
    (∀ i, w5.getD (fm s t i) false = w2.getD i false) →
    let r5 := (gs.map (mg s t)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w5
    let r2 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2
    26 ≤ r2.length ∧ r5.length = r2.length ∧ ∀ i, r5.getD (fm s t i) false = r2.getD i false := by
  induction gs with
  | nil => intro w5 w2 hl hle h; exact ⟨hl, hle, h⟩
  | cons g gs ih =>
    intro w5 w2 hl hle h
    have hv : (mg s t g).op.eval ((mg s t g).inputs.map fun i => w5.getD i false)
        = g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      simp only [mg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    have := ih (w5 ++ [(mg s t g).op.eval ((mg s t g).inputs.map fun i => w5.getD i false)])
      (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
      (by simp <;> omega) (by simp <;> omega) (by rw [hv]; exact step_eq s t w5 w2 _ hl hle h)
    simpa only [List.map_cons, List.foldl_cons] using this

theorem wires_rel (s t : Equiv.Perm (Fin 13)) (C : Circuit) (X Y : Finset (Fin 13)) (i : ℕ) :
    ((relab s t C).wires (PEqualNP.GenericRejection.incidenceInput
      (Finset.map (Equiv.toEmbedding s) X) (Finset.map (Equiv.toEmbedding t) Y))).getD
        (fm s t i) false
      = (C.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD i false := by
  have := fold_rel s t C.gates _ (PEqualNP.GenericRejection.incidenceInput X Y)
    (by simp [PEqualNP.GenericRejection.incidenceInput])
    (by simp [PEqualNP.GenericRejection.incidenceInput]) (base s t X Y)
  exact this.2.2 i

theorem eval_rel (s t : Equiv.Perm (Fin 13)) (C : Circuit) (X Y : Finset (Fin 13)) :
    (relab s t C).eval (PEqualNP.GenericRejection.incidenceInput
      (Finset.map (Equiv.toEmbedding s) X) (Finset.map (Equiv.toEmbedding t) Y))
      = C.eval (PEqualNP.GenericRejection.incidenceInput X Y) := by
  unfold Circuit.eval
  exact wires_rel s t C X Y C.output

theorem filt (s t : Equiv.Perm (Fin 13)) (c : ℕ) (l : List ℕ) :
    (l.map (fm s t)).filter (fun w => decide (26 ≤ w ∧ w < 26 + c))
      = l.filter (fun w => decide (26 ≤ w ∧ w < 26 + c)) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons, ih]
    by_cases hw : w < 26
    · have := fm_lt s t w hw
      have e1 : decide (26 ≤ fm s t w ∧ fm s t w < 26 + c) = false := by simp; omega
      have e2 : decide (26 ≤ w ∧ w < 26 + c) = false := by simp; omega
      rw [e1, e2]
      simp
    · rw [fm_ge s t w (by omega)]

theorem cones_rel (s t : Equiv.Perm (Fin 13)) (C : Circuit) :
    PEqualNP.EdgeOwnership.cones 26 (relab s t C) = PEqualNP.EdgeOwnership.cones 26 C := by
  unfold PEqualNP.EdgeOwnership.cones relab
  simp only [List.foldl_map]
  congr 1
  funext cs g
  unfold PEqualNP.EdgeOwnership.coneStep mg
  simp only
  rw [filt]

theorem gateAt_rel (s t : Equiv.Perm (Fin 13)) (C : Circuit) (j : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.gateAt (relab s t C) j
      = mg s t (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt relab
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> rfl

def kill (C : Circuit) (k : ℕ) : Circuit :=
  { gates := C.gates.set k { op := GateOp.or, inputs := [] }, output := C.output }

theorem kill_relab (s t : Equiv.Perm (Fin 13)) (C : Circuit) (k : ℕ) :
    kill (relab s t C) k = relab s t (kill C k) := by
  simp only [kill, relab, List.map_set]
  rfl

end PEqualNP.Outside.L_meta_7790

theorem PEqualNP.Outside.L_meta_7790 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) => { gates := x1.gates.set x2 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Equiv.Perm (Fin (13 : ℕ))),   ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),     x5.size = x2.size ∧       (PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.Monotone2 x5) ∧         (PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5) ∧           (∀ (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op) ∧             (∀ (x6 x7 : ℕ), PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x6 x7 ↔ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x2 x6 x7) ∧               ∀ (x6 x7 : Finset (Fin (13 : ℕ))),                 have x8 : List Bool := PEqualNP.GenericRejection.incidenceInput (Finset.map (Equiv.toEmbedding x3) x6) (Finset.map (Equiv.toEmbedding x4) x7);                 have x9 : List Bool := PEqualNP.GenericRejection.incidenceInput x6 x7;                 x5.eval x8 = x2.eval x9 ∧ (∀ (x10 : ℕ), (x5.wires x8).getD ((26 : ℕ) + x10) Bool.false = (x2.wires x9).getD ((26 : ℕ) + x10) Bool.false) ∧ ∀ (x10 : ℕ), (x1 x5 x10).eval x8 = (x1 x2 x10).eval x9 := by
  dsimp only
  intro C s t
  refine ⟨PEqualNP.Outside.L_meta_7790.relab s t C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_7790.relab, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro hm g hg
    simp only [PEqualNP.Outside.L_meta_7790.relab, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hm g0 hg0
    simpa [PEqualNP.Outside.L_meta_7790.mg] using this
  · intro hr j hj i hi
    rw [PEqualNP.Outside.L_meta_7790.gateAt_rel] at hi
    simp only [PEqualNP.Outside.L_meta_7790.mg, List.mem_map] at hi
    obtain ⟨i0, hi0, rfl⟩ := hi
    have hj' : j < C.gates.length := by simpa [PEqualNP.Outside.L_meta_7790.relab] using hj
    have := hr j hj' i0 hi0
    by_cases h26 : i0 < 26
    · have := PEqualNP.Outside.L_meta_7790.fm_lt s t i0 h26; omega
    · rw [PEqualNP.Outside.L_meta_7790.fm_ge s t i0 (by omega)]; exact this
  · intro j
    rw [PEqualNP.Outside.L_meta_7790.gateAt_rel]; rfl
  · intro i j
    unfold PEqualNP.EdgeOwnership.InCone
    rw [PEqualNP.Outside.L_meta_7790.cones_rel]
  · intro X Y
    refine ⟨PEqualNP.Outside.L_meta_7790.eval_rel s t C X Y, ?_, ?_⟩
    · intro k
      have := PEqualNP.Outside.L_meta_7790.wires_rel s t C X Y (26 + k)
      rwa [PEqualNP.Outside.L_meta_7790.fm_ge s t _ (by omega)] at this
    · intro k
      have := PEqualNP.Outside.L_meta_7790.eval_rel s t (PEqualNP.Outside.L_meta_7790.kill C k) X Y
      rw [← PEqualNP.Outside.L_meta_7790.kill_relab] at this
      exact this
