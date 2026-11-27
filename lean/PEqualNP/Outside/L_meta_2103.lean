import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2103

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (n1 n2 s5 : ℕ) (r : Fin n1 → Fin n2) (i : ℕ) : ℕ :=
  if h : i < n1 then (r ⟨i, h⟩).val else i - n1 + (n2 + s5)

def out5 (n2 s5 s4 o : ℕ) : ℕ := if o < n2 + s5 then o else n2 + s5 + s4

def comb (n1 n2 : ℕ) (r : Fin n1 → Fin n2) (C4 C5 : Circuit) : Circuit :=
  ⟨C5.gates ++ C4.gates.map (reGate (rho n1 n2 C5.gates.length r)) ++
    [⟨GateOp.or, [rho n1 n2 C5.gates.length r C4.output,
      out5 n2 C5.gates.length C4.gates.length C5.output]⟩],
    n2 + C5.gates.length + C4.gates.length⟩

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma getD_snoc_len (l : List Bool) (b : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [b]).getD n false = b := by
  subst h; simp

lemma fold_shape (gs : List Gate) :
    ∀ w : List Bool, ∃ u : List Bool, u.length = gs.length ∧ gs.foldl stepW w = w ++ u := by
  induction gs with
  | nil => intro w; exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨u, hu, he⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ u, ?_, ?_⟩
    · simp [hu] <;> omega
    · rw [List.foldl_cons, he]
      simp [stepW]

lemma fold_pair (P Q : List Bool) (ρ : ℕ → ℕ)
    (hρ : ∀ (v : List Bool) (i : ℕ), (P ++ v).getD (ρ i) false = (Q ++ v).getD i false)
    (gs : List Gate) :
    ∀ v : List Bool, ∃ v' : List Bool, v'.length = v.length + gs.length ∧
      gs.foldl stepW (Q ++ v) = Q ++ v' ∧
      (gs.map (reGate ρ)).foldl stepW (P ++ v) = P ++ v' := by
  induction gs with
  | nil => intro v; exact ⟨v, by simp, rfl, rfl⟩
  | cons g gs ih =>
    intro v
    obtain ⟨v', hl, h1, h2⟩ :=
      ih (v ++ [g.op.eval (g.inputs.map fun i => (Q ++ v).getD i false)])
    have hm : (g.inputs.map ρ).map (fun i => (P ++ v).getD i false)
        = g.inputs.map (fun i => (Q ++ v).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => hρ v i)
    refine ⟨v', ?_, ?_, ?_⟩
    · simp at hl ⊢; omega
    · rw [List.foldl_cons, ← h1]
      simp [stepW]
    · rw [List.map_cons, List.foldl_cons, ← h2]
      have hs : stepW (P ++ v) (reGate ρ g)
          = P ++ (v ++ [g.op.eval (g.inputs.map fun i => (Q ++ v).getD i false)]) := by
        show (P ++ v) ++ [g.op.eval ((g.inputs.map ρ).map fun i => (P ++ v).getD i false)] = _
        rw [hm, List.append_assoc]
      rw [hs]

lemma rho_spec (n1 n2 : ℕ) (r : Fin n1 → Fin n2) (x : Fin n2 → Bool) (u : List Bool)
    (v : List Bool) (i : ℕ) :
    ((List.ofFn x ++ u) ++ v).getD (rho n1 n2 u.length r i) false
      = (List.ofFn (fun k => x (r k)) ++ v).getD i false := by
  unfold rho
  by_cases h : i < n1
  · rw [dif_pos h]
    have h2 : (r ⟨i, h⟩).val < n2 := (r ⟨i, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simpa using h2),
      List.getD_append _ _ _ _ (by simpa using h),
      List.getD_eq_getElem _ _ (by simpa using h2), List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [dif_neg h]
    rw [List.getD_append_right _ _ _ _ (by simp <;> omega),
      List.getD_append_right _ _ _ _ (by simp <;> omega)]
    congr 1
    simp <;> omega

lemma main (n1 n2 : ℕ) (r : Fin n1 → Fin n2) (C4 C5 : Circuit) (x : Fin n2 → Bool) :
    (comb n1 n2 r C4 C5).eval (List.ofFn x)
      = (C4.eval (List.ofFn fun k => x (r k)) || C5.eval (List.ofFn x)) := by
  obtain ⟨u, hu, hW5⟩ := fold_shape C5.gates (List.ofFn x)
  obtain ⟨v', hl, h1, h2⟩ := fold_pair (List.ofFn x ++ u) (List.ofFn fun k => x (r k))
    (rho n1 n2 u.length r) (rho_spec n1 n2 r x u) C4.gates []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at h1 h2 hl
  have e4 : C4.wires (List.ofFn fun k => x (r k)) = (List.ofFn fun k => x (r k)) ++ v' := h1
  have e5 : C5.wires (List.ofFn x) = List.ofFn x ++ u := hW5
  have e10 : (comb n1 n2 r C4 C5).wires (List.ofFn x) = ((List.ofFn x ++ u) ++ v') ++
      [GateOp.or.eval ([rho n1 n2 u.length r C4.output,
        out5 n2 u.length C4.gates.length C5.output].map
          fun i => ((List.ofFn x ++ u) ++ v').getD i false)] := by
    rw [wires_eq]
    unfold comb
    simp only
    rw [List.foldl_append, List.foldl_append, hW5, ← hu, h2]
    rfl
  have h5 : ((List.ofFn x ++ u) ++ v').getD (out5 n2 u.length C4.gates.length C5.output) false
      = (List.ofFn x ++ u).getD C5.output false := by
    unfold out5
    by_cases h : C5.output < n2 + u.length
    · rw [if_pos h, List.getD_append _ _ _ _ (by simpa using h)]
    · rw [if_neg h, List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  unfold Circuit.eval
  rw [e10, e4, e5]
  have ho : (comb n1 n2 r C4 C5).output = n2 + u.length + C4.gates.length := by
    rw [hu]; rfl
  rw [ho, getD_snoc_len _ _ _ (by simp; omega)]
  show GateOp.or.eval [((List.ofFn x ++ u) ++ v').getD (rho n1 n2 u.length r C4.output) false,
    ((List.ofFn x ++ u) ++ v').getD (out5 n2 u.length C4.gates.length C5.output) false] = _
  rw [rho_spec, h5]
  simp [GateOp.eval]

lemma mono (n1 n2 : ℕ) (r : Fin n1 → Fin n2) (C4 C5 : Circuit)
    (h4 : PEqualNP.MetaComplexity.Monotone2 C4) (h5 : PEqualNP.MetaComplexity.Monotone2 C5) :
    PEqualNP.MetaComplexity.Monotone2 (comb n1 n2 r C4 C5) := by
  intro g hg
  unfold comb at hg
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact h5 g hg
  · have := h4 g' hg'
    simpa [reGate] using this
  · simp

end PEqualNP.Outside.L_meta_2103

theorem PEqualNP.Outside.L_meta_2103 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x5 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = ((PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x12 : Fin x1) => x11 (x3 x12)) || PEqualNP.MetaComplexity.circuitFun x2 x5 x11) := by
  intro n1 n2 r C4 C5 h4 _ h5 _
  refine ⟨PEqualNP.Outside.L_meta_2103.comb n1 n2 r C4 C5,
    PEqualNP.Outside.L_meta_2103.mono n1 n2 r C4 C5 h4 h5, ?_, ?_⟩
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2103.comb,
      List.length_append, List.length_map, List.length_singleton]
    omega
  · intro x
    exact PEqualNP.Outside.L_meta_2103.main n1 n2 r C4 C5 x
