import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19016.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_prefix (gs : List Gate) (x : List Bool) :
    ∃ t : List Bool, run gs x = x ++ t ∧ t.length = gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: t, ?_, by simp [hl]⟩
    change run gs (x ++ [_]) = _
    rw [ht]
    simp

lemma length_run (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  obtain ⟨t,ht,hl⟩ := wires_prefix gs x
  simp [ht,hl]

lemma input_value (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  obtain ⟨t,ht,_⟩ := wires_prefix C.gates x
  change (run C.gates x).getD i false = _
  rw [ht,List.getD_append _ _ _ _ hi]

lemma input_output_impossible (n m : ℕ) (C : Circuit) (ho : C.output < n+m)
    (hs : ∀ x : Fin (n+m) → Bool, C.eval (List.ofFn x) = true →
      ∃ (u : Fin n) (v : Fin m), x (Fin.castAdd m u) = true ∧ x (Fin.natAdd n v) = true) : False := by
  let x : Fin (n+m) → Bool := fun i => decide (i.val = C.output)
  have hx : C.eval (List.ofFn x) = true := by
    unfold Circuit.eval
    rw [input_value C (List.ofFn x) C.output (by simpa using ho)]
    simp [List.getD_eq_getElem?_getD,ho,x]
  obtain ⟨u,v,hu,hv⟩ := hs x hx
  simp only [x,decide_eq_true_eq,Fin.val_castAdd,Fin.val_natAdd] at hu hv
  have := u.isLt
  omega

lemma distinct_output_impossible (n : ℕ) (C : Circuit) (ho : C.output < n)
    (hs : ∀ x : Fin n → Bool,C.eval (List.ofFn x) = true →
      ∃ u v : Fin n,u ≠ v ∧ x u = true ∧ x v = true) : False := by
  let x : Fin n → Bool := fun i => decide (i.val = C.output)
  have hx : C.eval (List.ofFn x) = true := by
    unfold Circuit.eval
    rw [input_value C (List.ofFn x) C.output (by simpa using ho)]
    simp [List.getD_eq_getElem?_getD,ho,x]
  obtain ⟨u,v,huv,hu,hv⟩ := hs x hx
  apply huv
  apply Fin.ext
  simp only [x,decide_eq_true_eq] at hu hv
  omega
end PEqualNP.Outside.L_meta_19016.Helpers


theorem PEqualNP.Outside.L_meta_19016 : (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧ (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧ (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧ ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x3 x11 x12 ∧ x3 x12 x13 ∧ x10 x11 x7 ∧ x4 x11 x8 = Bool.true ∧ x5 x12 ∧ x4 x12 x8 = Bool.false ∧ x10 x13 x8 ∧ x1.output < (26 : ℕ)) := by
  rintro ⟨C,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,ho⟩
  apply PEqualNP.Outside.L_meta_19016.Helpers.input_output_impossible 13 13 C ho
  intro x hx
  obtain ⟨p,l,_,hp,hl⟩ := (a3 x).mp hx
  exact ⟨p,l,hp,hl⟩
