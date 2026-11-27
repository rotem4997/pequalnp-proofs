import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3453

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- The wire evaluation and gate monotonicity lemmas are adapted from L_meta_1766.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma wire_relation {n : ℕ} {C : Circuit} {u : ℕ} {sigma : ℕ → ℕ} {x : Fin n → Bool}
    (R : Bool → Bool → Prop) (reflR : ∀ b, R b b)
    (transR : ∀ {a b c}, R a b → R b c → R a c) (mono : OpMono R)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + u)
    (reads : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
      R (val C (List.ofFn x) (sigma r)) (val C (List.ofFn x) (n + u))) :
    ∀ i, R (val (PEqualNP.FactorSubst.substReads C n u sigma) (List.ofFn x) i)
      (val C (List.ofFn x) i) := by
  let D := PEqualNP.FactorSubst.substReads C n u sigma
  let z := List.ofFn x
  have hz : z.length = n := by simp [z]
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  change ∀ i, R (val D z i) (val C z i)
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < n
    · rw [val_input hz hin, val_input hz hin]
      exact reflR _
    by_cases hout : n + C.gates.length ≤ i
    · rw [val_ge hz (show n + D.gates.length ≤ i by omega), val_ge hz hout]
      exact reflR _
    let r := i - n
    have hi : i = n + r := by dsimp [r]; omega
    have hr : r < C.gates.length := by omega
    have hd : r < D.gates.length := by omega
    let sub := fun j : ℕ => if j = n + u then sigma r else j
    have atD : gateAt D r = ⟨(gateAt C r).op, (gateAt C r).inputs.map sub⟩ := by
      rw [gateAt_eq hd, gateAt_eq hr]
      simp [D, PEqualNP.FactorSubst.substReads, sub]
    rw [hi, val_gate hz hd, val_gate hz hr, atD, List.map_map]
    apply mono _ (hC.1 _ (gateAt_mem hr))
    intro j hj
    have hjlt := hC.2.1 r hr j hj
    have hsig := hs r
    have hsub : sub j < n + r := by
      dsimp [sub]
      split <;> omega
    simp only [Function.comp_apply, ite_eq_left hsub, ite_eq_left hjlt]
    by_cases he : j = n + u
    · subst j
      simpa only [sub, ite_eq_left rfl] using transR (ih (sigma r) (by omega)) (reads r hr hj)
    · simpa [sub, he] using ih j (by omega)

end PEqualNP.Outside.L_meta_3453

open PEqualNP.Outside.L_meta_3453

theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x hC _ hs
  constructor
  · intro h
    exact wire_relation (fun a b => a = true → b = true) (fun _ h => h)
      (fun h₁ h₂ v => h₂ (h₁ v)) opMono_imp hC hs h
  · intro h
    have equal := wire_relation Eq (fun _ => rfl) (fun h₁ h₂ => h₁.trans h₂) opMono_eq hC hs h
    apply List.ext_getElem
    · simp [wires_eq_foldl, foldl_length, PEqualNP.FactorSubst.substReads]
    · intro i hi hj
      simpa only [val, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hj, Option.getD_some] using equal i
