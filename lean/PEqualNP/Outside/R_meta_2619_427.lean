import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- If each input to a terminal AND accepts some singleton, monotonicity
-- forces its other operand's singleton support into just one neighbourhood.
-- Two such neighbourhoods cannot touch all thirteen diagonal flags.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2619_427
    (build : ∃ (C : Circuit) (j a b : Nat), C.size ≤ 64 ∧ IsAO2 26 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output = 26+j ∧
      C.gates[j]? = some ⟨.and,[a,b]⟩ ∧
      (∀ z : Fin 26 → Bool, C.eval (List.ofFn z) = true ↔ ∃ l : Fin 13,
        z (Fin.natAdd 13 l) = true ∧ (z (Fin.castAdd 13 l) || z (Fin.castAdd 13 (l+1)) ||
        z (Fin.castAdd 13 (l+3)) || z (Fin.castAdd 13 (l+9))) = true) ∧
      ∃ s t : Fin 26, (C.wires (List.ofFn (fun i : Fin 26 => decide (i=s)))).getD a false = true ∧
        (C.wires (List.ofFn (fun i : Fin 26 => decide (i=t)))).getD b false = true)
    (join : ∀ (n : Nat) (C : Circuit) (j a b : Nat), IsAO2 n C → C.output = n+j →
      C.gates[j]? = some ⟨.and,[a,b]⟩ → ∀ s t : Fin n,
      (C.wires (List.ofFn (fun i : Fin n => decide (i=s)))).getD a false = true →
      (C.wires (List.ofFn (fun i : Fin n => decide (i=t)))).getD b false = true →
      C.eval (List.ofFn (fun i : Fin n => decide (i=s ∨ i=t))) = true)
    (rename : ∀ (n : Nat) (f : Fin n → Fin n) (C : Circuit) (j a b : Nat), Function.Injective f →
      IsAO2 n C → (∀ g ∈ C.gates, g.inputs.Nodup) → C.output = n+j → C.gates[j]? = some ⟨.and,[a,b]⟩ →
      ∃ (D : Circuit) (u v : Nat), D.size = C.size ∧ IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        D.output = n+j ∧ D.gates[j]? = some ⟨.and,[u,v]⟩ ∧ ∀ x : Fin n → Bool,
        D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ f)) ∧
        (D.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn (x ∘ f))).getD a false ∧
        (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn (x ∘ f))).getD b false) : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false) := by
  let pt : Fin 13 → Fin 26 := Fin.castAdd 13
  let ln : Fin 13 → Fin 26 := Fin.natAdd 13
  let inc (z : Fin 26 → Bool) := ∃ l : Fin 13, z (ln l) = true ∧
    (z (pt l) || z (pt (l+1)) || z (pt (l+3)) || z (pt (l+9))) = true
  let pair (s t i : Fin 26) := decide (i = s ∨ i = t)
  let one (s i : Fin 26) := decide (i=s)
  have avoid : ∀ s t : Fin 26, ∃ k : Fin 13,
      ¬inc (pair (pt k) t) ∧ ¬inc (pair (ln k) t) ∧ ¬inc (pair s (pt k)) ∧ ¬inc (pair s (ln k)) := by
    dsimp only [inc, pair, pt, ln]
    decide +kernel
  obtain ⟨C,j,a,b,size,ao,nd,out,gate,correct,s,t,hs,ht⟩ := build
  obtain ⟨k,ap,al,bp,bl⟩ := avoid s t
  have quiet (z : Fin 26) (ha : ¬inc (pair z t)) (hb : ¬inc (pair s z)) :
      (C.wires (List.ofFn (one z))).getD a false = false ∧ (C.wires (List.ofFn (one z))).getD b false = false := by
    constructor
    · cases h : (C.wires (List.ofFn (one z))).getD a false with
      | false => rfl
      | true => exact False.elim (ha ((correct _).mp (join 26 C j a b ao out gate z t h ht)))
    · cases h : (C.wires (List.ofFn (one z))).getD b false with
      | false => rfl
      | true => exact False.elim (hb ((correct _).mp (join 26 C j a b ao out gate s z hs h)))
  let rot (d : Fin 13) (z : Fin 26) : Fin 26 := Fin.addCases (motive := fun _ => Fin 26) (fun i => pt (i+d)) (fun i => ln (i+d)) z
  have rp (d i : Fin 13) : rot d (pt i) = pt (i+d) := by simp only [rot,pt,Fin.addCases_left]
  have rl (d i : Fin 13) : rot d (ln i) = ln (i+d) := by simp only [rot,ln,Fin.addCases_right]
  have inv (d : Fin 13) (z : Fin 26) : rot (-d) (rot d z) = z := by
    refine Fin.addCases (m := 13) (n := 13) (motive := fun z => rot (-d) (rot d z) = z) (fun i => ?_) (fun i => ?_) z
    · change rot (-d) (rot d (pt i)) = pt i; simp only [rp, add_neg_cancel_right]
    · change rot (-d) (rot d (ln i)) = ln i; simp only [rl, add_neg_cancel_right]
  have inj (d : Fin 13) : Function.Injective (rot d) := fun x y h =>
    (inv d x).symm.trans ((congrArg (rot (-d)) h).trans (inv d y))
  have symmetry (x : Fin 26 → Bool) (d : Fin 13) : inc (x ∘ rot d) ↔ inc x := by
    constructor
    · rintro ⟨i,h1,h2⟩
      refine ⟨i+d,?_,?_⟩
      · simpa only [Function.comp_apply,rl] using h1
      · simpa only [Function.comp_apply,rp,add_right_comm i (1:Fin 13) d,add_right_comm i (3:Fin 13) d,add_right_comm i (9:Fin 13) d] using h2
    · rintro ⟨i,h1,h2⟩
      refine ⟨i-d,?_,?_⟩
      · simpa only [Function.comp_apply,rl,sub_add_cancel] using h1
      · simpa only [Function.comp_apply,rp,add_right_comm (i-d) (1:Fin 13) d,add_right_comm (i-d) (3:Fin 13) d,add_right_comm (i-d) (9:Fin 13) d,sub_add_cancel] using h2
  obtain ⟨D,u,v,ds,dao,dnd,dout,dgate,rel⟩ := rename 26 (rot (-k)) C j a b (inj _) ao nd out gate
  refine ⟨D,ds ▸ size,dao,dnd,?_,j,u,v,dout,dgate,?_⟩
  · intro x y
    rw [(rel _).1, correct]
    exact (symmetry _ _).trans (by simp only [inc,pt,ln,Fin.addCases_left,Fin.addCases_right])
  · have transport (w : Fin 26) (h : ¬inc (pair w t)) (h' : ¬inc (pair s w)) :
        (D.wires (List.ofFn (one (rot (-k) w)))).getD u false = false ∧
        (D.wires (List.ofFn (one (rot (-k) w)))).getD v false = false := by
      have eq : one (rot (-k) w) ∘ rot (-k) = one w := by
        funext i; simp [one,Function.comp_apply,(inj (-k)).eq_iff]
      obtain ⟨_,hu,hv⟩ := rel (one (rot (-k) w))
      rw [eq] at hu hv
      exact ⟨hu.trans (quiet w h h').1,hv.trans (quiet w h h').2⟩
    have oneIndex (w : Fin 26) : (fun i : Fin 26 => decide (i.val = w.val)) = one w := by
      funext i; simp only [one,Fin.val_inj]
    intro side
    cases side with
    | false =>
      have h := transport (pt k) ap bp
      rw [rp,add_neg_cancel] at h
      change (D.wires (List.ofFn (fun i : Fin 26 => decide (i.val = (pt 0).val)))).getD u false = false ∧ _
      rw [oneIndex (pt 0)]
      exact h
    | true =>
      have h := transport (ln k) al bl
      rw [rl,add_neg_cancel] at h
      change (D.wires (List.ofFn (fun i : Fin 26 => decide (i.val = (ln 0).val)))).getD u false = false ∧ _
      rw [oneIndex (ln 0)]
      exact h
