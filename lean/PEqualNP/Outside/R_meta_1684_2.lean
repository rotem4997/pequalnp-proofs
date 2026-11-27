import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1684_2
    (hAnd : let S : Finset (Fin 13) := {0, 1, 3, 9}
      let E := fun (p w : Fin 13) => ∃ d ∈ S, p = w + d
      let A := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬ E p w
      let T := fun (p w : Fin 13) (k : Fin 26) =>
        decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)
      let F := fun (P : Finset (Fin 13)) (k : Fin (13 + 13)) =>
        decide ((∃ pp ∈ P, k = Fin.castAdd 13 pp) ∨
          (∃ ww : Fin 13, k = Fin.natAdd 13 ww ∧
            (∀ pp ∈ P, ¬ (∃ dd ∈ S, pp = ww + dd))))
      let W := fun (C : Circuit) (a : ℕ) (x : Fin 26 → Bool) =>
        (C.wires (List.ofFn x)).getD a false
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 62 →
        ∀ (a b : Fin (26 + C.size)), a ≠ b →
        (∀ p w, E p w → GateOp.and.eval [W C a.val (T p w), W C b.val (T p w)] = true) →
        (∀ P, (∀ v ∉ P, ∃ w, A P w ∧ E v w) →
          ((∃ w, ∀ p ∈ P, E p w) ∨ (∃ v, ∀ w, A P w → E v w)) →
          GateOp.and.eval [W C a.val (F P), W C b.val (F P)] = false) →
        False)
    (hOr : let S : Finset (Fin 13) := {0, 1, 3, 9}
      let E := fun (p w : Fin 13) => ∃ d ∈ S, p = w + d
      let A := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬ E p w
      let T := fun (p w : Fin 13) (k : Fin 26) =>
        decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)
      let F := fun (P : Finset (Fin 13)) (k : Fin (13 + 13)) =>
        decide ((∃ pp ∈ P, k = Fin.castAdd 13 pp) ∨
          (∃ ww : Fin 13, k = Fin.natAdd 13 ww ∧
            (∀ pp ∈ P, ¬ (∃ dd ∈ S, pp = ww + dd))))
      let W := fun (C : Circuit) (a : ℕ) (x : Fin 26 → Bool) =>
        (C.wires (List.ofFn x)).getD a false
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 62 →
        ∀ (a b : Fin (26 + C.size)), a ≠ b →
        (∀ p w, E p w → GateOp.or.eval [W C a.val (T p w), W C b.val (T p w)] = true) →
        (∀ P, (∀ v ∉ P, ∃ w, A P w ∧ E v w) →
          ((∃ w, ∀ p ∈ P, E p w) ∨ (∃ v, ∀ w, A P w → E v w)) →
          GateOp.or.eval [W C a.val (F P), W C b.val (F P)] = false) →
        False) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  classical
  intro hbad
  have least {P : Circuit → Prop} (h : ∃ C, P C) :
      ∃ C, P C ∧ ∀ D, P D → C.size ≤ D.size := by
    have hex : ∃ n : ℕ, ∃ C, C.size = n ∧ P C := by
      obtain ⟨C, hC⟩ := h
      exact ⟨C.size, C, rfl, hC⟩
    obtain ⟨C, hsize, hC⟩ := Nat.find_spec hex
    refine ⟨C, hC, ?_⟩
    intro D hD
    rw [hsize]
    exact Nat.find_min' hex ⟨D, rfl, hD⟩
  obtain ⟨C, ⟨hmono, hsize, hpos, hneg⟩, hmin⟩ := least hbad
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  have hlen (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step w g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hinput (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = _
      rw [ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have hout0 := hpos 0 0 ⟨0, by decide, by decide⟩
  have hout1 := hpos 1 1 ⟨0, by decide, by decide⟩
  have hstart : 26 ≤ C.output := by
    by_contra h
    have hi : C.output < 26 := by omega
    let i : Fin 26 := ⟨C.output, hi⟩
    have hbit (x : Fin 26 → Bool) : circuitFun 26 C x = x i := by
      change (run C.gates (List.ofFn x)).getD C.output false = x i
      rw [hinput _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
      exact List.getElem_ofFn _
    rw [hbit] at hout0 hout1
    have hdis : ∀ k : Fin 26,
        ¬ ((k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)) ∧
          (k = Fin.castAdd 13 (1 : Fin 13) ∨ k = Fin.natAdd 13 (1 : Fin 13))) := by decide
    exact hdis i ⟨of_decide_eq_true hout0, of_decide_eq_true hout1⟩
  have hend : C.output < 26 + C.gates.length := by
    by_contra h
    change (run C.gates (List.ofFn _)).getD C.output false = true at hout0
    rw [List.getD_eq_default _ _ (by rw [hlen, List.length_ofFn]; omega)] at hout0
    contradiction
  let j := C.output - 26
  have hj : j < C.gates.length := by dsimp [j]; omega
  have hout : C.output = 26 + j := by dsimp [j]; omega
  let g := C.gates[j]
  -- The gates after the output do not affect its value.
  let D : Circuit := ⟨C.gates.take j, 0⟩
  have hprefix : C.gates = (D.gates ++ [g]) ++ C.gates.drop (j + 1) := by
    change C.gates = (C.gates.take j ++ [C.gates[j]]) ++ _
    conv_lhs => rw [← List.take_append_drop (j + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hj]
  have hDmono : Monotone2 D := by
    intro u hu
    exact hmono u (List.mem_of_mem_take hu)
  have hDlength : D.size = j := by
    change (C.gates.take j).length = j
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hDlt : D.size < C.size := by
    change j < C.size at hj
    omega
  have hDsize : D.size ≤ 62 := by omega
  have hgate := hmono g (List.getElem_mem hj)
  have hOp : g.op = .and ∨ g.op = .or := by simpa using hgate.1
  have hroot (x : Fin 26 → Bool) : circuitFun 26 C x =
      g.op.eval (g.inputs.map fun a => (D.wires (List.ofFn x)).getD a false) := by
    let w := run D.gates (List.ofFn x)
    have hw : w.length = C.output := by
      change (run D.gates (List.ofFn x)).length = C.output
      rw [hlen, List.length_ofFn, hout]
      change 26 + (C.gates.take j).length = 26 + j
      rw [List.length_take, Nat.min_eq_left (by omega)]
    change (run C.gates (List.ofFn x)).getD C.output false = _
    conv_lhs => rw [hprefix]
    have happ (as bs : List Gate) (z : List Bool) : run (as ++ bs) z = run bs (run as z) :=
      List.foldl_append
    rw [happ, happ]
    change (run (C.gates.drop (j + 1)) (step w g)).getD C.output false = _
    rw [hinput _ _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
    change (w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]).getD C.output false = _
    rw [← hw]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    rfl
  have hfalse := hneg ∅ (by
    intro v _
    exact ⟨v, by simp, 0, by decide, by simp⟩) (Or.inl ⟨0, by simp⟩)
  have noConstant (b : Bool) (h : ∀ x, circuitFun 26 C x = b) : False := by
    cases b with
    | false =>
      rw [h] at hout0
      contradiction
    | true =>
      rw [h] at hfalse
      contradiction
  let value (a : ℕ) (x : Fin 26 → Bool) := (D.wires (List.ofFn x)).getD a false
  -- A smallest separator cannot use an output gate that only copies another wire.
  have noBypass (a : ℕ) (h : ∀ x, circuitFun 26 C x = value a x) : False := by
    let B : Circuit := ⟨D.gates, a⟩
    have hBsize : B.size = D.size := rfl
    have hBeval (x : Fin 26 → Bool) : circuitFun 26 B x = value a x := rfl
    have hB : C.size ≤ B.size := hmin B (by
      refine ⟨hDmono, by omega, ?_, ?_⟩
      · intro p w hp
        rw [hBeval, ← h]
        exact hpos p w hp
      · intro P hclosed hdeg
        rw [hBeval, ← h]
        exact hneg P hclosed hdeg)
    omega
  have htwo : ∃ a b, g.inputs = [a, b] := by
    cases hin : g.inputs with
    | nil =>
      rcases hOp with hop | hop
      · exact False.elim (noConstant true (fun x => by
          rw [hroot, hin, hop]
          rfl))
      · exact False.elim (noConstant false (fun x => by
          rw [hroot, hin, hop]
          rfl))
    | cons a tail =>
      cases tail with
      | nil =>
        exact False.elim (noBypass a (fun x => by
          rw [hroot, hin]
          change g.op.eval [value a x] = value a x
          rcases hOp with hop | hop <;> rw [hop] <;> cases value a x <;> rfl))
      | cons b rest =>
        cases rest with
        | nil => exact ⟨a, b, rfl⟩
        | cons c more =>
          have h := hgate.2
          rw [hin] at h
          simp only [List.length_cons] at h
          omega
  obtain ⟨a, b, hin⟩ := htwo
  have hpair (x : Fin 26 → Bool) :
      circuitFun 26 C x = g.op.eval [value a x, value b x] := by
    rw [hroot, hin]
    rfl
  have hab : a ≠ b := by
    intro h
    subst b
    exact noBypass a (fun x => by
      rw [hpair]
      rcases hOp with hop | hop <;> rw [hop] <;> cases value a x <;> rfl)
  have beyond (c : ℕ) (hc : 26 + D.size ≤ c) (x : Fin 26 → Bool) :
      value c x = false := by
    change (run D.gates (List.ofFn x)).getD c false = false
    apply List.getD_eq_default
    rw [hlen, List.length_ofFn]
    exact hc
  have ha : a < 26 + D.size := by
    by_contra! h
    rcases hOp with hop | hop
    · exact noConstant false (fun x => by
        rw [hpair, hop, beyond a h x]
        cases value b x <;> rfl)
    · exact noBypass b (fun x => by
        rw [hpair, hop, beyond a h x]
        cases value b x <;> rfl)
  have hb : b < 26 + D.size := by
    by_contra! h
    rcases hOp with hop | hop
    · exact noConstant false (fun x => by
        rw [hpair, hop, beyond b h x]
        cases value a x <;> rfl)
    · exact noBypass a (fun x => by
        rw [hpair, hop, beyond b h x]
        cases value a x <;> rfl)
  let A : Fin (26 + D.size) := ⟨a, ha⟩
  let B : Fin (26 + D.size) := ⟨b, hb⟩
  have hAB : A ≠ B := fun h => hab (congrArg Fin.val h)
  rcases hOp with hop | hop
  · apply hAnd D hDmono hDsize A B hAB
    · intro p w h
      have hp := hpos p w h
      rw [hpair, hop] at hp
      exact hp
    · intro P hclosed hdeg
      have hf := hneg P hclosed hdeg
      rw [hpair, hop] at hf
      exact hf
  · apply hOr D hDmono hDsize A B hAB
    · intro p w h
      have hp := hpos p w h
      rw [hpair, hop] at hp
      exact hp
    · intro P hclosed hdeg
      have hf := hneg P hclosed hdeg
      rw [hpair, hop] at hf
      exact hf
