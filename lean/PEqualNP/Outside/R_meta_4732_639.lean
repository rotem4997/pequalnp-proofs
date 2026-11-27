import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection

-- Fix the trailing input and retain the circuit size.
-- Among the smallest separators, minimize the number of nested AND pairs.
-- The elimination premise removes degenerate gates and nested ANDs that
-- reject every quadrangle. Every remaining nested AND has a negative witness.
-- The first two premises specialize L-meta-2059 and L-meta-2061.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4732_639
    (flat :
      let S := singerLines3
      let neg := fun Q : Finset (Fin 13) => incidenceInput Q (missLines S Q)
      let good := fun (omitted : Fin 13) (C : Circuit) =>
        Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p ∈ S l → p ≠ 0 ∨ l ≠ omitted →
          C.eval (incidenceInput {p} {l}) = true) ∧
        ∀ Q, IsQuadrangle S Q → C.eval (neg Q) = false
      ∀ omitted C, good omitted C →
        (¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
        63 ≤ C.size)
    (clean :
      let S := singerLines3
      let neg := fun Q : Finset (Fin 13) => incidenceInput Q (missLines S Q)
      let good := fun (omitted : Fin 13) (C : Circuit) =>
        Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p ∈ S l → p ≠ 0 ∨ l ≠ omitted →
          C.eval (incidenceInput {p} {l}) = true) ∧
        ∀ Q, IsQuadrangle S Q → C.eval (neg Q) = false
      ∀ omitted C, good omitted C →
        (∀ D, good omitted D → C.size ≤ D.size) →
        (∀ D, good omitted D → D.size = C.size → andPairs 26 C ≤ andPairs 26 D) →
        (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) ∧
        (∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → InCone 26 C i j →
        ∃ Q, IsQuadrangle S Q ∧ (C.wires (neg Q)).getD (26 + i) false = true))
    (dirty :
      let S := singerLines3
      let neg := fun Q : Finset (Fin 13) => incidenceInput Q (missLines S Q)
      let good := fun (omitted : Fin 13) (C : Circuit) =>
        Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p ∈ S l → p ≠ 0 ∨ l ≠ omitted →
          C.eval (incidenceInput {p} {l}) = true) ∧
        ∀ Q, IsQuadrangle S Q → C.eval (neg Q) = false
      ∀ omitted C, good omitted C → C.size < 63 →
        (∀ D, good omitted D → C.size ≤ D.size) →
        (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
        (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        (∀ i j, (gateAt C i).op = .and → (gateAt C j).op = .and → InCone 26 C i j →
        ∃ Q, IsQuadrangle S Q ∧ (C.wires (neg Q)).getD (26 + i) false = true) → False)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) → (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ (0 : Fin (13 : ℕ)) ∨ x11 ≠ x6 → x5.eval (x2 x10 x11 ++ [x7]) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x5.eval (x3 x11 ++ [x7]) = Bool.false) → (63 : ℕ) ≤ x5.size := by
  intro d posRaw negRaw quadRaw C omitted b hm hr hp hn
  have inc : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ d := by
    dsimp only [d]
    decide
  have quad (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔
      Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ d)).card ≤ 2 := by
    have filterEq (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun p => p - l ∈ d) := by
      ext p
      simp [inc p l]
    change (Q.card = 4 ∧ ∀ l, (Q ∩ singerLines3 l).card ≤ 2) ↔ _
    simp_rw [filterEq]
  have miss (Q : Finset (Fin 13)) (l : Fin 13) : l ∈ missLines singerLines3 Q ↔
      ∀ p ∈ Q, p - l ∉ d := by
    change l ∈ Finset.univ.filter (fun a => Disjoint (singerLines3 a) Q) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
    constructor
    · exact fun h p hp hpl => h ((inc p l).mpr hpl) hp
    · exact fun h p hpl hp => h p hp ((inc p l).mp hpl)
  let pos (p l : Fin 13) := incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13))
  let neg (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
  have negEq (Q : Finset (Fin 13)) : neg Q =
      List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ d)) := by
    have eq : (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) =
        (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ d)) := by
      funext l
      exact decide_eq_decide.mpr (miss Q l)
    exact congrArg (fun f : Fin 13 → Bool =>
      List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++ List.ofFn f) eq
  have inputLen (P L : Finset (Fin 13)) : (incidenceInput P L).length = 26 := by
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ L))).length = 26
    simp
  have hp' (p l : Fin 13) (h : p ∈ singerLines3 l) (he : p ≠ 0 ∨ l ≠ omitted) :
      C.eval (pos p l ++ [b]) = true := by
    change C.eval ((List.ofFn (fun u : Fin 13 => decide (u ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun v : Fin 13 => decide (v ∈ ({l} : Finset (Fin 13))))) ++ [b]) = true
    simpa only [posRaw, Finset.mem_singleton] using hp p l ((inc p l).mp h) he
  have hn' (Q : Finset (Fin 13)) (h : IsQuadrangle singerLines3 Q) :
      C.eval (neg Q ++ [b]) = false := by
    rw [negEq]
    exact hn Q ((quad Q).mp h)
  have hn0 : IsQuadrangle singerLines3 ({0, 1, 2, 5} : Finset (Fin 13)) := by decide
  have hp0 : (1 : Fin 13) ∈ singerLines3 1 := by decide
  have hr' : ReadsBack 27 C := by
    intro j hj i hi
    have eq : gateAt C j = C.gates[j] := by
      change C.gates.getD j ⟨.or, []⟩ = C.gates[j]
      simp [List.getD_eq_getElem?_getD, hj]
    rw [eq] at hi
    exact hr ⟨j, hj⟩ i hi
  have hout : C.output ≠ 26 := by
    intro eq
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have keep (gs : List Gate) (w : List Bool) (hw : 26 < w.length) :
        (gs.foldl step w).getD 26 false = w.getD 26 false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hw
    have ev (x : List Bool) (hx : x.length = 26) : C.eval (x ++ [b]) = b := by
      change (C.gates.foldl step (x ++ [b])).getD C.output false = b
      rw [eq, keep _ _ (by simp [hx]), ← hx]
      simp
    have p := hp' 1 1 hp0 (Or.inl (by decide))
    have n := hn' {0, 1, 2, 5} hn0
    rw [ev _ (inputLen _ _)] at p
    rw [ev _ (inputLen _ _)] at n
    exact Bool.false_ne_true (n.symm.trans p)
  have normalizeTail (C : Circuit) (b : Bool) (hm : Monotone2 C) (hr : ReadsBack 27 C)
    (hout : C.output ≠ 26) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size = C.size ∧
      ∀ x : List Bool, x.length = 26 → D.eval x = C.eval (x ++ [b]) := by
    classical
    let reindex (w : ℕ) := if w < 26 then w else w - 1
    let trim (g : Gate) : Gate :=
      if 26 ∈ g.inputs ∧ ((g.op = .and ∧ b = false) ∨ (g.op = .or ∧ b = true)) then
        if b then ⟨.and, []⟩ else ⟨.or, []⟩
      else ⟨g.op, (g.inputs.filter (· != 26)).map reindex⟩
    let D : Circuit := ⟨C.gates.map trim, reindex C.output⟩
    have operands (g : Gate) (w : ℕ) (hw : w ∈ (trim g).inputs) :
        ∃ i ∈ g.inputs, i ≠ 26 ∧ w = reindex i := by
      unfold trim at hw
      split at hw
      · split at hw <;> simp at hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        have h := List.mem_filter.mp hi
        exact ⟨i, h.1, by simpa using h.2, rfl⟩
    have legal (g : Gate) (hg : g ∈ C.gates) :
        (trim g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (trim g).inputs.length ≤ 2 := by
      unfold trim
      split
      · split <;> simp
      · exact ⟨(hm g hg).1, by simpa using
          (List.length_filter_le (· != 26) g.inputs).trans (hm g hg).2⟩
    have hsz : D.gates.length = C.gates.length := List.length_map trim
    have atGate (E : Circuit) (j : ℕ) (hj : j < E.gates.length) :
        gateAt E j = E.gates[j] := by
      change E.gates.getD j ⟨.or, []⟩ = E.gates[j]
      simp [List.getD_eq_getElem?_getD, hj]
    refine ⟨D, ?_, ?_, hsz, ?_⟩
    · intro g hg
      change g ∈ C.gates.map trim at hg
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hg
      exact legal source hsource
    · intro j hj w hw
      have hjC : j < C.gates.length := hsz ▸ hj
      rw [atGate D j hj] at hw
      change w ∈ (C.gates.map trim)[j].inputs at hw
      rw [List.getElem_map] at hw
      obtain ⟨i, hi, hi26, rfl⟩ := operands _ _ hw
      have lt := hr j hjC i (by rw [atGate C j hjC]; exact hi)
      dsimp only [reindex]
      split <;> omega
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let consistent (big small : List Bool) : Prop :=
      big.length = small.length + 1 ∧ 26 ≤ small.length ∧ big.getD 26 false = b ∧
        ∀ i ≠ 26, big.getD i false = small.getD (reindex i) false
    have insertion (big small : List Bool) (h : consistent big small) (bit : Bool) :
        consistent (big ++ [bit]) (small ++ [bit]) := by
      obtain ⟨hlen, hmin, hb, hbits⟩ := h
      refine ⟨by simp [hlen], by simp; omega, ?_, ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega), hb]
      · intro i hi
        have less : i < big.length ↔ reindex i < small.length := by
          unfold reindex
          split <;> omega
        by_cases il : i < big.length
        · rw [List.getD_append _ _ _ _ il, List.getD_append _ _ _ _ (less.mp il), hbits i hi]
        · have hs := Nat.le_of_not_lt (fun h => il (less.mpr h))
          have hshift : i - big.length = reindex i - small.length := by
            unfold reindex
            split <;> omega
          rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt il),
            List.getD_append_right _ _ _ _ hs, hshift]
    have andInputs (big small : List Bool) (h : consistent big small) (is : List ℕ) :
        (is.map (fun i => big.getD i false)).all id =
          ((if 26 ∈ is then b else true) &&
            (((is.filter (· != 26)).map reindex).map (fun i => small.getD i false)).all id) := by
      induction is with
      | nil => simp
      | cons i is ih =>
        by_cases eq : i = 26
        · subst i
          simp only [List.map_cons, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
            List.mem_cons, true_or, ite_true, List.all_cons, id_eq, h.2.2.1, ih]
          cases b <;> simp
        · simp only [List.map_cons, List.filter_cons, bne_iff_ne, ite_eq_left eq, List.mem_cons,
            Ne.symm eq, false_or, List.all_cons, id_eq, h.2.2.2 i eq, ih]
          exact Bool.and_left_comm _ _ _
    have orInputs (big small : List Bool) (h : consistent big small) (is : List ℕ) :
        (is.map (fun i => big.getD i false)).any id =
          ((if 26 ∈ is then b else false) ||
            (((is.filter (· != 26)).map reindex).map (fun i => small.getD i false)).any id) := by
      induction is with
      | nil => simp
      | cons i is ih =>
        by_cases eq : i = 26
        · subst i
          simp only [List.map_cons, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
            List.mem_cons, true_or, ite_true, List.any_cons, id_eq, h.2.2.1, ih]
          cases b <;> simp
        · simp only [List.map_cons, List.filter_cons, bne_iff_ne, ite_eq_left eq, List.mem_cons,
            Ne.symm eq, false_or, List.any_cons, id_eq, h.2.2.2 i eq, ih]
          exact Bool.or_left_comm _ _ _
    have andEval (bits : List Bool) : GateOp.and.eval bits = bits.all id := rfl
    have orEval (bits : List Bool) : GateOp.or.eval bits = bits.any id := rfl
    have evalGate (g : Gate) (hg : g ∈ C.gates) (big small : List Bool) (h : consistent big small) :
        g.op.eval (g.inputs.map fun i => big.getD i false) =
          (trim g).op.eval ((trim g).inputs.map fun i => small.getD i false) := by
      have casesOp : g.op = .and ∨ g.op = .or := (hm g hg).1
      rcases g with ⟨op, inputs⟩
      rcases casesOp with hop | hop
      · change op = .and at hop
        subst op
        have ha := andInputs big small h inputs
        by_cases tail : 26 ∈ inputs <;> cases b <;> simp [trim, andEval, orEval, tail] at ha ⊢ <;> exact ha
      · change op = .or at hop
        subst op
        have ho := orInputs big small h inputs
        by_cases tail : 26 ∈ inputs <;> cases b <;> simp [trim, andEval, orEval, tail] at ho ⊢ <;> exact ho
    have fold (gs : List Gate) (hgs : ∀ g ∈ gs, g ∈ C.gates)
        (big small : List Bool) (h : consistent big small) :
        consistent (gs.foldl step big) ((gs.map trim).foldl step small) := by
      induction gs generalizing big small with
      | nil => exact h
      | cons g gs ih =>
        simp only [List.foldl_cons, List.map_cons]
        apply ih (fun j hj => hgs j (List.mem_cons_of_mem _ hj))
        dsimp only [step]
        rw [evalGate g (hgs g List.mem_cons_self) big small h]
        exact insertion big small h _
    intro x hx
    have start : consistent (x ++ [b]) x := by
      refine ⟨by simp, by omega, ?_, ?_⟩
      · rw [← hx]; simp
      · intro i hi
        by_cases il : i < 26
        · rw [List.getD_append _ _ _ _ (by omega)]
          simp [reindex, il]
        · rw [List.getD_eq_default _ _ (by simp [hx]; omega), List.getD_eq_default]
          simp [reindex, il, hx]
          omega
    exact ((fold C.gates (fun _ h => h) _ _ start).2.2.2 C.output hout).symm
  obtain ⟨D, hDmono, hDback, hsize, hD⟩ := normalizeTail C b hm hr' hout
  let good (E : Circuit) : Prop := Monotone2 E ∧ ReadsBack 26 E ∧
    (∀ p l : Fin 13, p ∈ singerLines3 l → p ≠ 0 ∨ l ≠ omitted →
      E.eval (pos p l) = true) ∧
    ∀ Q, IsQuadrangle singerLines3 Q → E.eval (neg Q) = false
  have Dgood : good D := by
    refine ⟨hDmono, hDback, ?_, ?_⟩
    · intro p l hi he
      rw [hD _ (inputLen _ _)]
      exact hp' p l hi he
    · intro Q hQ
      rw [hD _ (inputLen _ _)]
      exact hn' Q hQ
  classical
  by_contra! small
  have feasible : ∃ n : ℕ, ∃ E : Circuit, good E ∧ E.size = n :=
    ⟨D.size, D, Dgood, rfl⟩
  obtain ⟨E, Egood, Esize⟩ := Nat.find_spec feasible
  have Emin (F : Circuit) (hF : good F) : E.size ≤ F.size := by
    rw [Esize]
    exact Nat.find_min' feasible ⟨F, hF, rfl⟩
  have budget : E.size < 63 := (Emin D Dgood).trans_lt (hsize ▸ small)
  have feasiblePairs : ∃ k : ℕ, ∃ F : Circuit,
      good F ∧ F.size = E.size ∧ andPairs 26 F = k :=
    ⟨andPairs 26 E, E, Egood, rfl, rfl⟩
  obtain ⟨F, Fgood, Fsize, Fpairs⟩ := Nat.find_spec feasiblePairs
  have Fmin (G : Circuit) (hG : good G) : F.size ≤ G.size := Fsize ▸ Emin G hG
  have FpairMin (G : Circuit) (hG : good G) (sizeEq : G.size = F.size) :
      andPairs 26 F ≤ andPairs 26 G := by
    rw [Fpairs]
    exact Nat.find_min' feasiblePairs ⟨G, hG, sizeEq.trans Fsize, rfl⟩
  have Fbudget : F.size < 63 := Fsize ▸ budget
  by_cases nested : ∃ i j, (gateAt F i).op = .and ∧ (gateAt F j).op = .and ∧ InCone 26 F i j
  · obtain ⟨fanIn, witnesses⟩ := clean omitted F Fgood Fmin FpairMin
    exact dirty omitted F Fgood Fbudget Fmin nested fanIn witnesses
  · exact (Nat.not_le_of_lt Fbudget) (flat omitted F Fgood nested)
