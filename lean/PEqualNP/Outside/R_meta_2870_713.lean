import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2870_713
    (classify : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ T : Finset (Fin n), T.card ≤ q → ∀ A B : Fin n → Prop,
      (∀ p l, I p l → A p ∨ B l) → (∀ p, A p → ∃ l ∈ T, I p l) →
      (∀ l ∈ T, ¬ B l) →
      (∀ p, A p ↔ ∃ l ∈ T, I p l) ∧ (∀ l, B l ↔ l ∉ T))
    (compile : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n+j) →
      ∃ F : ℕ → Finset (Finset (Fin n)),
      (∀ i : Fin n, F i = {{i}}) ∧
      (∀ j (hj : j < C.size), ∃ a b, C.gates[j].inputs = [a,b] ∧ a < b ∧ b < n+j ∧
        F (n+j) = (if C.gates[j].op.eval [false,true] then
          (F a).biUnion (fun u => (F b).image (u ∪ ·)) else F a ∪ F b)) ∧
      (∀ xs : List Bool, xs.length = n → ∀ w, (C.wires xs).getD w false = true ↔
        ∀ t ∈ F w, ∃ i ∈ t, xs.getD i.val false = true))
    (floor : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C → C.output < n+n+C.size →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n+n+j) →
      (∀ p l, I p l → circuitFun (n+n) C (fun i => decide (i=Fin.castAdd n p ∨ i=Fin.natAdd n l)) = true) →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) → 4*q^2+2+n ≤ 2*C.size)
    (bound : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      250 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (F : ℕ → Finset (Finset (Fin (n+n)))), o < n+n+s →
      (∀ i : Fin (n+n), F i = {{i}}) →
      (∀ j < s, ∃ a b, a < b ∧ b < (n+n)+j ∧
        (F ((n+n)+j) = F a ∪ F b ∨ F ((n+n)+j) = (F a).biUnion (fun u => (F b).image (u ∪ ·)))) →
      (∀ t ∈ F o, ∀ p l, I p l → Fin.castAdd n p ∈ t ∨ Fin.natAdd n l ∈ t) →
      (∀ T : Finset (Fin n), T.card ≤ q → ∃ t ∈ F o,
        (∀ p, Fin.castAdd n p ∈ t ↔ ∃ l ∈ T, I p l) ∧ (∀ l, Fin.natAdd n l ∈ t ↔ l ∉ T)) →
      (∃ j < s, ∃ a b, a < b ∧ b < n+n+j ∧ F (n+n+j) = F a ∪ F b ∧
        ∃ d : Bool, ∀ w ∈ [a,b], ∃ z : Fin n → Bool,
          let row := fun c : Bool => if d then List.ofFn z ++ List.replicate n c else List.replicate n c ++ List.ofFn z
          let hit := fun c : Bool => ∀ t ∈ F w, ∃ i ∈ t, (row c).getD i.val false = true
          ¬ (hit false ↔ hit true)) → n*q ≤ 100*s) :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [_x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q n I dec C hq hn hdeg hline mono out order yes no marks sub nonempty marked _
  classical
  by_cases smallOrder : q ≤ 249
  · have low := floor q n I C (by omega) hn hdeg hline mono out order yes no
    have cap := Nat.mul_le_mul_right (q^2) (show q ≤ 249 by omega)
    rw [hn] at low ⊢
    nlinarith
  have large : 250 ≤ q := by omega
  obtain ⟨F, atoms, steps, semantics⟩ := compile (n+n) C mono order
  have computes (x : Fin (n+n) → Bool) : C.eval (List.ofFn x) = true ↔
      ∀ t ∈ F C.output, ∃ i ∈ t, x i = true := by
    change (C.wires (List.ofFn x)).getD C.output false = true ↔ _
    simpa using semantics (List.ofFn x) List.length_ofFn C.output
  have cover (t) (ht : t ∈ F C.output) (p l : Fin n) (hi : I p l) :
      Fin.castAdd n p ∈ t ∨ Fin.natAdd n l ∈ t := by
    obtain ⟨i, hit, lit⟩ := (computes _).mp (yes p l hi) t ht
    rcases of_decide_eq_true lit with rfl | rfl
    · exact Or.inl hit
    · exact Or.inr hit
  refine bound q n I large hn hdeg hline C.size C.output F out atoms ?_ cover ?_ ?_
  · intro j hj
    obtain ⟨a,b,_,ab,bj,eq⟩ := steps j hj
    refine ⟨a,b,ab,bj,?_⟩
    split at eq <;> tauto
  · intro T small
    let x : Fin (n+n) → Bool := Fin.addCases
      (fun p => decide (¬ ∃ l ∈ T, I p l)) (fun l => decide (l ∈ T))
    have exprP (p : Fin n) : x (Fin.castAdd n p) = decide (¬ ∃ l ∈ T, I p l) := Fin.addCases_left _
    have exprL (l : Fin n) : x (Fin.natAdd n l) = decide (l ∈ T) := Fin.addCases_right _
    have neg : C.eval (List.ofFn x) = false := by
      apply no x
      · simpa only [exprL, decide_eq_true_eq, Fintype.card_coe] using small
      · rintro ⟨p,l,inc,hp,hl⟩
        rw [exprP] at hp
        rw [exprL] at hl
        exact (of_decide_eq_true hp) ⟨l, of_decide_eq_true hl, inc⟩
    have missing : ¬ (∀ t ∈ F C.output, ∃ i ∈ t, x i = true) := by
      intro allTrue
      exact Bool.noConfusion (neg.symm.trans ((computes x).mpr allTrue))
    push Not at missing
    obtain ⟨t, ht, silent⟩ := missing
    refine ⟨t, ht, classify q n I hdeg hline T small _ _ (cover t ht) ?_ ?_⟩
    · intro p hp
      by_contra outside
      exact silent _ hp ((exprP p).trans (decide_eq_true outside))
    · intro l hl ht'
      exact silent _ ht' ((exprL l).trans (decide_eq_true hl))
  · obtain ⟨j,hj⟩ := Finset.card_pos.mp nonempty
    have range := Finset.mem_range.mp (sub hj)
    have someGate := List.getElem?_eq_getElem (l := C.gates) range
    obtain ⟨kind,side⟩ := (marked j _ someGate).mp hj
    obtain ⟨a,b,ins,ab,bj,eq⟩ := steps j range
    refine ⟨j, range, a, b, ab, bj, ?_, ?_⟩
    · rw [kind] at eq
      exact eq
    rcases side with lines | points
    · refine ⟨true, ?_⟩
      intro w hw
      obtain ⟨z,diff⟩ := lines w (ins ▸ hw)
      refine ⟨z, ?_⟩
      dsimp only [ite_true, eq_self]
      rwa [← semantics _ (by simp) w, ← semantics _ (by simp) w, ← Bool.eq_iff_iff]
    · refine ⟨false, ?_⟩
      intro w hw
      obtain ⟨z,diff⟩ := points w (ins ▸ hw)
      refine ⟨z, ?_⟩
      dsimp only [Bool.false_eq_true, ite_false]
      rwa [← semantics _ (by simp) w, ← semantics _ (by simp) w, ← Bool.eq_iff_iff]
