import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2870_819
    (floor : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      101 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C →
      (∀ p l, I p l → circuitFun (n+n) C
        (fun i => decide (i=Fin.castAdd n p ∨ i=Fin.natAdd n l)) = true) →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) → 3*n ≤ C.size)
    (detect : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      301 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C →
      C.size = (n*q-1)/100 → C.output < n+n+C.size →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a<b ∧ b<n+n+j) →
      (∃ g ∈ C.gates, g.op = GateOp.and ∧ ∃ d : Bool,
        ∀ i ∈ g.inputs, ∃ x : Fin n → Bool,
          let row := fun b => if d then List.ofFn x ++ List.replicate n b else List.replicate n b ++ List.ofFn x
          (C.wires (row false)).getD i false ≠ (C.wires (row true)).getD i false) →
      (∀ p l, I p l → circuitFun (n+n) C
        (fun i => decide (i=Fin.castAdd n p ∨ i=Fin.natAdd n l)) = true) →
      ∃ T : Finset (Fin n), T.card ≤ q ∧
        circuitFun (n+n) C (Fin.addCases (fun p => decide (¬∃ l ∈ T, I p l))
          (fun l => decide (l ∈ T))) = true) :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [_x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q n I dec C big order degrees join hm out inputs yes no marks sub nonempty marked _
  classical
  by_contra! short
  have lo := floor q n I C (by omega) order degrees join hm yes no
  have large : 301 ≤ q := by
    by_contra! small
    have scale := Nat.mul_le_mul_left n (show q ≤ 300 by omega)
    omega
  let cap := (n*q-1)/100
  have bound : C.size ≤ cap := by dsimp [cap]; omega
  let dummy : Gate := ⟨GateOp.or,[0,1]⟩
  let pad := List.replicate (cap-C.size) dummy
  let D : Circuit := ⟨C.gates ++ pad,C.output⟩
  have sizeD : D.size = cap := by
    change (C.gates ++ List.replicate (cap-C.size) dummy).length = cap
    rw [List.length_append,List.length_replicate]
    change C.size+(cap-C.size) = cap
    omega
  have monoD : Monotone2 D := by
    intro g hg
    rcases List.mem_append.mp hg with orig | extra
    · exact hm g orig
    · have eq : g = dummy := (List.mem_replicate.mp extra).2
      subst g
      simp [dummy]
  have normD (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g) :
      ∃ a b, g.inputs = [a,b] ∧ a<b ∧ b<n+n+j := by
    change (C.gates ++ pad)[j]? = some g at hg
    by_cases initial : j < C.gates.length
    · rw [List.getElem?_append_left initial] at hg
      exact inputs j g hg
    · rw [List.getElem?_append_right (Nat.le_of_not_gt initial)] at hg
      have eq : g = dummy := (List.mem_replicate.mp (List.mem_of_getElem? hg)).2
      subst g
      exact ⟨0,1,rfl,by decide,by omega⟩
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have sizeW (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length+gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have keep (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (gs.foldl step xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step xs g) (by simp [step]; omega)]
      simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
  have preserve (xs : List Bool) (len : xs.length = n+n) (i : ℕ) (hi : i<n+n+C.size) :
      (D.wires xs).getD i false = (C.wires xs).getD i false := by
    change ((C.gates ++ pad).foldl step xs).getD i false = (C.gates.foldl step xs).getD i false
    rw [List.foldl_append]
    apply keep
    rw [sizeW,len]
    exact hi
  have evalEq (x : Fin (n+n) → Bool) : circuitFun (n+n) D x = circuitFun (n+n) C x :=
    preserve (List.ofFn x) List.length_ofFn C.output out
  obtain ⟨j,hj⟩ := Finset.card_pos.mp nonempty
  have jlt : j<C.gates.length := Finset.mem_range.mp (sub hj)
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_some_iff.mpr ⟨jlt,rfl⟩
  have hmarked := (marked j g hg).mp hj
  obtain ⟨a,b,gins,ab,bj⟩ := inputs j g hg
  have smallWire (i : ℕ) (hi : i ∈ g.inputs) : i < n+n+C.size := by
    simp [gins] at hi
    change i < n+n+C.gates.length
    omega
  have markedD : ∃ g ∈ D.gates, g.op = GateOp.and ∧ ∃ d : Bool,
      ∀ i ∈ g.inputs, ∃ x : Fin n → Bool,
        let row := fun b => if d then List.ofFn x ++ List.replicate n b else List.replicate n b ++ List.ofFn x
        (D.wires (row false)).getD i false ≠ (D.wires (row true)).getD i false := by
    refine ⟨g,List.mem_append_left _ (List.mem_of_getElem? hg),hmarked.1,?_⟩
    rcases hmarked.2 with left | right
    · refine ⟨true,?_⟩
      intro i hi
      obtain ⟨x,hx⟩ := left i hi
      refine ⟨x,?_⟩
      change (D.wires (List.ofFn x ++ List.replicate n false)).getD i false ≠
        (D.wires (List.ofFn x ++ List.replicate n true)).getD i false
      rw [preserve _ (by simp) i (smallWire i hi),preserve _ (by simp) i (smallWire i hi)]
      exact hx
    · refine ⟨false,?_⟩
      intro i hi
      obtain ⟨x,hx⟩ := right i hi
      refine ⟨x,?_⟩
      change (D.wires (List.replicate n false ++ List.ofFn x)).getD i false ≠
        (D.wires (List.replicate n true ++ List.ofFn x)).getD i false
      rw [preserve _ (by simp) i (smallWire i hi),preserve _ (by simp) i (smallWire i hi)]
      exact hx
  obtain ⟨T,small,trueOn⟩ := detect q n I D large order degrees join monoD sizeD
    (by change C.output < n+n+D.size; omega) normD markedD
    (fun p l inc => (evalEq _).trans (yes p l inc))
  let x : Fin (n+n) → Bool := Fin.addCases (fun p => decide (¬∃ l ∈ T, I p l)) (fun l => decide (l ∈ T))
  have hp (p : Fin n) : x (Fin.castAdd n p) = decide (¬∃ l ∈ T, I p l) := Fin.addCases_left _
  have hl (l : Fin n) : x (Fin.natAdd n l) = decide (l ∈ T) := Fin.addCases_right _
  have neg : circuitFun (n+n) C x = false := by
    apply no
    · simpa only [hl,decide_eq_true_eq,Fintype.card_coe] using small
    · rintro ⟨p,l,inc,onP,onL⟩
      exact (of_decide_eq_true ((hp p).symm.trans onP)) ⟨l,of_decide_eq_true ((hl l).symm.trans onL),inc⟩
  exact Bool.noConfusion (neg.symm.trans ((evalEq x).symm.trans trueOn))
