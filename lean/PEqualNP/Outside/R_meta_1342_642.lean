import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.R_meta_1342_642
    (finite : ∃ p : Fin 21 → Bool × Fin 32 × Fin 32,
      (∀ j : Fin 21, (p j).2.1.val < 11 + j.val ∧ (p j).2.2.val < 11 + j.val) ∧
      let C : Circuit := ⟨(List.ofFn p).map (fun t : Bool × Fin 32 × Fin 32 => (⟨if t.1 = true then .and else .or, [t.2.1.val,t.2.2.val]⟩ : Gate)),31⟩
      let w := (List.ofFn p).foldl (fun (w : List ℕ) (t : Bool × Fin 32 × Fin 32) => w ++ [if t.1 = true then w.getD t.2.1.val 0 &&& w.getD t.2.2.val 0 else w.getD t.2.1.val 0 ||| w.getD t.2.2.val 0]) ([2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146] : List ℕ)
      w.getD 31 0 = 65535 ∧
      (List.ofFn (fun j : Fin 21 => decide ((p j).1 = true ∧ w.getD (11+j.val) 0 &&& 1099511562240 ≠ 0))).count true = 2 ∧
      ∀ i j : Fin 21, (p i).1 = true → w.getD (11+i.val) 0 &&& 1099511562240 = 0 →
        (p j).1 = true → ¬ PEqualNP.EdgeOwnership.InCone 11 C i.val j.val)
    (boundary : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
  (∀ k : Fin 40, C.eval (([2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146] : List ℕ).map (fun z => z.testBit k.val)) = (65535 : ℕ).testBit k.val) →
  ∀ x : Fin 11 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 11, (u.val,v.val) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  obtain ⟨p, hread, hout, hjunk, htop⟩ := finite
  let mk : Bool × Fin 32 × Fin 32 → Gate := fun t : Bool × Fin 32 × Fin 32 => (⟨if t.1 = true then .and else .or, [t.2.1.val,t.2.2.val]⟩ : Gate)
  let ns : List ℕ → (Bool × Fin 32 × Fin 32) → List ℕ := fun (w : List ℕ) (t : Bool × Fin 32 × Fin 32) => w ++ [if t.1 = true then w.getD t.2.1.val 0 &&& w.getD t.2.2.val 0 else w.getD t.2.1.val 0 ||| w.getD t.2.2.val 0]
  let bs : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let C : Circuit := ⟨(List.ofFn p).map mk,31⟩
  let cols : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  have hm : Monotone2 C := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hg
    by_cases h : t.1 = true <;> simp [mk,h]
  have encode (k : ℕ) :
      (((List.ofFn p).foldl ns cols).getD 31 0).testBit k =
        C.eval (cols.map (fun z => z.testBit k)) := by
    let bit : ℕ → Bool := fun z => z.testBit k
    have getBit (w : List ℕ) (i : ℕ) :
        (w.map bit).getD i false = bit (w.getD i 0) := by
      simp only [bit,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases h : w[i]? <;> simp [h]
    have stepBit (w : List ℕ) (t : Bool × Fin 32 × Fin 32) :
        (ns w t).map bit = bs (w.map bit) (mk t) := by
      by_cases h : t.1 = true
      · simp only [ns,bs,mk,h,ite_true,List.map_append,List.map_cons,List.map_nil]
        change w.map bit ++ [bit (w.getD t.2.1.val 0 &&& w.getD t.2.2.val 0)] =
          w.map bit ++ [(w.map bit).getD t.2.1.val false && ((w.map bit).getD t.2.2.val false && true)]
        rw [getBit,getBit]
        simp only [bit,Nat.testBit_and,Bool.and_true]
      · simp only [ns,bs,mk,h,ite_false,List.map_append,List.map_cons,List.map_nil]
        change w.map bit ++ [bit (w.getD t.2.1.val 0 ||| w.getD t.2.2.val 0)] =
          w.map bit ++ [(w.map bit).getD t.2.1.val false || ((w.map bit).getD t.2.2.val false || false)]
        rw [getBit,getBit]
        simp only [bit,Nat.testBit_or,Bool.or_false]
    have foldBits : ∀ (ts : List (Bool × Fin 32 × Fin 32)) (w : List ℕ),
        (ts.foldl ns w).map bit = (ts.map mk).foldl bs (w.map bit) := by
      intro ts
      induction ts with
      | nil => intro w; rfl
      | cons t ts ih =>
        intro w
        simp only [List.foldl_cons,List.map_cons]
        rw [ih,stepBit]
    change bit (((List.ofFn p).foldl ns cols).getD 31 0) =
      (((List.ofFn p).map mk).foldl bs (cols.map bit)).getD 31 false
    rw [← foldBits,getBit]
  refine ⟨C,hm,?_,?_⟩
  · apply boundary C hm
    intro k
    have hh := encode k.val
    change ((List.ofFn p).foldl ns cols).getD 31 0 = 65535 at hout
    rw [hout] at hh
    exact hh.symm
  · change ((List.ofFn p).map mk).length ≤ 21
    simp
