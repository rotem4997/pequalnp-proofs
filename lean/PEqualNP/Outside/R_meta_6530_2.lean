import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6530_2
  (oneWire :
    let H := fun i j : Fin 13 => (i.val+j.val)%13 ∈ [0,1,3,9]
    let N := fun z : Finset (Fin 13) × Finset (Fin 13) =>
      Maximal (fun p : Finset (Fin 13) × Finset (Fin 13) => ∀ i ∈ p.1, ∀ j ∈ p.2, ¬ H i j) z
    let W := fun (C : Circuit) (A B : Finset (Fin 13)) (w : ℕ) =>
      (C.wires (List.ofFn fun i : Fin 26 => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ A)
        else decide (Fin.ofNat 13 i.val ∈ B))).getD w false
    ∀ (C : Circuit) (a : ℕ), Monotone2 C → 26≤a →
      (∀ i j, H i j → W C {i} {j} a=true) →
      (∀ z, N z → W C z.1 z.2 a=false) → 63≤C.size)
  (twoWires :
    let H := fun i j : Fin 13 => (i.val+j.val)%13 ∈ [0,1,3,9]
    let N := fun z : Finset (Fin 13) × Finset (Fin 13) =>
      Maximal (fun p : Finset (Fin 13) × Finset (Fin 13) => ∀ i ∈ p.1, ∀ j ∈ p.2, ¬ H i j) z
    let W := fun (C : Circuit) (A B : Finset (Fin 13)) (w : ℕ) =>
      (C.wires (List.ofFn fun i : Fin 26 => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ A)
        else decide (Fin.ofNat 13 i.val ∈ B))).getD w false
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → 26≤a → 26≤b →
      (∀ i j, H i j → W C {i} {j} a=true ∧ W C {i} {j} b=true) →
      (∀ z, N z → W C z.1 z.2 a=false ∨ W C z.1 z.2 b=false) →
      (∃ z, N z ∧ W C z.1 z.2 a=true ∧ W C z.1 z.2 b=false) →
      (∃ z, N z ∧ W C z.1 z.2 b=true ∧ W C z.1 z.2 a=false) → 63≤C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (63 : ℕ) ≤ x1.size := by
  let H := fun i j : Fin 13 => (i.val+j.val)%13 ∈ [0,1,3,9]
  let N := fun z : Finset (Fin 13) × Finset (Fin 13) =>
    Maximal (fun p : Finset (Fin 13) × Finset (Fin 13) => ∀ i ∈ p.1, ∀ j ∈ p.2, ¬ H i j) z
  let W := fun (C : Circuit) (A B : Finset (Fin 13)) (w : ℕ) =>
    (C.wires (List.ofFn fun i : Fin 26 => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ A)
      else decide (Fin.ofNat 13 i.val ∈ B))).getD w false
  intro C taps legal length realizes
  let E := fun (A B : Finset (Fin 13)) => ∃ i∈A, ∃ j∈B, H i j
  have edge (i j : Fin 13) (h : H i j) : E {i} {j} :=
    ⟨i,Finset.mem_singleton_self _,j,Finset.mem_singleton_self _,h⟩
  have off (z : Finset (Fin 13) × Finset (Fin 13)) (h : N z) : ¬E z.1 z.2 := by
    rintro ⟨i,hi,j,hj,e⟩
    exact h.1 i hi j hj e
  change ∀ A B, GateOp.and.eval (taps.map (W C A B))=true ↔ E A B at realizes
  have internal (w : ℕ) (accept : ∀ i j, H i j → W C {i} {j} w=true) : 26≤w := by
    by_contra! raw
    let step := fun (u : List Bool) (g : Gate) => u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)]
    have keep (gs : List Gate) (u : List Bool) (h : w<u.length) :
        (gs.foldl step u).getD w false=u.getD w false := by
      induction gs generalizing u with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons,ih (step u g) (by simp [step];omega)]
        exact List.getD_append _ _ _ _ h
    have project (A B : Finset (Fin 13)) : W C A B w=
        (if w<13 then decide (Fin.ofNat 13 w∈A) else decide (Fin.ofNat 13 w∈B)) := by
      let f := fun i : Fin 26 => if i.val<13 then decide (Fin.ofNat 13 i.val∈A) else decide (Fin.ofNat 13 i.val∈B)
      change (C.gates.foldl step (List.ofFn f)).getD w false=_
      rw [keep _ _ (by simpa using raw)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left raw,Option.getD_some,f]
    have zero := accept 0 0 (by decide)
    have other := accept 1 12 (by decide)
    rw [project] at zero other
    by_cases left : w<13
    · simp only [if_pos left,decide_eq_true_eq,Finset.mem_singleton] at zero other
      exact (by decide : (0 : Fin 13)≠1) (zero.symm.trans other)
    · simp only [if_neg left,decide_eq_true_eq,Finset.mem_singleton] at zero other
      exact (by decide : (0 : Fin 13)≠12) (zero.symm.trans other)
  cases taps with
  | nil =>
    obtain ⟨i,hi,rest⟩ := (realizes ∅ ∅).1 rfl
    simp at hi
  | cons a tail =>
    cases tail with
    | nil =>
      have full (A B : Finset (Fin 13)) : W C A B a=true ↔ E A B := by
        have h := realizes A B
        change (W C A B a && true)=true ↔ E A B at h
        simpa only [Bool.and_true] using h
      have pass (i j : Fin 13) (h : H i j) := (full _ _).2 (edge i j h)
      apply oneWire C a legal (internal a pass) pass
      intro z hz
      change W C z.1 z.2 a=false
      cases h : W C z.1 z.2 a with
      | false => rfl
      | true => exact False.elim (off z hz ((full _ _).1 h))
    | cons b rest =>
      have er : rest=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at length; omega)
      subst rest
      have full (A B : Finset (Fin 13)) : (W C A B a=true ∧ W C A B b=true) ↔ E A B := by
        have h := realizes A B
        change (W C A B a && (W C A B b && true))=true ↔ E A B at h
        simpa only [Bool.and_true,Bool.and_eq_true] using h
      have pos (i j : Fin 13) (h : H i j) := (full _ _).2 (edge i j h)
      have neg (z : Finset (Fin 13) × Finset (Fin 13)) (hz : N z) :
          W C z.1 z.2 a=false ∨ W C z.1 z.2 b=false := by
        cases ha : W C z.1 z.2 a with
        | false => exact Or.inl rfl
        | true =>
          cases hb : W C z.1 z.2 b with
          | false => exact Or.inr rfl
          | true => exact False.elim (off z hz ((full _ _).1 ⟨ha,hb⟩))
      classical
      by_cases left : ∀ z, N z → W C z.1 z.2 a=false
      · exact oneWire C a legal (internal a (fun i j h => (pos i j h).1)) (fun i j h => (pos i j h).1) left
      by_cases right : ∀ z, N z → W C z.1 z.2 b=false
      · exact oneWire C b legal (internal b (fun i j h => (pos i j h).2)) (fun i j h => (pos i j h).2) right
      push Not at left right
      obtain ⟨p,hp,ap⟩ := left
      obtain ⟨q,hq,bq⟩ := right
      have av : W C p.1 p.2 a=true := Bool.eq_true_of_not_eq_false ap
      have bv : W C q.1 q.2 b=true := Bool.eq_true_of_not_eq_false bq
      exact twoWires C a b legal (internal a (fun i j h => (pos i j h).1))
        (internal b (fun i j h => (pos i j h).2)) pos neg
        ⟨p,hp,av,(neg p hp).resolve_left (by simp [av])⟩
        ⟨q,hq,bv,(neg q hq).resolve_right (by simp [bv])⟩
