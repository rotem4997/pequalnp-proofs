import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Test positive row outputs on single edges. For negative tests, select a set
-- of points and turn on every line they miss. Clear the three special lines
-- when testing the auxiliary output at zero. Wire monotonicity then covers
-- every input between a lower and an upper test.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_4966_1
    (mono : ∀ (C : Circuit), Monotone2 C → ∀ (a b : Fin 25 → Bool),
      (∀ i, a i = true → b i = true) → ∀ w : ℕ,
      (C.wires (List.ofFn a)).getD w false = true →
      (C.wires (List.ofFn b)).getD w false = true)
    (bank :
      let P := fun p : Fin 25 => p.val < 12 ∧ p.val ∉ ([0,2,8] : List ℕ)
      let I := fun p l : Fin 25 => P p ∧ 12 ≤ l.val ∧
        (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ)
      let T := ([13,15,21] : List (Fin 25))
      let hi := fun (s : Finset (Fin 25)) (clear : Bool) (j : Fin 25) =>
        decide ((P j → j ∈ s) ∧ (∀ p ∈ s, ¬ I p j) ∧ (clear = true → j ∉ T))
      ∃ (C : Circuit) (w : Fin 25 → ℕ) (q : ℕ),
        let V := fun (x : Fin 25 → Bool) (k : ℕ) => (C.wires (List.ofFn x)).getD k false
        Monotone2 C ∧ C.size ≤ 28 ∧ (∀ i, w i < 25+C.size) ∧ q < 25+C.size ∧
        (∃ p l, I p l ∧ V (fun j => decide (j=l)) (w p) = false) ∧
        (∀ p l, I p l → V (fun j => decide (j=p ∨ j=l)) (w p) = true) ∧
        (∀ t ∈ T, V (fun j => decide (j=t)) q = true) ∧
        ∀ s, (∀ p ∈ s, P p) →
          (∀ p ∈ s, V (hi s false) (w p) = false) ∧ V (hi s true) q = false) :
    let I := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧
      (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)
    ∃ (B : Circuit) (w : Fin 25 → ℕ) (q : ℕ), Monotone2 B ∧ B.size ≤ 28 ∧
      (∀ i, w i < 25+B.size) ∧ q < 25+B.size ∧
      (∃ p l, I p l ∧ (B.wires (List.ofFn (fun j : Fin 25 => decide (j=l)))).getD (w p) false = false) ∧
      ∀ x : Fin 25 → Bool,
        let v := fun a => (B.wires (List.ofFn x)).getD a false
        (∀ p l, I p l → x p = true → x l = true → v (w p) = true) ∧
        ((¬ ∃ p l, I p l ∧ x p = true ∧ x l = true) →
          (∀ p, p.val < 12 → p.val ∉ ([0,2,8] : List ℕ) → x p = true → v (w p) = false) ∧
          v q = (x 13 || x 15 || x 21)) := by
  extract_lets P I T hi at bank
  obtain ⟨C,w,q,model,size,wb,qb,single,pairs,ones,upper⟩ := bank
  obtain ⟨p,l,hit,hval⟩ := single
  change I p l at hit
  refine ⟨C,w,q,model,size,wb,qb,⟨p,l,⟨hit.1.1,hit.2.1,hit.2.2,hit.1.2⟩,hval⟩,?_⟩
  intro x
  constructor
  · intro a b hab ha hb
    apply mono C model _ x _ (w a) (pairs a b ⟨⟨hab.1,hab.2.2.2⟩,hab.2.1,hab.2.2.1⟩)
    intro j hj
    rcases of_decide_eq_true hj with rfl | rfl
    · exact ha
    · exact hb
  · intro independent
    let s := Finset.univ.filter (fun j : Fin 25 => P j ∧ x j = true)
    have mem (j : Fin 25) : j ∈ s ↔ P j ∧ x j = true := by simp [s]
    obtain ⟨rows,zero⟩ := upper s (fun j hj => ((mem j).mp hj).1)
    have cover (clear : Bool) (off : clear = true → ∀ j ∈ T, x j = false) :
        ∀ j, x j = true → hi s clear j = true := by
      intro j hj
      apply decide_eq_true
      refine ⟨fun hp => (mem j).mpr ⟨hp,hj⟩, ?_, ?_⟩
      · intro a ha hadj
        apply independent
        exact ⟨a,j,⟨hadj.1.1,hadj.2.1,hadj.2.2,hadj.1.2⟩,((mem a).mp ha).2,hj⟩
      · intro hc hT
        rw [off hc j hT] at hj
        contradiction
    constructor
    · intro a hlt hkeep ha
      have h0 := rows a ((mem a).mpr ⟨⟨hlt,hkeep⟩,ha⟩)
      change (C.wires (List.ofFn x)).getD (w a) false = false
      cases h : (C.wires (List.ofFn x)).getD (w a) false with
      | false => rfl
      | true =>
        have h1 := mono C model x (hi s false) (cover false (fun hc => by cases hc)) (w a) h
        change (C.wires (List.ofFn (hi s false))).getD (w a) false = false at h0
        rw [h0] at h1
        contradiction
    · by_cases ht : ∃ t ∈ T, x t = true
      · obtain ⟨t,ht,hx⟩ := ht
        have leOne : ∀ j : Fin 25, decide (j=t) = true → x j = true := by
          intro j hj
          rwa [of_decide_eq_true hj]
        have h1 := mono C model (fun j => decide (j=t)) x leOne q (ones t ht)
        change (C.wires (List.ofFn x)).getD q false = _
        rw [h1]
        simp only [T, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl <;> simp [hx]
      · have off (t : Fin 25) (h : t ∈ T) : x t = false := by
          cases hx : x t with
          | false => rfl
          | true => exact (ht ⟨t,h,hx⟩).elim
        have hz : (C.wires (List.ofFn x)).getD q false = false := by
          cases h : (C.wires (List.ofFn x)).getD q false with
          | false => rfl
          | true =>
            have h1 := mono C model x (hi s true) (cover true (fun _ => off)) q h
            change (C.wires (List.ofFn (hi s true))).getD q false = false at zero
            rw [zero] at h1
            contradiction
        change (C.wires (List.ofFn x)).getD q false = _
        rw [hz,off 13 (by decide),off 15 (by decide),off 21 (by decide)]
        rfl
