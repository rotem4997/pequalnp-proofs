import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1988_2
    (hgeom : ∀ (S : Finset (Fin 13)), 4 ≤ S.card →
      (let T : Finset (Fin 13) := Finset.univ.filter
        (fun l : Fin 13 => ∀ p ∈ S, ¬ ((p.val + l.val) % 13 ∈ [0,1,3,9])); T.card ≤ 3))
    (hcore : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → outs.length ≤ 2 →
      (∀ P L : Finset (Fin 13),
        PEqualNP.CircuitLowerBounds.GateOp.and.eval (outs.map (fun k =>
          (C.wires (List.ofFn (fun i : Fin 26 =>
            if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P)
            else decide (Fin.ofNat 13 i.val ∈ L)))).getD k false)) = true ↔
          ∃ p ∈ P, ∃ l ∈ L, (p.val + l.val) % 13 ∈ [0,1,3,9]) → 63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C outs hC hlen htests
  have eval_and (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
  have eval_or (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := rfl
  let inc (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ [0,1,3,9]
  letI : DecidableRel inc := by intro p l; unfold inc; infer_instance
  let avoid (P : Finset (Fin 13)) : Finset (Fin 13) :=
    Finset.univ.filter (fun l => ∀ p ∈ P, ¬ inc p l)

  have inc_symm (p l : Fin 13) : inc p l ↔ inc l p := by
    simp only [inc, Nat.add_comm]

  have large_avoid (P : Finset (Fin 13)) (h : 4 ≤ P.card) : (avoid P).card ≤ 3 := by
    exact hgeom P h

  have no_edge_subsets (P L : Finset (Fin 13))
      (h : ¬ ∃ p ∈ P, ∃ l ∈ L, inc p l) : L ⊆ avoid P ∧ P ⊆ avoid L := by
    constructor
    · intro l hl
      simp only [avoid, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p hp hi
      exact h ⟨p, hp, l, hl, hi⟩
    · intro p hp
      simp only [avoid, Finset.mem_filter, Finset.mem_univ, true_and]
      intro l hl hi
      exact h ⟨p, hp, l, hl, (inc_symm l p).mp hi⟩

  have tests_force_function
      (B : Finset (Fin 13) → Finset (Fin 13) → Bool)
      (hmono : ∀ P P' L L', P ⊆ P' → L ⊆ L' → B P L = true → B P' L' = true)
      (hpositive : ∀ p l, inc p l → B {p} {l} = true)
      (hnegative : ∀ S, S.card ≤ 3 → B S (avoid S) = false ∧ B (avoid S) S = false)
      (P L : Finset (Fin 13)) : B P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l := by
    constructor
    · intro hB
      by_contra hn
      obtain ⟨hL, hP⟩ := no_edge_subsets P L hn
      by_cases hsmall : P.card ≤ 3
      · have hb := hmono P P L (avoid P) (Finset.Subset.refl _) hL hB
        rw [(hnegative P hsmall).1] at hb
        cases hb
      · have hlarge : 4 ≤ P.card := by omega
        have hsmallL : L.card ≤ 3 :=
          (Finset.card_le_card hL).trans (large_avoid P hlarge)
        have hb := hmono P (avoid L) L L hP (Finset.Subset.refl _) hB
        rw [(hnegative L hsmallL).2] at hb
        cases hb
    · rintro ⟨p, hp, l, hl, hi⟩
      exact hmono {p} P {l} L (Finset.singleton_subset_iff.mpr hp)
        (Finset.singleton_subset_iff.mpr hl) (hpositive p l hi)


  let encode (P L : Finset (Fin 13)) (i : Fin 26) : Bool :=
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P)
    else decide (Fin.ofNat 13 i.val ∈ L)

  let out (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : List ℕ) (P L : Finset (Fin 13)) : Bool :=
    PEqualNP.CircuitLowerBounds.GateOp.and.eval (outs.map fun k => (C.wires (List.ofFn (encode P L))).getD k false)

  have encode_mono {P Q L M : Finset (Fin 13)} (hp : P ⊆ Q) (hl : L ⊆ M) :
      ∀ i, encode P L i = true → encode Q M i = true := by
    intro i hi
    unfold encode at hi ⊢
    split_ifs at hi ⊢ with h
    · exact decide_eq_true (hp (of_decide_eq_true hi))
    · exact decide_eq_true (hl (of_decide_eq_true hi))

  have getD_snoc (xs : List Bool) (a : Bool) (k : ℕ) :
      (xs ++ [a]).getD k false =
        if k < xs.length then xs.getD k false else if k = xs.length then a else false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left h1]
    · subst h2; simp
    · rw [List.getElem?_append_right (by omega)]
      rw [List.getElem?_eq_none (by simp; omega)]
      simp

  have wires_mono (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (xs ys : List Bool)
      (hlen : xs.length = ys.length)
      (hxy : ∀ k, xs.getD k false = true → ys.getD k false = true) :
      ∀ k, (C.wires xs).getD k false = true → (C.wires ys).getD k false = true := by
    obtain ⟨gs, o⟩ := C
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    induction gs generalizing xs ys with
    | nil => simpa using hxy
    | cons g gs ih =>
      simp only [List.foldl_cons]
      apply ih
      · simpa only [List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hlen
      · intro k hk
        simp only [getD_snoc, hlen] at hk ⊢
        split_ifs at hk ⊢ with h1 h2
        · exact hxy k hk
        · have hop := (hC g List.mem_cons_self).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with hop | hop
          · simp only [hop, eval_and, List.all_map, Function.comp_apply, id,
              List.all_eq_true] at hk ⊢
            exact fun j hj => hxy j (hk j hj)
          · simp only [hop, eval_or, List.any_map, Function.comp_apply, id,
              List.any_eq_true] at hk ⊢
            obtain ⟨j, hj, hjv⟩ := hk
            exact ⟨j, hj, hxy j hjv⟩
      · intro g' hg'
        exact hC g' (List.mem_cons_of_mem _ hg')

  have out_mono (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : List ℕ) (hC : PEqualNP.MetaComplexity.Monotone2 C)
      {P Q L M : Finset (Fin 13)} (hp : P ⊆ Q) (hl : L ⊆ M) :
      out C outs P L = true → out C outs Q M = true := by
    intro h
    have hm := wires_mono C hC (List.ofFn (encode P L)) (List.ofFn (encode Q M))
      (by simp) (by
        intro k hk
        by_cases hkn : k < 26
        · rw [List.getD_eq_getElem _ _ (by simpa using hkn)] at hk ⊢
          simp only [List.getElem_ofFn] at hk ⊢
          exact encode_mono hp hl ⟨k, hkn⟩ hk
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hkn)] at hk
          cases hk)
    simp only [out, eval_and, List.all_map, Function.comp_apply, id, List.all_eq_true] at h ⊢
    exact fun k hk => hm k (h k hk)

  have circuit_tests_force_function (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : List ℕ) (hC : PEqualNP.MetaComplexity.Monotone2 C)
      (hpositive : ∀ p l, inc p l → out C outs {p} {l} = true)
      (hnegative : ∀ S, S.card ≤ 3 →
        out C outs S (avoid S) = false ∧ out C outs (avoid S) S = false) :
      ∀ P L, out C outs P L = true ↔ ∃ p ∈ P, ∃ l ∈ L, inc p l := by
    exact tests_force_function (out C outs)
      (fun _ _ _ _ hp hl => out_mono C outs hC hp hl) hpositive hnegative

  change (∀ p l, inc p l → out C outs {p} {l} = true) ∧
    (∀ S, S.card ≤ 3 → out C outs S (avoid S) = false ∧ out C outs (avoid S) S = false) at htests
  apply hcore C outs hC hlen
  exact circuit_tests_force_function C outs hC htests.1 htests.2
