import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_5200_791
  (coverage : let S := PEqualNP.HeptadCover.singerLines3
    let row (Q : Finset (Fin 13)) : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13)
      (fun p => decide (p ∈ Q)) (fun l => decide (l ∈ PEqualNP.HeptadCover.missLines S Q))
    ∀ a b : Fin 26, (¬ (∃ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
       ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
        (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)))) →
      ∃ Q, PEqualNP.HeptadCover.IsQuadrangle S Q ∧ row Q a = true ∧ row Q b = true)
  (lower : let occ (a b : Fin 26) : Prop := ∃ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
       ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
        (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))
    let row (a b : Fin 26) := List.ofFn (fun i => decide (i = a ∨ i = b))
    let v (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) (r : List Bool) :=
      (C.wires r).getD w false
    let g := PEqualNP.MetaComplexity.NestedCover.gateAt
    let nest (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) : Prop :=
      let d := PEqualNP.CircuitLowerBounds.GateOp.and
      (g C j).op = d ∧ ∃ i ∈ (g C j).inputs, 26 ≤ i ∧ (g C (i - 26)).op = d
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u w : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
      u < 26 + C.size → w < 26 + C.size →
      (∀ a b : Fin 26, (v C u (row a b) || v C w (row a b)) = decide (occ a b)) →
      (∃ a b : Fin 26, v C u (row a b) = true ∧ v C w (row a b) = false) →
      (∃ a b : Fin 26, v C w (row a b) = true ∧ v C u (row a b) = false) →
      (∃ i ∈ Finset.range C.size, ∃ j ∈ Finset.range C.size,
        i ≠ j ∧ nest C i ∧ nest C j ∧ ∀ k ∈ Finset.range C.size, nest C k → k = i ∨ k = j) →
      63 ≤ C.size) :
  have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∃ x18 ∈ Finset.range x7.size, ∃ x19 ∈ Finset.range x7.size, x18 ≠ x19 ∧ x6 x7 x18 ∧ x6 x7 x19 ∧ ∀ x20 ∈ Finset.range x7.size, x6 x7 x20 → x20 = x18 ∨ x20 = x19) → (63 : ℕ) ≤ x7.size := by
  classical
  intro _S _row _wire _gate _op _nested C u w mono back hu hw onEdges offQuadrangles onlyU onlyW two
  let S := PEqualNP.HeptadCover.singerLines3
  let bits (a b : Fin 26) : Fin 26 → Bool := fun i => decide (i = a ∨ i = b)
  let row (Q : Finset (Fin 13)) : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13)
    (fun p => decide (p ∈ Q)) (fun l => decide (l ∈ PEqualNP.HeptadCover.missLines S Q))
  let wire (w : ℕ) (r : List Bool) := (C.wires r).getD w false
  let pair := fun (p l : Fin 13) =>
    List.ofFn (fun i : Fin 13 => decide (i ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun i : Fin 13 => decide (i ∈ ({l} : Finset (Fin 13))))
  have pairRow (p l : Fin 13) : List.ofFn (bits (Fin.castAdd 13 p) (Fin.natAdd 13 l)) =
      pair p l := by
    rw [List.ofFn_add (n := 13) (m := 13)]
    congr 1 <;> apply congrArg List.ofFn <;> funext i
    · simp [bits, Fin.ext_iff]
      omega
    · simp [bits, Fin.ext_iff]
      omega
  have quadRow (Q : Finset (Fin 13)) : List.ofFn (row Q) =
      List.ofFn (fun i : Fin 13 => decide (i ∈ Q)) ++
      List.ofFn (fun i : Fin 13 => decide (i ∈ PEqualNP.HeptadCover.missLines S Q)) := by
    rw [List.ofFn_add (n := 13) (m := 13)]
    congr 1
  have orderBool {a b : Bool} (h : a = true → b = true) : a ≤ b := by
    cases a <;> cases b <;> simp at h ⊢

  have gateOrder (g : PEqualNP.CircuitLowerBounds.Gate) (ha : g.op = .and ∨ g.op = .or)
      {x y : List Bool} (hxy : ∀ i, x.getD i false ≤ y.getD i false) :
      g.op.eval (g.inputs.map fun i => x.getD i false) ≤
        g.op.eval (g.inputs.map fun i => y.getD i false) := by
    apply orderBool
    rcases ha with h | h
    · rw [h]
      change (g.inputs.map fun i => x.getD i false).all id = true →
        (g.inputs.map fun i => y.getD i false).all id = true
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro hx i hi
      exact Bool.eq_true_of_true_le (hx i hi ▸ hxy i)
    · rw [h]
      change (g.inputs.map fun i => x.getD i false).any id = true →
        (g.inputs.map fun i => y.getD i false).any id = true
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, hx⟩
      exact ⟨i, hi, Bool.eq_true_of_true_le (hx ▸ hxy i)⟩

  have appendOrder (X Y : List Bool) (a b : Bool)
      (len : X.length = Y.length) (h : ∀ i, X.getD i false ≤ Y.getD i false) (ab : a ≤ b) :
      ∀ i, (X ++ [a]).getD i false ≤ (Y ++ [b]).getD i false := by
    intro i
    by_cases q : i < X.length
    · rw [List.getD_append _ _ _ _ q, List.getD_append _ _ _ _ (len ▸ q)]
      exact h i
    · by_cases e : i = X.length
      · subst i
        simp [List.getD_eq_getElem?_getD, len, ab]
      · have gt : X.length < i := by omega
        rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

  have foldOrder (gs : List PEqualNP.CircuitLowerBounds.Gate) (X Y : List Bool)
      (len : X.length = Y.length) (h : ∀ i, X.getD i false ≤ Y.getD i false)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ i,
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) X).getD i false ≤
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) Y).getD i false := by
    induction gs generalizing X Y with
    | nil => exact h
    | cons g gs ih =>
      simp only [List.foldl_cons]
      exact ih _ _ (by simp [len]) (appendOrder X Y _ _ len h (gateOrder g (ops _ (by simp)) h))
        (fun q hq => ops q (by simp [hq]))
  have wireMono (x y : Fin 26 → Bool) (xy : x ≤ y) (j : ℕ) :
      wire j (List.ofFn x) ≤ wire j (List.ofFn y) := by
    apply foldOrder C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ ?_ j
    · intro i
      by_cases hi : i < 26
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
        exact xy ⟨i, hi⟩
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hi]
        exact le_rfl
    · intro g hg
      exact (mono g hg).1
  have pairComm (a b : Fin 26) : bits a b = bits b a := by
    funext i
    simp [bits, Bool.or_comm]
  have falsePair (a b : Fin 26)
      (h : ¬ (∃ p l : Fin 13, p ∈ S l ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)))) :
      wire u (List.ofFn (bits a b)) = false ∧ wire w (List.ofFn (bits a b)) = false := by
    obtain ⟨Q, hQ, onA, onB⟩ := coverage a b h
    change row Q a = true at onA
    change row Q b = true at onB
    have below : bits a b ≤ row Q := by
      intro i
      by_cases ha : i = a
      · subst i
        simp [bits, onA]
      · by_cases hb : i = b
        · subst i
          simp [bits, onB]
        · simp [bits, ha, hb]
    have hu' := wireMono _ _ below u
    have hw' := wireMono _ _ below w
    rw [quadRow] at hu' hw'
    have offU := (offQuadrangles Q hQ).1
    have offW := (offQuadrangles Q hQ).2
    change wire u _ = false at offU
    change wire w _ = false at offW
    rw [offU] at hu'
    rw [offW] at hw'
    exact ⟨Bool.eq_false_of_le_false hu', Bool.eq_false_of_le_false hw'⟩
  apply lower C u w mono back hu hw
  · intro a b
    by_cases hi : ∃ p l : Fin 13, p ∈ S l ∧
        ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
         (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))
    · rw [decide_eq_true hi]
      obtain ⟨p, l, he, hab | hba⟩ := hi
      · obtain ⟨rfl, rfl⟩ := hab
        change (wire u (List.ofFn (bits _ _)) || wire w (List.ofFn (bits _ _))) = true
        rw [pairRow]
        exact Bool.or_eq_true_iff.mpr (onEdges p l he)
      · obtain ⟨rfl, rfl⟩ := hba
        change (wire u (List.ofFn (bits _ _)) || wire w (List.ofFn (bits _ _))) = true
        rw [pairComm, pairRow]
        exact Bool.or_eq_true_iff.mpr (onEdges p l he)
    · rw [decide_eq_false hi]
      have off := falsePair a b hi
      change (wire u (List.ofFn (bits _ _)) || wire w (List.ofFn (bits _ _))) = false
      rw [off.1, off.2]
      rfl
  · obtain ⟨p, l, _, a, b⟩ := onlyU
    refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, ?_⟩
    change wire u (List.ofFn (bits _ _)) = true ∧ wire w (List.ofFn (bits _ _)) = false
    rw [pairRow]
    exact ⟨a, b⟩
  · obtain ⟨p, l, _, a, b⟩ := onlyW
    refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, ?_⟩
    change wire w (List.ofFn (bits _ _)) = true ∧ wire u (List.ofFn (bits _ _)) = false
    rw [pairRow]
    exact ⟨a, b⟩
  · exact two
