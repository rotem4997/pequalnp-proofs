import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

-- Close the frontier with an OR tree, then count the pairs with a single
-- occurrence on either side separately from the pairs requiring both re-reads.
-- The one-occurrence bounds are L-meta-2970 and L-meta-2972.
theorem PEqualNP.Outside.R_meta_5030_1
    (lineOnce : ∀ (n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      (∀ p r l u, p ≠ r → l ≠ u → ¬ (I p l ∧ I r l ∧ I p u ∧ I r u)) →
      IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ 1 →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧
        lineSingle C (n+n) (fun k => decide (n ≤ k)) e.1.val (n+e.2.val) = true} ≤ 10 * C.size)
    (pointOnce : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧
        lineSingle C (n+n) (fun k => decide (k < n)) e.1.val (n+e.2.val) = true} ≤ 10 * C.size)
    (bothRepeated : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      300 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      (∀ p l, I p l → circuitFun (n+n) C
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true) →
      Fintype.card {e : Fin n × Fin n // I e.1 e.2 ∧
        lineSingle C (n+n) (fun k => decide (n ≤ k)) e.1.val (n+e.2.val) = false ∧
        lineSingle C (n+n) (fun k => decide (k < n)) e.1.val (n+e.2.val) = false} ≤ 30 * C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset ℕ),   have x7 : (Fin (x2 + x2) → Bool) → ℕ → Bool := fun (x7 : Fin (x2 + x2) → Bool) (x8 : ℕ) => PEqualNP.CircuitLowerBounds.wireValue x5 (List.ofFn x7) x8;   have x8 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x8 x9 : Fin x2) (x10 : Fin (x2 + x2)) => Decidable.decide (x10 = Fin.castAdd x2 x8 ∨ x10 = Fin.natAdd x2 x9);   have x9 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x9 : Finset (Fin x2)) (x10 : Fin (x2 + x2)) => Fin.addCases (fun (x11 : Fin x2) => Decidable.decide (∀ x12 ∈ x9, ¬x3 x11 x12)) (fun (x11 : Fin x2) => Decidable.decide (x11 ∈ x9)) x10;   (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x12 : Fin x2), Fintype.card { x13 : Fin x2 // x3 x13 x12 } = x1 + (1 : ℕ)) → (∀ (x13 x14 : Fin x2), x13 ≠ x14 → ∃! x16 : Fin x2, x3 x13 x16 ∧ x3 x14 x16) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ x16 ∈ x6, x2 + x2 ≤ x16 ∧ x16 < x2 + x2 + x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x16 - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x7 (x8 x18 x19) x16 = Bool.true) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → ∃ x20 ∈ x6, x7 (x8 x17 x18) x20 = Bool.true) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∀ x20 ∈ x6, x7 (x9 x18) x20 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * (x5.size + (1 : ℕ)) := by
  classical
  intro q n I inst C F val pair neg hq hn degree unique basis shape front accepts rejects
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have joinFrontier (n : ℕ) (C : Circuit) (F : Finset ℕ) (hC : IsAO2 n C)
      (nonempty : F.Nonempty) (bound : ∀ w ∈ F, w < n + C.size) :
      ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 ≤ C.size + F.card ∧
        ∀ x : Fin n → Bool, circuitFun n D x = true ↔
          ∃ w ∈ F, wireValue C (List.ofFn x) w = true := by
    have length (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [step]
        omega
    have wiresLength (D : Circuit) (x : Fin n → Bool) :
        (D.wires (List.ofFn x)).length = n+D.size := by
      change (D.gates.foldl step (List.ofFn x)).length = n+D.gates.length
      rw [length, List.length_ofFn]
    have atGate (D : Circuit) (j : ℕ) (hj : j < D.gates.length) :
        gateAt D j = D.gates[j] := List.getD_eq_getElem _ _ hj
    have build : ∀ S : Finset ℕ, S.Nonempty → (∀ w ∈ S, w < n+C.size) →
        ∃ D : Circuit, IsAO2 n D ∧ C.size ≤ D.size ∧ D.output < n+D.size ∧
          D.size+1 ≤ C.size+S.card ∧
          (∀ (x : Fin n → Bool) w, w < n+C.size →
            wireValue D (List.ofFn x) w = wireValue C (List.ofFn x) w) ∧
          ∀ x : Fin n → Bool, circuitFun n D x = true ↔
            ∃ w ∈ S, wireValue C (List.ofFn x) w = true := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro hs _
        obtain ⟨w, hw⟩ := hs
        simp at hw
      | @insert w S notIn ih =>
        intro _ hs
        have wlt := hs w (Finset.mem_insert_self w S)
        by_cases se : S.Nonempty
        · obtain ⟨D, hD, dGe, out, dLe, old, eval⟩ :=
            ih se (fun v hv => hs v (Finset.mem_insert_of_mem hv))
          let g : Gate := ⟨.or, [D.output,w]⟩
          let D' : Circuit := ⟨D.gates ++ [g], n+D.size⟩
          have size : D'.size = D.size + 1 := by
            change (D.gates ++ [g]).length = D.gates.length + 1
            simp
          have original (j : ℕ) (hj : j < D.gates.length) :
              gateAt D' j = gateAt D j := by
            rw [atGate D j hj, atGate D' j (by simpa [D'] using Nat.lt_succ_of_lt hj)]
            exact List.getElem_append_left hj
          have model : IsAO2 n D' := by
            refine ⟨?_, ?_, ?_⟩
            · intro a ha
              change a ∈ D.gates ++ [g] at ha
              rcases List.mem_append.mp ha with ha | ha
              · exact hD.1 a ha
              · have eq : a = g := List.mem_singleton.mp ha
                exact Or.inr (eq.symm ▸ rfl)
            · intro j hj i hi
              by_cases prev : j < D.gates.length
              · rw [original j prev] at hi
                exact hD.2.1 j prev i hi
              · have eq : j = D.gates.length := by
                  change j < (D.gates ++ [g]).length at hj
                  simp only [List.length_append, List.length_singleton] at hj
                  omega
                subst j
                have endGate : gateAt D' D.gates.length = g := by
                  rw [atGate _ _ (by simp [D'])]
                  simp [D']
                rw [endGate] at hi
                change i ∈ [D.output,w] at hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                change D.output < n+D.gates.length at out
                change C.size ≤ D.gates.length at dGe
                rcases hi with rfl | rfl <;> omega
            · intro a ha
              change a ∈ D.gates ++ [g] at ha
              rcases List.mem_append.mp ha with ha | ha
              · exact hD.2.2 a ha
              · rw [List.mem_singleton.mp ha]
                rfl
          have newWires (x : Fin n → Bool) :
              D'.wires (List.ofFn x) = D.wires (List.ofFn x) ++
                [wireValue D (List.ofFn x) D.output || wireValue D (List.ofFn x) w] := by
            change (D.gates ++ [g]).foldl step (List.ofFn x) = _
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            have orEval (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
              cases a <;> cases b <;> rfl
            change D.wires (List.ofFn x) ++ [GateOp.or.eval
              [wireValue D (List.ofFn x) D.output, wireValue D (List.ofFn x) w]] = _
            rw [orEval]
          refine ⟨D', model, by omega, by change n+D.size < n+D'.size; omega,
            ?_, ?_, ?_⟩
          · rw [Finset.card_insert_of_notMem notIn, size]
            omega
          · intro x i hi
            change (D'.wires (List.ofFn x)).getD i false = _
            rw [newWires, List.getD_append _ _ _ _ (by rw [wiresLength]; omega)]
            exact old x i hi
          · intro x
            change (D'.wires (List.ofFn x)).getD (n+D.size) false = true ↔ _
            rw [newWires, ← wiresLength D x]
            simp only [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self,
              List.getD_cons_zero, Bool.or_eq_true]
            rw [old x w wlt]
            change circuitFun n D x = true ∨ _ ↔ _
            rw [eval]
            constructor
            · rintro (⟨v, hv, val⟩ | val)
              · exact ⟨v, Finset.mem_insert_of_mem hv, val⟩
              · exact ⟨w, Finset.mem_insert_self w S, val⟩
            · rintro ⟨v, hv, val⟩
              rcases Finset.mem_insert.mp hv with rfl | hv
              · exact Or.inr val
              · exact Or.inl ⟨v, hv, val⟩
        · have eq := Finset.not_nonempty_iff_eq_empty.mp se
          subst S
          let D : Circuit := ⟨C.gates,w⟩
          refine ⟨D, hC, le_rfl, wlt, ?_, fun _ _ _ => rfl, ?_⟩
          · change C.size+1 ≤ C.size+(insert w (∅ : Finset ℕ)).card
            simp
          · intro x
            change wireValue C (List.ofFn x) w = true ↔ _
            simp
    obtain ⟨D, good, _, _, ds, _, ev⟩ := build F nonempty bound
    exact ⟨D, good, ds, ev⟩
  have getDGate (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] :=
    List.getD_eq_getElem _ _ hj
  have hao : IsAO2 (n+n) C := by
    refine ⟨fun g hg => (basis g hg).1, ?_, ?_⟩
    · intro j hj w hw
      rw [getDGate j hj] at hw
      obtain ⟨a, b, inputs, hab, hb⟩ := shape j C.gates[j] (List.getElem?_eq_getElem hj)
      rw [inputs] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hab.trans hb
      · exact hb
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨a, b, inputs, _, _⟩ := shape j g hj
      rw [inputs]
      rfl
  have npos : 0 < n := by omega
  let l₀ : Fin n := ⟨0, npos⟩
  have ppos : 0 < Fintype.card {p : Fin n // I p l₀} := by rw [degree]; omega
  obtain ⟨p₀⟩ := Fintype.card_pos_iff.mp ppos
  obtain ⟨w₀, hw₀, _⟩ := accepts p₀.val l₀ p₀.property
  have fpos : F.Nonempty := ⟨w₀, hw₀⟩
  obtain ⟨D, hD, dsize, dval⟩ := joinFrontier (n+n) C F hao fpos (fun w hw => (front w hw).2.1)
  have fcard : F.card ≤ C.size := by
    let G := (Finset.range C.size).image (fun j => n+n+j)
    have sub : F ⊆ G := by
      intro w hw
      obtain ⟨hlo, hhi, _, _⟩ := front w hw
      exact Finset.mem_image.mpr ⟨w-(n+n), Finset.mem_range.mpr (by omega), by omega⟩
    exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans_eq (Finset.card_range C.size))
  have acceptD (p l : Fin n) (h : I p l) : circuitFun (n+n) D
      (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = true :=
    (dval (pair p l)).mpr (accepts p l h)
  let leBits (a b : List Bool) := ∀ i, a.getD i false = true → b.getD i false = true
  have evalMono (op : GateOp) (hop : op = .and ∨ op = .or) (s : List ℕ)
      (a b : List Bool) (h : leBits a b) :
      op.eval (s.map (fun i => a.getD i false)) = true →
      op.eval (s.map (fun i => b.getD i false)) = true := by
    rcases hop with rfl | rfl
    · change (s.map _).all id = true → (s.map _).all id = true
      simp only [List.all_eq_true, List.mem_map, id_eq]
      intro H v hv
      obtain ⟨i, hi, rfl⟩ := hv
      exact h i (H _ ⟨i,hi,rfl⟩)
    · change (s.map _).any id = true → (s.map _).any id = true
      simp only [List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
      exact ⟨_, ⟨i,hi,rfl⟩, h i hv⟩
  have foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ a b : List Bool, a.length = b.length → leBits a b →
        leBits (gs.foldl step a) (gs.foldl step b) := by
    induction gs with
    | nil => intro a b _ h; exact h
    | cons g gs ih =>
      intro a b len h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))
      · simp [step, len]
      · intro i hi
        change (a ++ [_]).getD i false = true at hi
        change (b ++ [_]).getD i false = true
        by_cases earlier : i < a.length
        · rw [List.getD_append _ _ _ _ earlier] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega), ← len]
          by_cases next : i - a.length = 0
          · rw [next] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact evalMono g.op (ops g List.mem_cons_self) _ a b h hi
          · obtain ⟨k, eq⟩ : ∃ k, i - a.length = k+1 :=
              ⟨i-a.length-1, by omega⟩
            rw [eq] at hi
            simp at hi
  have cardSubtype {α : Type} [Fintype α] (S : Finset α) (P : α → Prop)
      [DecidablePred P] (mem : ∀ a, a ∈ S ↔ P a) :
      S.card = Fintype.card (Subtype P) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight mem)
  have rejectD (x : Fin (n+n) → Bool)
      (small : Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q)
      (miss : ¬ ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) :
      circuitFun (n+n) D x = false := by
    let Y := Finset.univ.filter (fun l : Fin n => x (Fin.natAdd n l) = true)
    have yCard : Y.card ≤ q := by
      rw [cardSubtype Y (fun l => x (Fin.natAdd n l) = true) (by simp [Y])]
      exact small
    have dominated (i : Fin (n+n)) (hx : x i = true) : neg Y i = true := by
      revert hx
      refine Fin.addCases ?_ ?_ i
      · intro p hp
        have none : ∀ l ∈ Y, ¬ I p l := by
          intro l hl h
          exact miss ⟨p, l, h, hp, (Finset.mem_filter.mp hl).2⟩
        change Fin.addCases _ _ (Fin.castAdd n p) = true
        rw [Fin.addCases_left]
        exact decide_eq_true none
      · intro l hl
        change Fin.addCases _ _ (Fin.natAdd n l) = true
        rw [Fin.addCases_right, decide_eq_true_eq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
    have lists : leBits (List.ofFn x) (List.ofFn (neg Y)) := by
      intro i hi
      by_cases inside : i < n+n
      · rw [List.getD_eq_getElem _ _ (by simp [inside]), List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ (by simp [inside]), List.getElem_ofFn]
        exact dominated ⟨i, inside⟩ hi
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt inside)] at hi
        contradiction
    cases h : circuitFun (n+n) D x with
    | false => rfl
    | true =>
      obtain ⟨w, hw, hit⟩ := (dval x).mp h
      have reaches : val (neg Y) w = true :=
        foldMono C.gates hao.1 _ _ (by simp) lists w hit
      rw [rejects Y yCard w hw] at reaches
      contradiction
  have fourFree (p r l u : Fin n) (neP : p ≠ r) (neL : l ≠ u) :
      ¬ (I p l ∧ I r l ∧ I p u ∧ I r u) := by
    rintro ⟨a,b,c,d⟩
    obtain ⟨v, _, only⟩ := unique p r neP
    exact neL ((only l ⟨a,b⟩).trans (only u ⟨c,d⟩).symm)
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun e => I e.1 e.2)
  let lx (e : Fin n × Fin n) := lineSingle D (n+n) (fun k => decide (n ≤ k)) e.1.val (n+e.2.val)
  let px (e : Fin n × Fin n) := lineSingle D (n+n) (fun k => decide (k < n)) e.1.val (n+e.2.val)
  let A := E.filter (fun e => lx e = true)
  let B := E.filter (fun e => px e = true)
  let T := E.filter (fun e => lx e = false ∧ px e = false)
  have Acount : A.card ≤ 10 * D.size := by
    rw [cardSubtype A (fun e => I e.1 e.2 ∧ lx e = true) (by simp [A,E])]
    exact lineOnce n I D fourFree hD (fun x small miss => rejectD x (by omega) miss)
  have Bcount : B.card ≤ 10 * D.size := by
    rw [cardSubtype B (fun e => I e.1 e.2 ∧ px e = true) (by simp [B,E])]
    exact pointOnce q n I D (by omega) hn degree unique hD rejectD
  have Tcount : T.card ≤ 30 * D.size := by
    rw [cardSubtype T (fun e => I e.1 e.2 ∧ lx e = false ∧ px e = false)
      (by simp [T,E, and_assoc])]
    exact bothRepeated q n I D hq hn degree unique hD rejectD acceptD
  have covers : E ⊆ A ∪ (B ∪ T) := by
    intro e he
    cases hl : lx e
    · cases hp : px e
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨he,hl,hp⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨he,hp⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,hl⟩)
  let fibers : ∀ l : Fin n, Type := fun l => {p : Fin n // I p l}
  have incCount : E.card = n * (q+1) := by
    rw [← Fintype.card_coe]
    let e : ↥E ≃ (Σ l : Fin n, fibers l) :=
      { toFun := fun z => ⟨z.val.2, ⟨z.val.1, (Finset.mem_filter.mp z.property).2⟩⟩
        invFun := fun z => ⟨(z.2.val,z.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.2.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp [fibers, degree]
  have lb := ((Finset.card_le_card covers).trans (Finset.card_union_le A (B ∪ T)))
  rw [incCount] at lb
  have bc := Finset.card_union_le B T
  have incidence : n*q ≤ n*(q+1) := Nat.mul_le_mul_left n (Nat.le_succ q)
  omega
