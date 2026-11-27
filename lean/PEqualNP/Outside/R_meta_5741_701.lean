import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5741_701
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → Monotone2 C →
      circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size)
    (toTopForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D)
    (pg23LowJunk :
      let G : SimpleGraph (Fin 26) := SimpleGraph.fromRel fun a b : Fin 26 =>
        a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ [DecidableRel G.Adj] (C : Circuit),
        IsLeastAO G C → TopForm G C → (junk G C).card ≤ 1 → 64 ≤ C.size)
    (pg23MultiJunk :
      let G : SimpleGraph (Fin 26) := SimpleGraph.fromRel fun a b : Fin 26 =>
        a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ [DecidableRel G.Adj] (C : Circuit),
        IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), x3 x4 x7 ∧ x2 x5 x7; have x5 : Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ x3 x5 x7); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → (∀ (x9 x10 : Fin (13 : ℕ)), x2 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) → (∀ (x10 : Finset (Fin (13 : ℕ))), x4 x10 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 (x5 x10) = Bool.false) → False := by
  dsimp only at pg23LowJunk pg23MultiJunk ⊢
  classical
  intro C hMono hSize hInc hMax
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let inc : Fin 13 → Fin 13 → Prop := fun p l => ∃ d ∈ D, p = l + d
  let avoid : Finset (Fin 13) → Fin 13 → Prop := fun X l => ∀ p ∈ X, ¬ inc p l
  let isClosed : Finset (Fin 13) → Prop := fun X => ∀ p ∉ X, ∃ l, avoid X l ∧ inc p l
  let maxIn : Finset (Fin 13) → Fin 26 → Bool := fun X k =>
    decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ ∃ l, k = Fin.natAdd 13 l ∧ avoid X l)
  let G : SimpleGraph (Fin 26) := SimpleGraph.fromRel fun a b : Fin 26 =>
    a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  -- Monotonicity of Monotone2 circuits
  have hMonoEval : ∀ (x y : Fin 26 → Bool), (∀ i, x i = true → y i = true) →
      circuitFun 26 C x = true → circuitFun 26 C y = true := by
    intro x y hle hx
    have hfold : ∀ (gs : List Gate) (w1 w2 : List Bool),
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        w1.length = w2.length →
        (∀ k, w1.getD k false = true → w2.getD k false = true) →
        ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD k false = true →
             (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD k false = true := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ hw k hk; exact hw k hk
      | cons g rest ih =>
        intro w1 w2 hgs hlen hw
        rw [List.foldl_cons, List.foldl_cons]
        apply ih
        · intro g' hg'; exact hgs g' (List.mem_cons_of_mem g hg')
        · simp [hlen]
        · intro k hk
          have hg := (hgs g List.mem_cons_self).1
          by_cases hlt : k < w1.length
          · have hlt2 : k < w2.length := hlen ▸ hlt
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt, ← List.getD_eq_getElem _ _ hlt] at hk
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt2, ← List.getD_eq_getElem _ _ hlt2]
            exact hw k hk
          · by_cases heq : k = w1.length
            · subst heq
              rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)] at hk
              simp only [Nat.sub_self, List.getElem_cons_zero] at hk
              rw [hlen, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              rcases hg with hand | hor
              · rw [hand] at hk ⊢
                change (g.inputs.map fun i => w1.getD i false).all id = true at hk
                change (g.inputs.map fun i => w2.getD i false).all id = true
                simp only [List.all_eq_true, List.mem_map, id_eq] at hk ⊢
                rintro _ ⟨i, hi, rfl⟩
                exact hw i (hk _ ⟨i, hi, rfl⟩)
              · rw [hor] at hk ⊢
                change (g.inputs.map fun i => w1.getD i false).any id = true at hk
                change (g.inputs.map fun i => w2.getD i false).any id = true
                simp only [List.any_eq_true, List.mem_map, id_eq] at hk ⊢
                obtain ⟨_, ⟨i, hi, rfl⟩, h1⟩ := hk
                exact ⟨_, ⟨i, hi, rfl⟩, hw i h1⟩
            · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
              cases hk
    have hinit : ∀ k, (List.ofFn x).getD k false = true → (List.ofFn y).getD k false = true := by
      intro k hk
      by_cases hlt : k < 26
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn] at hk
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        exact hle ⟨k, hlt⟩ hk
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        cases hk
    exact hfold C.gates (List.ofFn x) (List.ofFn y) hMono (by simp) hinit C.output hx
  -- Equivalence of G.Adj with inc
  have hIncRel : ∀ p l : Fin 13, inc p l ↔ (p.val + 13 - l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
    decide
  have hAdjIff : ∀ u v : Fin 26, G.Adj u v ↔
      (∃ p l : Fin 13, inc p l ∧
        ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p))) := by
    intro u v
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, ⟨hu, hv, hrel⟩ | ⟨hv, hu, hrel⟩⟩
      · let p : Fin 13 := ⟨u.val, hu⟩
        let l : Fin 13 := ⟨v.val - 13, by omega⟩
        refine ⟨p, l, (hIncRel p l).mpr hrel, Or.inl ⟨by ext; simp [p], by ext; simp [l]; omega⟩⟩
      · let p : Fin 13 := ⟨v.val, hv⟩
        let l : Fin 13 := ⟨u.val - 13, by omega⟩
        refine ⟨p, l, (hIncRel p l).mpr hrel, Or.inr ⟨by ext; simp [l]; omega, by ext; simp [p]⟩⟩
    · rintro ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · refine ⟨by intro h; have := congrArg Fin.val h; simp at this; omega, Or.inl ⟨p.isLt, by simp, ?_⟩⟩
        have hrel := (hIncRel p l).mp hpl
        simpa using hrel
      · refine ⟨by intro h; have := congrArg Fin.val h; simp at this; omega, Or.inr ⟨p.isLt, by simp, ?_⟩⟩
        have hrel := (hIncRel p l).mp hpl
        simpa using hrel
  -- Galois closure: C computes graphFun G ∅ exactly
  have hExact : circuitFun 26 C = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change circuitFun 26 C x = true ↔
      (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
    constructor
    · intro hCx
      by_contra hNoEdge
      let A : Finset (Fin 13) := Finset.univ.filter (fun p => x (Fin.castAdd 13 p) = true)
      let X : Finset (Fin 13) := Finset.univ.filter (fun p => ∀ l : Fin 13, avoid A l → ¬ inc p l)
      have hAX : A ⊆ X := by
        intro p hp
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
        intro l hl
        exact hl p hp
      have hAvoidIff : ∀ l : Fin 13, avoid X l ↔ avoid A l := by
        intro l
        constructor
        · intro hl p hp; exact hl p (hAX hp)
        · intro hl p hp
          have hpX := (Finset.mem_filter.mp hp).2
          exact hpX l hl
      have hClosedX : isClosed X := by
        intro p hp
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, Classical.not_not] at hp
        obtain ⟨l, hlA, hpl⟩ := hp
        exact ⟨l, (hAvoidIff l).mpr hlA, hpl⟩
      have hle : ∀ k : Fin 26, x k = true → maxIn X k = true := by
        intro k hk
        simp only [maxIn, decide_eq_true_eq]
        by_cases hlt : k.val < 13
        · let p : Fin 13 := ⟨k.val, hlt⟩
          have hk_eq : k = Fin.castAdd 13 p := by ext; simp [p]
          left
          refine ⟨p, hAX ?_, hk_eq⟩
          simp [A, ← hk_eq, hk]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk_eq : k = Fin.natAdd 13 l := by ext; simp [l]; omega
          right
          refine ⟨l, hk_eq, (hAvoidIff l).mpr ?_⟩
          intro p hp hpl
          have hp_true : x (Fin.castAdd 13 p) = true := (Finset.mem_filter.mp hp).2
          exact hNoEdge ⟨Fin.castAdd 13 p, Fin.natAdd 13 l,
            (hAdjIff _ _).mpr ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩, hp_true, hk_eq ▸ hk⟩
      have hTrueMax : circuitFun 26 C (maxIn X) = true := hMonoEval x (maxIn X) hle hCx
      have hFalseMax : circuitFun 26 C (maxIn X) = false := hMax X hClosedX
      rw [hTrueMax] at hFalseMax
      cases hFalseMax
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hAdjIff u v).mp huv
      · apply hMonoEval (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) x
        · intro k hk
          simp only [decide_eq_true_eq] at hk
          rcases hk with rfl | rfl <;> assumption
        · exact hInc p l hpl
      · apply hMonoEval (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)) x
        · intro k hk
          simp only [decide_eq_true_eq] at hk
          rcases hk with rfl | rfl <;> assumption
        · exact hInc p l hpl
  have hNonempty : G.edgeFinset.Nonempty := by
    refine ⟨s(Fin.castAdd 13 (0 : Fin 13), Fin.natAdd 13 (0 : Fin 13)), ?_⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact (hAdjIff _ _).mpr ⟨0, 0, ⟨0, by simp [D], by simp⟩, Or.inl ⟨rfl, rfl⟩⟩
  -- Normalize Monotone2 to IsAO2, then extract least size via Nat.find
  obtain ⟨D0, hD0_ao, hD0_fun, hD0_sz⟩ := normalize 26 G C hNonempty hMono hExact
  have hEx : ∃ m : ℕ, ∃ D : Circuit, IsAO2 26 D ∧ circuitFun 26 D = graphFun G ∅ ∧ D.size = m :=
    ⟨D0.size, D0, hD0_ao, hD0_fun, rfl⟩
  let m := Nat.find hEx
  obtain ⟨Dmin, hDmin_ao, hDmin_fun, hDmin_sz⟩ := Nat.find_spec hEx
  have hm_le : m ≤ D0.size := Nat.find_min' hEx ⟨D0, hD0_ao, hD0_fun, rfl⟩
  have hLeast : IsLeastAO G Dmin := by
    refine ⟨hDmin_ao, hDmin_fun, ?_⟩
    intro D' hD'_ao hD'_fun
    have := Nat.find_min' hEx ⟨D', hD'_ao, hD'_fun, rfl⟩
    omega
  obtain ⟨Dtop, hDtop_least, hDtop_tf⟩ := toTopForm 26 G Dmin hNonempty hLeast
  have hDtop_le : Dtop.size ≤ 63 := by
    have h1 := hDtop_least.2.2 Dmin hDmin_ao hDmin_fun
    omega
  by_cases hj : (junk G Dtop).card ≤ 1
  · have h64 := pg23LowJunk Dtop hDtop_least hDtop_tf hj
    omega
  · have hj2 : 2 ≤ (junk G Dtop).card := by omega
    have h64 := pg23MultiJunk Dtop hDtop_least hDtop_tf hj2
    omega
