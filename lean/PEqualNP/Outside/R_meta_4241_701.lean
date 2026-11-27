import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.HeptadCover

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4241_701
    (oneAndPair :
      let S := singerLines3
      let neg (X Y : Finset (Fin 13)) := IsFalseInput S X Y ∧
        ((∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l)
      let good (C : Circuit) := IsAO2 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ X Y, neg X Y → C.eval (incidenceInput X Y) = false
      ∀ C : Circuit, good C → (∀ D, good D → C.size ≤ D.size) →
        andPairs 26 C = 1 → 64 ≤ C.size)
    (manyAndPairs :
      let S := singerLines3
      let neg (X Y : Finset (Fin 13)) := IsFalseInput S X Y ∧
        ((∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l)
      let good (C : Circuit) := IsAO2 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ X Y, neg X Y → C.eval (incidenceInput X Y) = false
      ∀ C : Circuit, good C → (∀ D, good D → C.size ≤ D.size) →
        2 ≤ andPairs 26 C → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → ∀ (x9 x10 : Fin ((26 : ℕ) + x7.size)), x9 ≠ x10 → (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x4 x12 x13), x6 x7 (↑x10) (x4 x12 x13)] = Bool.true) → (∀ (x13 : Finset (Fin (13 : ℕ))), (∀ x14 ∉ x13, ∃ (x16 : Fin (13 : ℕ)), x3 x13 x16 ∧ x2 x14 x16) → (x13.card ≤ (2 : ℕ) ∨ Nat.card { x15 : Fin (13 : ℕ) // x3 x13 x15 } ≤ (2 : ℕ) ∨ x13.card = (3 : ℕ) ∧ ∃ (x15 : Fin (13 : ℕ)), ∀ x16 ∈ x13, x2 x16 x15) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x5 x13), x6 x7 (↑x10) (x5 x13)] = Bool.false) → (63 : ℕ) ≤ x7.size := by
  dsimp only
  intro C hMono a b _ hPos hDegMax
  let S := singerLines3
  let Dset : Finset (Fin 13) := {0, 1, 3, 9}
  let Inc (p l : Fin 13) : Prop := ∃ d ∈ Dset, p = l + d
  have hIncIff : ∀ p l : Fin 13, p ∈ S l ↔ Inc p l := by decide +kernel
  have univMax : (∀ q ∉ (Finset.univ : Finset (Fin 13)), ∃ l ∈ missLines S Finset.univ, q ∈ S l) ∧
      (missLines S Finset.univ).card ≤ 2 := by decide +kernel
  have emptyMax : (∀ q ∉ (∅ : Finset (Fin 13)), ∃ l ∈ missLines S ∅, q ∈ S l) ∧
      (∅ : Finset (Fin 13)).card ≤ 2 := by decide +kernel
  have le2Max : ∀ p q : Fin 13,
      (∀ r ∉ ({p, q} : Finset (Fin 13)), ∃ l ∈ missLines S {p, q}, r ∈ S l) ∧
      ({p, q} : Finset (Fin 13)).card ≤ 2 := by decide +kernel
  have lineEraseMax : ∀ l p : Fin 13, p ∈ S l →
      (∀ q ∉ (S l).erase p, ∃ m ∈ missLines S ((S l).erase p), q ∈ S m) ∧
      ((S l).erase p).card = 3 ∧ (S l).erase p ⊆ S l := by decide +kernel
  have twoLinesMeet : ∀ l1 l2 : Fin 13, l1 ≠ l2 → ∃ p, p ∈ S l1 ∧ p ∈ S l2 := by decide +kernel
  have lineCard4 : ∀ l : Fin 13, (S l).card = 4 := by decide +kernel
  have pairLineMax : ∀ l1 l2 : Fin 13,
      let P := zeroSet S {l1, l2}
      (∀ q ∉ P, ∃ l ∈ missLines S P, q ∈ S l) ∧
      (missLines S P).card ≤ 2 ∧ ({l1, l2} : Finset (Fin 13)) ⊆ missLines S P := by decide +kernel
  have threePencilMax : ∀ p l0 : Fin 13, p ∈ S l0 →
      let P := (S l0).erase p
      let Y0 := (Finset.univ.filter fun l => p ∈ S l).erase l0
      (∀ q ∉ P, ∃ l ∈ missLines S P, q ∈ S l) ∧
      P.card = 3 ∧ P ⊆ S l0 ∧ Y0 ⊆ missLines S P ∧
      (∀ q, (∀ l ∈ Y0, q ∉ S l) → q ∈ P) := by decide +kernel
  have pencilCard4 : ∀ p : Fin 13, (Finset.univ.filter fun l => p ∈ S l).card = 4 := by decide +kernel
  have fourPencilCover : ∀ p q : Fin 13, ∃ l, p ∈ S l ∧ q ∈ S l := by decide +kernel
  have hOther : ∀ u : Fin 26, ∃ p l : Fin 13, p ∈ S l ∧ p.val ≠ u.val ∧ 13 + l.val ≠ u.val := by
    decide +kernel
  have hptSelf : ∀ p : Fin 13, p ∈ S p := by decide +kernel
  let adj26 (u v : Fin 26) : Prop :=
    ∃ p l : Fin 13, p ∈ S l ∧
      ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p))
  have hDiffUniq : ∀ x ∈ Dset, ∀ y ∈ Dset, ∀ z ∈ Dset, ∀ w ∈ Dset,
      x ≠ y → x - y = z - w → x = z ∧ y = w := by
    decide +kernel
  have hUniqueLine : ∀ p1 p2 l1 l2 : Fin 13, p1 ≠ p2 → l1 ≠ l2 →
      ¬ (p1 ∈ S l1 ∧ p2 ∈ S l1 ∧ p1 ∈ S l2 ∧ p2 ∈ S l2) := by
    intro p1 p2 l1 l2 hp hl hconj
    obtain ⟨h11, h21, h12, h22⟩ := hconj
    rw [hIncIff] at h11 h21 h12 h22
    obtain ⟨d1, hd1, hp11⟩ := h11
    obtain ⟨d2, hd2, hp21⟩ := h21
    obtain ⟨d3, hd3, hp12⟩ := h12
    obtain ⟨d4, hd4, hp22⟩ := h22
    have hne : d1 ≠ d2 := fun heq => hp (by rw [hp11, hp21, heq])
    have hsub : d1 - d2 = d3 - d4 := by
      have h1 : d1 - d2 = p1 - p2 := by rw [hp11, hp21, add_sub_add_left_eq_sub]
      have h2 : d3 - d4 = p1 - p2 := by rw [hp12, hp22, add_sub_add_left_eq_sub]
      exact h1.trans h2.symm
    obtain ⟨hd13, _⟩ := hDiffUniq d1 hd1 d2 hd2 d3 hd3 d4 hd4 hne hsub
    have hlEq : l1 = l2 := by
      have h := hp11.symm.trans hp12
      rw [hd13] at h
      exact add_right_cancel h
    exact hl hlEq
  have hNoC4 : ∀ c1 c2 i1 i2 : Fin 26, c1 ≠ c2 → i1 ≠ i2 →
      ¬ (adj26 c1 i1 ∧ adj26 c1 i2 ∧ adj26 c2 i1 ∧ adj26 c2 i2) := by
    intro c1 c2 i1 i2 hcc hii hconj
    obtain ⟨h11, h12, h21, h22⟩ := hconj
    by_cases hc1 : c1.val < 13
    · obtain ⟨p1, l1, hp1l1, ⟨hc1p, hi1l⟩ | ⟨hc1l, _⟩⟩ := h11
      · obtain ⟨p1', l2, hp1'l2, ⟨hc1p', hi2l⟩ | ⟨hc1l, _⟩⟩ := h12
        · have hp1eq : p1 = p1' := Fin.ext (by have := congrArg Fin.val (hc1p.symm.trans hc1p'); simpa using this)
          rw [← hp1eq] at hp1'l2
          have hlne : l1 ≠ l2 := fun heq => hii (by rw [hi1l, hi2l, heq])
          obtain ⟨p2, l1', hp2l1', ⟨hc2p, hi1l'⟩ | ⟨hc2l, hi1p⟩⟩ := h21
          · have hl1eq : l1 = l1' := by
              have := congrArg Fin.val (hi1l.symm.trans hi1l')
              simp at this
              exact Fin.ext (by omega)
            rw [← hl1eq] at hp2l1'
            have hpne : p1 ≠ p2 := fun heq => hcc (by rw [hc1p, hc2p, heq])
            obtain ⟨p2', l2', hp2'l2', ⟨hc2p', hi2l'⟩ | ⟨hc2l', hi2p⟩⟩ := h22
            · have hp2eq : p2 = p2' := Fin.ext (by have := congrArg Fin.val (hc2p.symm.trans hc2p'); simpa using this)
              have hl2eq : l2 = l2' := by
                have := congrArg Fin.val (hi2l.symm.trans hi2l')
                simp at this
                exact Fin.ext (by omega)
              rw [← hp2eq, ← hl2eq] at hp2'l2'
              exact hUniqueLine p1 p2 l1 l2 hpne hlne ⟨hp1l1, hp2l1', hp1'l2, hp2'l2'⟩
            · have := congrArg Fin.val (hi2l.symm.trans hi2p)
              simp at this; omega
          · have := congrArg Fin.val (hi1l.symm.trans hi1p)
            simp at this; omega
        · have := congrArg Fin.val hc1l; simp at this; omega
      · have := congrArg Fin.val hc1l; simp at this; omega
    · obtain ⟨p1, l1, hp1l1, ⟨hc1p, _⟩ | ⟨hc1l, hi1p⟩⟩ := h11
      · have := congrArg Fin.val hc1p; simp at this; omega
      · obtain ⟨p2, l1', hp2l1', ⟨hc1p, _⟩ | ⟨hc1l', hi2p⟩⟩ := h12
        · have := congrArg Fin.val hc1p; simp at this; omega
        · have hl1eq : l1 = l1' := by
            have := congrArg Fin.val (hc1l.symm.trans hc1l')
            simp at this; exact Fin.ext (by omega)
          rw [← hl1eq] at hp2l1'
          have hpne : p1 ≠ p2 := fun heq => hii (by rw [hi1p, hi2p, heq])
          obtain ⟨p1', l2, hp1'l2, ⟨hc2p, hi1l⟩ | ⟨hc2l, hi1p'⟩⟩ := h21
          · have := congrArg Fin.val (hi1p.symm.trans hi1l); simp at this; omega
          · have hp1eq : p1 = p1' := Fin.ext (by have := congrArg Fin.val (hi1p.symm.trans hi1p'); simpa using this)
            rw [← hp1eq] at hp1'l2
            have hlne : l1 ≠ l2 := fun heq => hcc (by rw [hc1l, hc2l, heq])
            obtain ⟨p2', l2', hp2'l2', ⟨hc2p, hi2l⟩ | ⟨hc2l', hi2p'⟩⟩ := h22
            · have := congrArg Fin.val (hi2p.symm.trans hi2l); simp at this; omega
            · have hl2eq : l2 = l2' := by
                have := congrArg Fin.val (hc2l.symm.trans hc2l')
                simp at this; exact Fin.ext (by omega)
              have hp2eq : p2 = p2' := Fin.ext (by have := congrArg Fin.val (hi2p.symm.trans hi2p'); simpa using this)
              rw [← hl2eq, ← hp2eq] at hp2'l2'
              exact hUniqueLine p1 p2 l1 l2 hpne hlne ⟨hp1l1, hp2l1', hp1'l2, hp2'l2'⟩
  have hTwoOnLine : ∀ p q : Fin 13, ∃ l : Fin 13, p ∈ S l ∧ q ∈ S l := by decide +kernel
  have hTwoMeet : ∀ l1 l2 : Fin 13, ∃ p : Fin 13, p ∈ S l1 ∧ p ∈ S l2 := by decide +kernel
  have hPtOnLine : ∀ p : Fin 13, ∃ l : Fin 13, p ∈ S l := by decide +kernel
  have hIncidCard : (incidences S).card = 52 := by decide +kernel
  have hDeg4 : ∀ c : Fin 26, (Finset.univ.filter fun i => adj26 c i).card = 4 := by
    intro c
    refine Fin.addCases (m := 13) (n := 13) (motive := fun u => (Finset.univ.filter fun i => adj26 u i).card = 4)
      (fun p => ?_) (fun l => ?_) c
    · have hEq : (Finset.univ.filter fun i => adj26 (Fin.castAdd 13 p) i) =
          (Finset.univ.filter fun l : Fin 13 => p ∈ S l).map ⟨Fin.natAdd 13, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        constructor
        · rintro ⟨p', l', hp', ⟨hpEq, rfl⟩ | ⟨hImpossible, _⟩⟩
          · have hppe : p = p' := Fin.ext (by have := congrArg Fin.val hpEq; simpa using this)
            exact ⟨l', hppe ▸ hp', rfl⟩
          · have := congrArg Fin.val hImpossible; simp at this; omega
        · rintro ⟨l, hpl, rfl⟩
          exact ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hEq, Finset.card_map, pencilCard4 p]
    · have hEq : (Finset.univ.filter fun i => adj26 (Fin.natAdd 13 l) i) =
          (S l).map ⟨Fin.castAdd 13, fun a b h => Fin.ext (by have := congrArg Fin.val h; simpa using this)⟩ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        constructor
        · rintro ⟨p', l', hp', ⟨hImpossible, _⟩ | ⟨hlEq, rfl⟩⟩
          · have := congrArg Fin.val hImpossible; simp at this; omega
          · have hlle : l = l' := Fin.ext (by have := congrArg Fin.val hlEq; simp at this; omega)
            exact ⟨p', hlle ▸ hp', rfl⟩
        · rintro ⟨p, hpl, rfl⟩
          exact ⟨p, l, hpl, Or.inr ⟨rfl, rfl⟩⟩
      rw [hEq, Finset.card_map, lineCard4 l]
  classical
  have hEvalAnd : ∀ xs : List Bool, GateOp.and.eval xs = xs.all id := fun _ => rfl
  have hEvalOr : ∀ xs : List Bool, GateOp.or.eval xs = xs.any id := fun _ => rfl
  have hOpndDef : ∀ (C0 : Circuit) (j : ℕ) (idx : Fin 2), opnd C0 j idx = (gateAt C0 j).inputs.getD idx.val 0 := fun _ _ _ => rfl
  have hIncInDef : ∀ X Y : Finset (Fin 13), incidenceInput X Y =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) := fun _ _ => rfl
  have hIncInLen : ∀ X Y : Finset (Fin 13), (incidenceInput X Y).length = 26 := fun X Y => by
    rw [hIncInDef, List.length_append, List.length_ofFn, List.length_ofFn]
  have hSizeDef : ∀ C0 : Circuit, C0.size = C0.gates.length := fun _ => rfl
  have hMissLinesDef : ∀ (S0 : Fin 13 → Finset (Fin 13)) (P : Finset (Fin 13)),
      missLines S0 P = Finset.univ.filter (fun l => Disjoint (S0 l) P) := fun _ _ => rfl
  have hZeroSetDef : ∀ (S0 : Fin 13 → Finset (Fin 13)) (Y0 : Finset (Fin 13)),
      zeroSet S0 Y0 = Finset.univ.filter (fun p => ∀ l ∈ Y0, p ∉ S0 l) := fun _ _ => rfl
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  let bdSum (n : ℕ) (s : Bool ⊕ ℕ) : Prop := Sum.casesOn s (fun _ => True) (fun w => w < 26 + n)
  let evalSum (x : Fin 26 → Bool) (gs : List Gate) (s : Bool ⊕ ℕ) : Bool :=
    Sum.casesOn s (fun b => b) (fun w => (run gs (List.ofFn x)).getD w false)
  have hRunLen : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih =>
      intro w
      change (run gs (step w g)).length = w.length + (gs.length + 1)
      rw [ih]
      simp [step]
      omega
  have hRunSnoc : ∀ (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ),
      (run (gs ++ [g]) w).getD i false =
        if i = w.length + gs.length then g.op.eval (g.inputs.map fun j => (run gs w).getD j false)
        else (run gs w).getD i false := by
    intro gs g w i
    change ((gs ++ [g]).foldl step w).getD i false = _
    rw [List.foldl_append]
    change (step (run gs w) g).getD i false = _
    unfold step
    rw [← hRunLen gs w]
    split_ifs with hi
    · subst hi
      simp [List.getD_eq_getElem?_getD]
    · by_cases hlt : i < (run gs w).length
      · exact List.getD_append _ _ _ _ hlt
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have hRunMono : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ w1 w2 : List Bool, w1.length = w2.length →
        (∀ i, w1.getD i false = true → w2.getD i false = true) →
        ∀ i, (run gs w1).getD i false = true → (run gs w2).getD i false = true := by
    intro gs hgs
    induction gs using List.reverseRecOn with
    | nil => intro w1 w2 _ hle i hi; exact hle i hi
    | append_singleton gs g ih =>
      intro w1 w2 hlen hle i hi
      have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (by simp [hg'])
      have ih' := ih hgs' w1 w2 hlen hle
      rw [hRunSnoc, hlen] at hi
      rw [hRunSnoc]
      split_ifs at hi ⊢ with heq
      · have hg := (hgs g (by simp)).1
        rcases (show g.op = GateOp.and ∨ g.op = GateOp.or by simpa using hg) with h | h
        · rw [h, hEvalAnd] at hi ⊢
          simp only [List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
          intro j hj
          exact ih' j (hi j hj)
        · rw [h, hEvalOr] at hi ⊢
          simp only [List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
          rcases hi with ⟨j, hj, hv⟩
          exact ⟨j, hj, ih' j hv⟩
      · exact ih' i hi
  let D0 : Circuit := ⟨C.gates ++ [⟨GateOp.and, [a.val, b.val]⟩], 26 + C.size⟩
  have hD0Size : D0.size = C.size + 1 := by rw [hSizeDef, hSizeDef]; simp [D0]
  have hD0Mono : Monotone2 D0 := by
    intro g hg
    change g ∈ C.gates ++ [⟨GateOp.and, [a.val, b.val]⟩] at hg
    rcases List.mem_append.mp hg with hgC | hgNew
    · exact hMono g hgC
    · rw [List.mem_singleton] at hgNew
      subst hgNew
      simp
  have hD0Eval : ∀ x : Fin 26 → Bool,
      D0.eval (List.ofFn x) =
        GateOp.and.eval [(C.wires (List.ofFn x)).getD a.val false,
          (C.wires (List.ofFn x)).getD b.val false] := by
    intro x
    change (run (C.gates ++ [⟨GateOp.and, [a.val, b.val]⟩]) (List.ofFn x)).getD (26 + C.size) false = _
    rw [hRunSnoc]
    have hlen : (List.ofFn x).length + C.gates.length = 26 + C.size := by rw [List.length_ofFn, hSizeDef]
    rw [ite_eq_left hlen.symm]
    rfl
  let neg (X Y : Finset (Fin 13)) : Prop :=
    IsFalseInput S X Y ∧ ((∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l)
  have hGeomExt : ∀ X Y : Finset (Fin 13), neg X Y →
      ∃ P : Finset (Fin 13),
        (∀ q ∉ P, ∃ l ∈ missLines S P, q ∈ S l) ∧
        (P.card ≤ 2 ∨ (missLines S P).card ≤ 2 ∨ P.card = 3 ∧ ∃ l, P ⊆ S l) ∧
        X ⊆ P ∧ Y ⊆ missLines S P := by
    intro X Y hneg
    obtain ⟨hFalse, hDeg⟩ := hneg
    have hYsub : ∀ P, X ⊆ P → (∀ l ∈ Y, Disjoint (S l) P) → Y ⊆ missLines S P := by
      intro P _ hDisj l hl
      rw [hMissLinesDef]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hDisj l hl
    rcases hDeg with ⟨l, hXl⟩ | ⟨p, hYp⟩
    · by_cases hYe : Y = ∅
      · subst hYe
        exact ⟨Finset.univ, univMax.1, Or.inr (Or.inl univMax.2), Finset.subset_univ _, Finset.empty_subset _⟩
      · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
        have hDisj0 : Disjoint (S l0) X := hFalse l0 hl0
        have hXcard3 : X.card ≤ 3 := by
          by_cases heq : l0 = l
          · subst heq
            have hXe : X = ∅ := Finset.subset_empty.mp (fun x hx => absurd (hXl hx) (Finset.disjoint_left.mp hDisj0.symm hx))
            simp [hXe]
          · obtain ⟨p, hp1, hp2⟩ := twoLinesMeet l l0 (Ne.symm heq)
            have hpnot : p ∉ X := fun hx => Finset.disjoint_left.mp hDisj0 hp2 hx
            have hsub : X ⊆ (S l).erase p := Finset.subset_erase.mpr ⟨hXl, hpnot⟩
            have hcard : ((S l).erase p).card = 3 := by
              rw [Finset.card_erase_of_mem hp1, lineCard4 l]
            exact (Finset.card_le_card hsub).trans_eq hcard
        rcases Nat.lt_or_eq_of_le hXcard3 with hlt | heq3
        · have hXle2 : X.card ≤ 2 := by omega
          rcases Nat.eq_zero_or_pos X.card with h0 | hpos
          · have hXe : X = ∅ := Finset.card_eq_zero.mp h0
            subst hXe
            exact ⟨∅, emptyMax.1, Or.inl emptyMax.2, Finset.Subset.rfl, hYsub ∅ Finset.Subset.rfl (fun m _ => Finset.disjoint_empty_right _)⟩
          · obtain ⟨a1, b1, hab1⟩ : ∃ p q : Fin 13, X = {p, q} := by
              rcases (show X.card = 1 ∨ X.card = 2 by omega) with h1 | h2
              · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
                exact ⟨p, p, by simp [hp]⟩
              · obtain ⟨p, q, _, hpq⟩ := Finset.card_eq_two.mp h2
                exact ⟨p, q, hpq⟩
            rw [hab1]
            exact ⟨{a1, b1}, (le2Max a1 b1).1, Or.inl (le2Max a1 b1).2, Finset.Subset.rfl,
              fun m hm => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab1 ▸ hFalse m hm⟩⟩
        · have hne : l0 ≠ l := by
            rintro rfl
            have hXe : X = ∅ := Finset.subset_empty.mp (fun x hx => absurd (hXl hx) (Finset.disjoint_left.mp hDisj0.symm hx))
            simp [hXe] at heq3
          obtain ⟨p, hp1, hp2⟩ := twoLinesMeet l l0 (Ne.symm hne)
          have hpnot : p ∉ X := fun hx => Finset.disjoint_left.mp hDisj0 hp2 hx
          have hsub : X ⊆ (S l).erase p := Finset.subset_erase.mpr ⟨hXl, hpnot⟩
          have hlem := lineEraseMax l p hp1
          have hXeq : X = (S l).erase p := Finset.eq_of_subset_of_card_le hsub (by rw [hlem.2.1, heq3])
          rw [hXeq]
          exact ⟨(S l).erase p, hlem.1, Or.inr (Or.inr ⟨hlem.2.1, l, hlem.2.2⟩), Finset.Subset.rfl,
            fun m hm => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hXeq ▸ hFalse m hm⟩⟩
    · let pn := Finset.univ.filter fun l => p ∈ S l
      have hYsubPn : Y ⊆ pn := fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hYp l hl⟩
      have hYle4 : Y.card ≤ 4 := (Finset.card_le_card hYsubPn).trans_eq (pencilCard4 p)
      by_cases hYe : Y = ∅
      · subst hYe
        exact ⟨Finset.univ, univMax.1, Or.inr (Or.inl univMax.2), Finset.subset_univ _, Finset.empty_subset _⟩
      · rcases Nat.lt_or_eq_of_le hYle4 with hlt4 | heq4
        · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt4) with hlt3 | heq3
          · have hYle2 : Y.card ≤ 2 := by omega
            obtain ⟨l1, l2, hYeq⟩ : ∃ l1 l2 : Fin 13, Y = {l1, l2} := by
              have hpos : 0 < Y.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hYe)
              rcases (show Y.card = 1 ∨ Y.card = 2 by omega) with h1 | h2
              · obtain ⟨l1, hl1⟩ := Finset.card_eq_one.mp h1
                exact ⟨l1, l1, by simp [hl1]⟩
              · obtain ⟨l1, l2, _, hl12⟩ := Finset.card_eq_two.mp h2
                exact ⟨l1, l2, hl12⟩
            have hlem := pairLineMax l1 l2
            refine ⟨zeroSet S {l1, l2}, hlem.1, Or.inr (Or.inl hlem.2.1), ?_, ?_⟩
            · intro q hq
              rw [hZeroSetDef]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              intro l hl hql
              rw [← hYeq] at hl
              exact Finset.disjoint_left.mp (hFalse l hl) hql hq
            · rw [hYeq]; exact hlem.2.2
          · have hDiffCard : (pn \ Y).card = 1 := by
              rw [Finset.card_sdiff_of_subset hYsubPn, pencilCard4 p, heq3]
            obtain ⟨l0, hl0⟩ := Finset.card_eq_one.mp hDiffCard
            have hl0mem : l0 ∈ pn \ Y := by rw [hl0]; exact Finset.mem_singleton_self _
            have hl0pn : l0 ∈ pn := (Finset.mem_sdiff.mp hl0mem).1
            have hpSl0 : p ∈ S l0 := (Finset.mem_filter.mp hl0pn).2
            have hYeq : Y = pn.erase l0 := by
              rw [← Finset.sdiff_singleton_eq_erase, ← hl0, Finset.sdiff_sdiff_eq_self hYsubPn]
            have hlem := threePencilMax p l0 hpSl0
            refine ⟨(S l0).erase p, hlem.1, Or.inr (Or.inr ⟨hlem.2.1, l0, hlem.2.2.1⟩), ?_, ?_⟩
            · intro q hq
              apply hlem.2.2.2.2 q
              intro l hl hql
              rw [← hYeq] at hl
              exact Finset.disjoint_left.mp (hFalse l hl) hql hq
            · rw [hYeq]; exact hlem.2.2.2.1
        · have hYeq : Y = pn := Finset.eq_of_subset_of_card_le hYsubPn (by rw [pencilCard4 p, heq4])
          have hXe : X = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro q hq
            obtain ⟨l, hlp, hlq⟩ := fourPencilCover p q
            have hlY : l ∈ Y := hYeq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlp⟩
            exact Finset.disjoint_left.mp (hFalse l hlY) hlq hq
          subst hXe
          exact ⟨∅, emptyMax.1, Or.inl emptyMax.2, Finset.Subset.rfl, hYsub ∅ Finset.Subset.rfl (fun m _ => Finset.disjoint_empty_right _)⟩
  have hD0Pos : RightOnIncidentPairs S D0 := by
    intro l p hp
    have hin : Inc p l := (hIncIff p l).mp hp
    have h1 := hPos p l hin
    have hrow : incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) =
        List.ofFn (fun u : Fin 26 => decide (u = Fin.castAdd 13 p ∨ u = Fin.natAdd 13 l)) := by
      rw [hIncInDef]
      rw [← List.ofFn_fin_append]
      congr 1
      funext u
      refine Fin.addCases (m := 13) (n := 13) (fun q => ?_) (fun m => ?_) u
      · rw [Fin.append_left]
        apply decide_eq_decide.mpr
        simp only [Finset.mem_singleton]
        constructor
        · intro hq; exact Or.inl (by rw [hq])
        · rintro (hq | hm)
          · exact Fin.ext (by have := congrArg Fin.val hq; simpa using this)
          · have := congrArg Fin.val hm; simp at this; omega
      · rw [Fin.append_right]
        apply decide_eq_decide.mpr
        simp only [Finset.mem_singleton]
        constructor
        · intro hm; exact Or.inr (by rw [hm])
        · rintro (hq | hm)
          · have := congrArg Fin.val hq; simp at this; omega
          · exact Fin.ext (by have := congrArg Fin.val hm; simp at this; omega)
    rw [hrow, hD0Eval]
    rw [show (fun x6 : Fin 26 => @Decidable.decide (x6 = Fin.castAdd 13 p ∨ x6 = Fin.natAdd 13 l) _) =
        (fun u : Fin 26 => decide (u = Fin.castAdd 13 p ∨ u = Fin.natAdd 13 l))
      from funext fun _ => decide_eq_decide.mpr Iff.rfl] at h1
    exact h1
  have hD0Neg : ∀ X Y : Finset (Fin 13), neg X Y → D0.eval (incidenceInput X Y) = false := by
    intro X Y hneg
    obtain ⟨P, hPmax, hPdeg, hXP, hYP⟩ := hGeomExt X Y hneg
    have hPmax' : ∀ q ∉ P, ∃ l, (∀ r ∈ P, ¬Inc r l) ∧ Inc q l := by
      intro q hq
      obtain ⟨l, hlM, hql⟩ := hPmax q hq
      have hDisj := (Finset.mem_filter.mp hlM).2
      exact ⟨l, fun r hr hrl => Finset.disjoint_left.mp hDisj ((hIncIff r l).mpr hrl) hr,
        (hIncIff q l).mp hql⟩
    have hPdeg' : P.card ≤ 2 ∨ Nat.card { l : Fin 13 // ∀ r ∈ P, ¬Inc r l } ≤ 2 ∨
        P.card = 3 ∧ ∃ l, ∀ r ∈ P, Inc r l := by
      rcases hPdeg with h1 | h2 | ⟨h3, l, hl⟩
      · exact Or.inl h1
      · refine Or.inr (Or.inl ?_)
        have e : { l : Fin 13 // ∀ r ∈ P, ¬Inc r l } ≃ { l : Fin 13 // l ∈ missLines S P } :=
          { toFun := fun l => ⟨l.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Finset.disjoint_left.mpr fun p hp1 hp2 => l.2 p hp2 ((hIncIff p l.1).mp hp1)⟩⟩
            invFun := fun l => ⟨l.1, fun r hr hrl =>
              Finset.disjoint_left.mp (Finset.mem_filter.mp l.2).2 ((hIncIff r l.1).mpr hrl) hr⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
        exact h2
      · exact Or.inr (Or.inr ⟨h3, l, fun r hr => (hIncIff r l).mp (hl hr)⟩)
    have hPfalse := hDegMax P hPmax' hPdeg'
    let bigVec : Fin 26 → Bool := fun u =>
      decide ((∃ p ∈ P, u = Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, u = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬∃ d ∈ Dset, q = l + d)
    have hBigEq : incidenceInput P (missLines S P) = List.ofFn bigVec := by
      rw [hIncInDef]
      rw [← List.ofFn_fin_append]
      congr 1
      funext u
      refine Fin.addCases (fun q => ?_) (fun m => ?_) u
      · rw [Fin.append_left]
        apply decide_eq_decide.mpr
        constructor
        · intro hq; exact Or.inl ⟨q, hq, rfl⟩
        · rintro (⟨r, hr, he⟩ | ⟨l, he, _⟩)
          · have : q = r := Fin.ext (by have := congrArg Fin.val he; simpa using this)
            exact this ▸ hr
          · have := congrArg Fin.val he; simp at this; omega
      · rw [Fin.append_right]
        apply decide_eq_decide.mpr
        rw [hMissLinesDef]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
        constructor
        · intro hm
          exact Or.inr ⟨m, rfl, fun q hq hd => hm ((hIncIff q m).mpr hd) hq⟩
        · rintro (⟨r, _, he⟩ | ⟨l, he, hl⟩)
          · have := congrArg Fin.val he; simp at this; omega
          · have : m = l := Fin.ext (by have := congrArg Fin.val he; simp at this; omega)
            subst this
            intro q hql hqP
            exact hl q hqP ((hIncIff q m).mp hql)
    have hPzero : D0.eval (incidenceInput P (missLines S P)) = false := by
      rw [hBigEq, hD0Eval]
      rw [show (fun x6 : Fin 26 => @Decidable.decide
          ((∃ x7 ∈ P, x6 = Fin.castAdd 13 x7) ∨
            ∃ x7, x6 = Fin.natAdd 13 x7 ∧ ∀ x8 ∈ P, ¬∃ x10 ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x8 = x7 + x10) _) = bigVec
        from funext fun _ => decide_eq_decide.mpr Iff.rfl] at hPfalse
      exact hPfalse
    let smallVec : Fin 26 → Bool := fun u =>
      Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y)) u
    have hSmallEq : incidenceInput X Y = List.ofFn smallVec := by
      rw [hIncInDef]
      rw [← List.ofFn_fin_append]
      rfl
    have hMonoIn : ∀ i : ℕ, (incidenceInput X Y).getD i false = true →
        (incidenceInput P (missLines S P)).getD i false = true := by
      intro i hi
      by_cases hi26 : i < 26
      · rw [hSmallEq] at hi
        rw [hBigEq]
        rw [List.getD_eq_getElem _ _ (by simp [hi26]), List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ (by simp [hi26]), List.getElem_ofFn]
        let u : Fin 26 := ⟨i, hi26⟩
        change smallVec u = true at hi
        change bigVec u = true
        revert hi
        refine Fin.addCases (m := 13) (n := 13) (motive := fun j => smallVec j = true → bigVec j = true) (fun p hp => ?_) (fun l hl => ?_) u
        · simp only [smallVec, Fin.addCases_left, decide_eq_true_eq] at hp
          exact decide_eq_true (Or.inl ⟨p, hXP hp, rfl⟩)
        · simp only [smallVec, Fin.addCases_right, decide_eq_true_eq] at hl
          have hlM := hYP hl
          rw [hMissLinesDef] at hlM
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left] at hlM
          exact decide_eq_true (Or.inr ⟨l, rfl, fun q hq hd => hlM ((hIncIff q l).mpr hd) hq⟩)
      · rw [List.getD_eq_default _ _ (by rw [hIncInLen]; omega)] at hi
        cases hi
    cases hv : D0.eval (incidenceInput X Y) with
    | false => rfl
    | true =>
      have hlen : (incidenceInput X Y).length = (incidenceInput P (missLines S P)).length := by
        rw [hIncInLen, hIncInLen]
      have hUp := hRunMono D0.gates hD0Mono _ _ hlen hMonoIn D0.output hv
      change D0.eval (incidenceInput P (missLines S P)) = true at hUp
      rw [hPzero] at hUp
      cases hUp
  have hCompile : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∃ (gs' : List Gate) (mw : ℕ → Bool ⊕ ℕ),
        (∀ g ∈ gs', g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length = 2) ∧
        (∀ j < gs'.length, ∀ i ∈ (gs'.getD j ⟨GateOp.or, []⟩).inputs, i < 26 + j) ∧
        gs'.length ≤ gs.countP (fun g => decide (2 ≤ g.inputs.length)) ∧
        (∀ i, bdSum gs'.length (mw i)) ∧
        (∀ (x : Fin 26 → Bool) (i : ℕ),
          (run gs (List.ofFn x)).getD i false = evalSum x gs' (mw i)) := by
    intro gs hgs
    induction gs using List.reverseRecOn with
    | nil =>
      refine ⟨[], fun i => if i < 26 then Sum.inr i else Sum.inl false, by simp, by simp, by simp, ?_, ?_⟩
      · intro i
        dsimp only
        split_ifs with hi
        · exact hi
        · trivial
      · intro x i
        dsimp only
        split_ifs with hi
        · rfl
        · rw [List.getD_eq_default _ _ (by simp [run]; omega)]
    | append_singleton gs g ih =>
      have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (by simp [hg'])
      obtain ⟨gs', mw, hAO', hRB', hCnt', hBd', hSem'⟩ := ih hgs'
      have hg := hgs g (by simp)
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
      let ev (u : ℕ) : Bool ⊕ ℕ := if u < 26 + gs.length then mw u else Sum.inl false
      have hEvBd : ∀ u, bdSum gs'.length (ev u) := by
        intro u
        dsimp only [ev]
        split_ifs with hu
        · exact hBd' u
        · trivial
      have hEvSem : ∀ (x : Fin 26 → Bool) (u : ℕ),
          (run gs (List.ofFn x)).getD u false = evalSum x gs' (ev u) := by
        intro x u
        dsimp only [ev]
        split_ifs with hu
        · exact hSem' x u
        · rw [List.getD_eq_default _ _ (by rw [hRunLen]; simp; omega)]
      have hStep2 : ∃ (extra : List Gate) (res : Bool ⊕ ℕ),
          (∀ g0 ∈ extra, g0.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g0.inputs.length = 2) ∧
          (∀ j < extra.length, ∀ i ∈ (extra.getD j ⟨GateOp.or, []⟩).inputs, i < 26 + gs'.length + j) ∧
          extra.length ≤ (if 2 ≤ g.inputs.length then 1 else 0) ∧
          bdSum (gs'.length + extra.length) res ∧
          (∀ (x : Fin 26 → Bool),
            g.op.eval (g.inputs.map fun u => (run gs (List.ofFn x)).getD u false) =
              evalSum x (gs' ++ extra) res) := by
        rcases hins : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, zs⟩⟩⟩
        · refine ⟨[], Sum.inl (if g.op = GateOp.and then true else false), by simp, by simp, by simp, trivial, ?_⟩
          intro x
          dsimp only [evalSum]
          rcases hop with h | h
          · rw [h, hEvalAnd]; simp
          · rw [h, hEvalOr]; simp
        · refine ⟨[], ev u, by simp, by simp, by simp, hEvBd u, ?_⟩
          intro x
          have hsemu := hEvSem x u
          dsimp only [evalSum]
          rcases hop with h | h
          · rw [h, hEvalAnd]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, List.append_nil]
            exact hsemu
          · rw [h, hEvalOr]
            simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, List.append_nil]
            exact hsemu
        · have hbin : ∀ (a b : Bool ⊕ ℕ),
              bdSum gs'.length a →
              bdSum gs'.length b →
              ∃ (extra : List Gate) (res : Bool ⊕ ℕ),
                (∀ g0 ∈ extra, g0.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g0.inputs.length = 2) ∧
                (∀ j < extra.length, ∀ i ∈ (extra.getD j ⟨GateOp.or, []⟩).inputs, i < 26 + gs'.length + j) ∧
                extra.length ≤ 1 ∧
                bdSum (gs'.length + extra.length) res ∧
                (∀ x : Fin 26 → Bool,
                  let va := evalSum x gs' a
                  let vb := evalSum x gs' b
                  g.op.eval [va, vb] = evalSum x (gs' ++ extra) res) := by
            intro a b ha hb
            rcases hop with h | h
            · rcases a with ca | wa <;> rcases b with cb | wb
              · refine ⟨[], Sum.inl (ca && cb), by simp, by simp, by simp, trivial, fun x => ?_⟩
                dsimp only [evalSum]; rw [h, hEvalAnd]; simp
              · cases ca
                · refine ⟨[], Sum.inl false, by simp, by simp, by simp, trivial, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalAnd]; simp
                · refine ⟨[], Sum.inr wb, by simp, by simp, by simp, hb, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalAnd]; simp
              · cases cb
                · refine ⟨[], Sum.inl false, by simp, by simp, by simp, trivial, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalAnd]; simp
                · refine ⟨[], Sum.inr wa, by simp, by simp, by simp, ha, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalAnd]; simp
              · refine ⟨[⟨GateOp.and, [wa, wb]⟩], Sum.inr (26 + gs'.length), ?_, ?_, by simp, by dsimp only [bdSum]; simp, fun x => ?_⟩
                · simp
                · intro j hj i hi
                  simp only [List.length_cons, List.length_nil] at hj
                  have hj0 : j = 0 := by omega
                  subst hj0
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
                    List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · exact ha
                  · exact hb
                · dsimp only [evalSum]
                  rw [hRunSnoc]
                  have hlen : (List.ofFn x).length + gs'.length = 26 + gs'.length := by simp
                  rw [ite_eq_left hlen.symm, h]
                  rfl
            · rcases a with ca | wa <;> rcases b with cb | wb
              · refine ⟨[], Sum.inl (ca || cb), by simp, by simp, by simp, trivial, fun x => ?_⟩
                dsimp only [evalSum]; rw [h, hEvalOr]; simp
              · cases ca
                · refine ⟨[], Sum.inr wb, by simp, by simp, by simp, hb, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalOr]; simp
                · refine ⟨[], Sum.inl true, by simp, by simp, by simp, trivial, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalOr]; simp
              · cases cb
                · refine ⟨[], Sum.inr wa, by simp, by simp, by simp, ha, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalOr]; simp
                · refine ⟨[], Sum.inl true, by simp, by simp, by simp, trivial, fun x => ?_⟩
                  dsimp only [evalSum]; rw [h, hEvalOr]; simp
              · refine ⟨[⟨GateOp.or, [wa, wb]⟩], Sum.inr (26 + gs'.length), ?_, ?_, by simp, by dsimp only [bdSum]; simp, fun x => ?_⟩
                · simp
                · intro j hj i hi
                  simp only [List.length_cons, List.length_nil] at hj
                  have hj0 : j = 0 := by omega
                  subst hj0
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
                    List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · exact ha
                  · exact hb
                · dsimp only [evalSum]
                  rw [hRunSnoc]
                  have hlen : (List.ofFn x).length + gs'.length = 26 + gs'.length := by simp
                  rw [ite_eq_left hlen.symm]
                  simp only [h, hEvalOr]
                  simp
          obtain ⟨extra, res, h1, h2, h3, h4, h5⟩ := hbin (ev u) (ev v) (hEvBd u) (hEvBd v)
          refine ⟨extra, res, h1, h2, by simp [h3], h4, fun x => ?_⟩
          rw [List.map_cons, List.map_cons, List.map_nil, hEvSem x u, hEvSem x v]
          exact h5 x
        · exfalso
          have hlen := hg.2
          rw [hins] at hlen
          simp at hlen
      obtain ⟨extra, res, hExAO, hExRB, hExLen, hResBd, hExSem⟩ := hStep2
      refine ⟨gs' ++ extra, fun i => if i = 26 + gs.length then res else mw i, ?_, ?_, ?_, ?_, ?_⟩
      · intro g0 hg0
        rcases List.mem_append.mp hg0 with hg0' | hg0'
        · exact hAO' g0 hg0'
        · exact hExAO g0 hg0'
      · intro j hj i hi
        by_cases hj' : j < gs'.length
        · have hjEq : (gs' ++ extra).getD j ⟨GateOp.or, []⟩ = gs'.getD j ⟨GateOp.or, []⟩ := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
          rw [hjEq] at hi
          exact hRB' j hj' i hi
        · have hge : gs'.length ≤ j := Nat.le_of_not_lt hj'
          have hjSub : j - gs'.length < extra.length := by
            rw [List.length_append] at hj; omega
          have hjEq : (gs' ++ extra).getD j ⟨GateOp.or, []⟩ = extra.getD (j - gs'.length) ⟨GateOp.or, []⟩ := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
          rw [hjEq] at hi
          have := hExRB (j - gs'.length) hjSub i hi
          omega
      · rw [List.length_append, List.countP_append]
        have hcg : [g].countP (fun g0 => decide (2 ≤ g0.inputs.length)) = if 2 ≤ g.inputs.length then 1 else 0 := by
          simp
        omega
      · intro i
        dsimp only [bdSum]
        split_ifs with hi
        · cases res with
          | inl _ => trivial
          | inr w => dsimp only [bdSum] at hResBd ⊢; rw [List.length_append]; omega
        · have hiBd := hBd' i
          cases hmw : mw i with
          | inl b => trivial
          | inr w =>
            rw [hmw] at hiBd
            dsimp only [bdSum] at hiBd ⊢
            rw [List.length_append]
            omega
      · intro x i
        rw [hRunSnoc]
        have hlen : (List.ofFn x).length + gs.length = 26 + gs.length := by simp
        rw [hlen]
        dsimp only [evalSum]
        split_ifs with hi
        · exact hExSem x
        · rw [hSem' x i]
          cases hmw : mw i with
          | inl b => rfl
          | inr w =>
            dsimp only [evalSum]
            have hw : w < 26 + gs'.length := by have := hBd' i; rw [hmw] at this; exact this
            rcases (show extra = [] ∨ ∃ g0, extra = [g0] by
              have hl : extra.length ≤ 1 := by
                refine hExLen.trans ?_; split_ifs <;> omega
              rcases extra with _ | ⟨g0, _ | _⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨g0, rfl⟩
              · simp at hl) with rfl | ⟨g0, rfl⟩
            · simp only [List.append_nil]
            · rw [hRunSnoc]
              have hlen' : (List.ofFn x).length + gs'.length = 26 + gs'.length := by simp
              rw [hlen', ite_eq_right (by omega)]
  have hNormalize : ∀ D : Circuit, Monotone2 D →
      RightOnIncidentPairs S D → (∀ X Y : Finset (Fin 13), neg X Y → D.eval (incidenceInput X Y) = false) →
      ∃ E : Circuit, IsAO2 26 E ∧ E.size ≤ D.gates.countP (fun g => decide (2 ≤ g.inputs.length)) ∧
        ∀ x : Fin 26 → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x) := by
    intro D hDm hDp hDn
    obtain ⟨gs', mw, hAO', hRB', hLen', hBd', hSem'⟩ := hCompile D.gates hDm
    have hSemD : ∀ x : Fin 26 → Bool,
        D.eval (List.ofFn x) = evalSum x gs' (mw D.output) := fun x => hSem' x D.output
    cases hOut : mw D.output with
    | inl b =>
      exfalso
      cases b
      · have h0 := hDp 0 0 (by decide)
        have hrow : incidenceInput ({(0 : Fin 13)} : Finset (Fin 13)) ({(0 : Fin 13)} : Finset (Fin 13)) =
            List.ofFn (Fin.addCases (m := 13) (n := 13) (fun p : Fin 13 => decide (p = 0)) (fun l : Fin 13 => decide (l = 0))) := by
          rw [hIncInDef, ← List.ofFn_fin_append]; rfl
        rw [hrow, hSemD, hOut] at h0
        dsimp only [evalSum] at h0
        cases h0
      · have h0 := hDn ∅ ∅ ⟨fun l hl => by simp at hl, Or.inl ⟨0, by simp⟩⟩
        have hrow : incidenceInput (∅ : Finset (Fin 13)) (∅ : Finset (Fin 13)) =
            List.ofFn (fun _ : Fin 26 => false) := by
          rw [hIncInDef]
          rw [← List.ofFn_fin_append]
          congr 1
          funext u
          by_cases h13 : u.val < 13
          · have huc : u = Fin.castAdd 13 ⟨u.val, h13⟩ := Fin.ext rfl
            rw [huc, Fin.append_left]
            simp
          · have hun : u = Fin.natAdd 13 ⟨u.val - 13, by omega⟩ := Fin.ext (by simp; omega)
            rw [hun, Fin.append_right]
            simp
        rw [hrow, hSemD, hOut] at h0
        dsimp only [evalSum] at h0
        cases h0
    | inr w =>
      refine ⟨⟨gs', w⟩, ⟨?_, ?_, ?_⟩, hLen', fun x => ?_⟩
      · intro g hg
        have := (hAO' g hg).1
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      · intro j hj i hi
        have hge : gateAt ⟨gs', w⟩ j = gs'.getD j ⟨GateOp.or, []⟩ := rfl
        rw [hge] at hi
        exact hRB' j hj i hi
      · intro g hg
        exact (hAO' g hg).2
      · change (run gs' (List.ofFn x)).getD w false = D.eval (List.ofFn x)
        rw [hSemD x, hOut]
  let good (E : Circuit) : Prop :=
    IsAO2 26 E ∧ RightOnIncidentPairs S E ∧
    ∀ X Y : Finset (Fin 13), neg X Y → E.eval (incidenceInput X Y) = false
  have hD0GoodExist : ∃ n, ∃ E : Circuit, good E ∧ E.size = n := by
    obtain ⟨E0, hAO, hSz, hEq⟩ := hNormalize D0 hD0Mono hD0Pos hD0Neg
    refine ⟨E0.size, E0, ⟨hAO, ?_, ?_⟩, rfl⟩
    · intro l p hp
      have hvec : ∃ x : Fin 26 → Bool, incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x :=
        ⟨_, (List.ofFn_fin_append _ _).symm⟩
      obtain ⟨x, hx⟩ := hvec
      rw [hx, hEq x, ← hx]
      exact hD0Pos l p hp
    · intro X Y hxy
      have hvec : ∃ x : Fin 26 → Bool, incidenceInput X Y = List.ofFn x :=
        ⟨_, (List.ofFn_fin_append _ _).symm⟩
      obtain ⟨x, hx⟩ := hvec
      rw [hx, hEq x, ← hx]
      exact hD0Neg X Y hxy
  let nMin := Nat.find hD0GoodExist
  obtain ⟨E, hEgood, hEsize⟩ := Nat.find_spec hD0GoodExist
  have hEmin : ∀ D : Circuit, good D → E.size ≤ D.size := by
    intro D hD
    rw [hEsize]
    exact Nat.find_min' hD0GoodExist ⟨D, hD, rfl⟩
  have hEbound : E.size ≤ C.size + 1 := by
    obtain ⟨E0, hAO, hSz, hEq⟩ := hNormalize D0 hD0Mono hD0Pos hD0Neg
    have hE0good : good E0 := ⟨hAO, fun l p hp => by
      have hx : ∃ x : Fin 26 → Bool, incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x :=
        ⟨_, (List.ofFn_fin_append _ _).symm⟩
      obtain ⟨x, hx⟩ := hx; rw [hx, hEq x, ← hx]; exact hD0Pos l p hp,
      fun X Y hxy => by
      have hx : ∃ x : Fin 26 → Bool, incidenceInput X Y = List.ofFn x :=
        ⟨_, (List.ofFn_fin_append _ _).symm⟩
      obtain ⟨x, hx⟩ := hx; rw [hx, hEq x, ← hx]; exact hD0Neg X Y hxy⟩
    have h1 := hEmin E0 hE0good
    have h2 : D0.gates.countP (fun g => decide (2 ≤ g.inputs.length)) ≤ D0.gates.length := List.countP_le_length
    change E0.size ≤ _ at hSz
    change D0.gates.length = C.size + 1 at hD0Size
    omega
  have hAndNotZero : andPairs 26 E = 0 → 64 ≤ E.size := by
    intro hAnd0
    obtain ⟨hEAO, hEPos, hENeg⟩ := hEgood
    obtain ⟨hEAOO, hERB, hELen2⟩ := hEAO
    have hEMono : Monotone2 E := by
      intro g hg
      exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hEAOO g hg, (hELen2 g hg).le⟩
    have hEOutBound : 26 ≤ E.output ∧ E.output < 26 + E.gates.length := by
      constructor
      · by_contra! hlt
        obtain ⟨p, l, hpl, hnp, hnl⟩ := hOther ⟨E.output, hlt⟩
        have hpos := hEPos l p hpl
        change (run E.gates (incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)))).getD E.output false = true at hpos
        have hkeep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
            (run gs w).getD i false = w.getD i false := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil => intro w i _; rfl
          | append_singleton gs g ih =>
            intro w i hi
            have hlen := hRunLen gs w
            rw [hRunSnoc, ite_eq_right (by omega)]
            exact ih w i hi
        rw [hkeep E.gates _ E.output (by rw [hIncInLen]; exact hlt)] at hpos
        rw [hIncInDef] at hpos
        by_cases h13 : E.output < 13
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [h13]),
            List.getElem?_eq_getElem (by simp [h13]), Option.getD_some, List.getElem_ofFn] at hpos
          simp only [Finset.mem_singleton, decide_eq_true_eq] at hpos
          exact hnp (congrArg Fin.val hpos.symm)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
            List.length_ofFn, List.getElem?_eq_getElem (by simp; omega), Option.getD_some, List.getElem_ofFn] at hpos
          simp only [Finset.mem_singleton, decide_eq_true_eq] at hpos
          have heq : E.output - 13 = l.val := congrArg Fin.val hpos
          have hnl' : 13 + l.val ≠ E.output := hnl
          omega
      · by_contra! hge
        have hpos := hEPos 0 0 (by decide)
        change (run E.gates (incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13)))).getD E.output false = true at hpos
        rw [List.getD_eq_default _ _ (by rw [hRunLen, hIncInLen]; exact hge)] at hpos
        cases hpos
    have hConesProp : ∀ (gs : List Gate),
        (∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, w < 26 + j) →
        (gs.foldl (coneStep 26) []).length = gs.length ∧
        (∀ j < gs.length, ∀ i ∈ (gs.foldl (coneStep 26) []).getD j [], i < j) ∧
        (∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 26 ≤ w →
          (w - 26) ∈ (gs.foldl (coneStep 26) []).getD j [] ∧
          ∀ i ∈ (gs.foldl (coneStep 26) []).getD (w - 26) [], i ∈ (gs.foldl (coneStep 26) []).getD j []) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil => intro _; simp
      | append_singleton gs g ih =>
        intro hrb
        have hrb' : ∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, w < 26 + j := by
          intro j hj w hw
          have h1 := hrb j (by simp; omega) w
          have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
            List.getD_append _ _ _ _ hj
          rw [hget] at h1
          exact h1 hw
        obtain ⟨ihLen, ihLt, ihStep⟩ := ih hrb'
        have hfold : (gs ++ [g]).foldl (coneStep 26) [] =
            coneStep 26 (gs.foldl (coneStep 26) []) g := by
          rw [List.foldl_append]; rfl
        set cs := gs.foldl (coneStep 26) []
        have hcslen : cs.length = gs.length := ihLen
        let newC := (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
          (fun w => (w - 26) :: cs.getD (w - 26) [])
        have hcsSnoc : (gs ++ [g]).foldl (coneStep 26) [] = cs ++ [newC] := hfold
        refine ⟨by rw [hcsSnoc, List.length_append, hcslen]; simp, ?_, ?_⟩
        · intro j hj i hi
          rw [hcsSnoc] at hi
          by_cases hj' : j < gs.length
          · rw [List.getD_append _ _ _ _ (by rw [hcslen]; exact hj')] at hi
            exact ihLt j hj' i hi
          · have hjeq : j = gs.length := by rw [List.length_append] at hj; simp at hj; omega
            subst hjeq
            rw [List.getD_append_right _ _ _ _ (by omega), hcslen, Nat.sub_self] at hi
            simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
              newC, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons] at hi
            rcases hi with ⟨w, ⟨_, h26, hlt⟩, rfl | hi'⟩
            · omega
            · have := ihLt (w - 26) (by omega) i hi'
              omega
        · intro j hj w hw hw26
          rw [hcsSnoc]
          by_cases hj' : j < gs.length
          · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
              List.getD_append _ _ _ _ hj'
            rw [hget] at hw
            have hltw : w < 26 + j := hrb' j hj' w hw
            rw [List.getD_append _ _ _ _ (by rw [hcslen]; exact hj'),
              List.getD_append _ _ _ _ (by rw [hcslen]; omega)]
            exact ihStep j hj' w hw hw26
          · have hjeq : j = gs.length := by rw [List.length_append] at hj; simp at hj; omega
            subst hjeq
            have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
              rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
            rw [hget] at hw
            have hltw : w < 26 + gs.length := hrb gs.length (by simp) w (by rw [hget]; exact hw)
            have hwfilt : w ∈ g.inputs.filter (fun u => decide (26 ≤ u ∧ u < 26 + cs.length)) :=
              List.mem_filter.mpr ⟨hw, decide_eq_true ⟨hw26, by omega⟩⟩
            rw [List.getD_append_right _ _ _ _ (by omega), hcslen, Nat.sub_self,
              List.getD_append _ _ _ _ (by rw [hcslen]; omega)]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
              newC, List.mem_flatMap, List.mem_cons]
            exact ⟨⟨w, hwfilt, Or.inl rfl⟩, fun i hi => ⟨w, hwfilt, Or.inr hi⟩⟩
    obtain ⟨hCLen, hCLt, hCStep⟩ := hConesProp E.gates hERB
    have hInConeStep : ∀ j < E.gates.length, ∀ w ∈ (gateAt E j).inputs, 26 ≤ w →
        InCone 26 E (w - 26) j ∧ ∀ i, InCone 26 E i (w - 26) → InCone 26 E i j := by
      intro j hj w hw hw26
      have h1 := hCStep j hj w hw hw26
      exact ⟨h1.1, fun i hi => h1.2 i hi⟩
    have hInConeMono : ∀ j < E.gates.length, ∀ w ∈ (gateAt E j).inputs, 26 ≤ w →
        InCone 26 E (w - 26) j := fun j hj w hw hw26 => (hInConeStep j hj w hw hw26).1
    have hNoAndInCone : ∀ i j, i < E.gates.length → j < E.gates.length →
        (gateAt E i).op = GateOp.and → (gateAt E j).op = GateOp.and → ¬ InCone 26 E i j := by
      intro i j hi hj hopi hopj hcone
      have hmem : (i, j) ∈ (Finset.range E.gates.length ×ˢ Finset.range E.gates.length).filter fun p =>
          (gateAt E p.1).op = GateOp.and ∧ (gateAt E p.2).op = GateOp.and ∧ InCone 26 E p.1 p.2 :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩,
          hopi, hopj, hcone⟩
      have hpos : 0 < andPairs 26 E := by
        unfold andPairs
        exact Finset.card_pos.mpr ⟨(i, j), by simpa using hmem⟩
      omega
    let noAndBelow (w : ℕ) : Prop :=
      (∀ j < E.gates.length, w = 26 + j → (gateAt E j).op = GateOp.or) ∧
      (26 ≤ w → ∀ i < E.gates.length, InCone 26 E i (w - 26) → (gateAt E i).op = GateOp.or)
    have hOpCases : ∀ j < E.gates.length, (gateAt E j).op = GateOp.and ∨ (gateAt E j).op = GateOp.or := by
      intro j hj
      have hm : gateAt E j ∈ E.gates := by
        change E.gates.getD j ⟨GateOp.or, []⟩ ∈ E.gates
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hEAOO _ hm
    have hNoAndOfAnd : ∀ k < E.gates.length, (gateAt E k).op = GateOp.and →
        ∀ w ∈ (gateAt E k).inputs, noAndBelow w := by
      intro k hk hopk w hw
      have hwlt := hERB k hk w hw
      constructor
      · intro j hj heq
        subst heq
        rcases hOpCases j hj with hjand | hjor
        · exfalso
          exact hNoAndInCone j k hj hk hjand hopk (by simpa using hInConeMono k hk (26 + j) hw (by omega))
        · exact hjor
      · intro hw26 i hi hcone
        rcases hOpCases i hi with hiand | hior
        · exfalso
          exact hNoAndInCone i k hi hk hiand hopk ((hInConeStep k hk w hw hw26).2 i hcone)
        · exact hior
    have hNoAndStep : ∀ m < E.gates.length, noAndBelow (26 + m) →
        ∀ w ∈ (gateAt E m).inputs, noAndBelow w := by
      intro m hm hno w hw
      have hwlt := hERB m hm w hw
      constructor
      · intro j hj heq
        subst heq
        have hcone : InCone 26 E j m := by simpa using hInConeMono m hm (26 + j) hw (by omega)
        exact hno.2 (by omega) j hj (by simpa using hcone)
      · intro hw26 i hi hcone
        have hcone' : InCone 26 E i m := (hInConeStep m hm w hw hw26).2 i hcone
        exact hno.2 (by omega) i hi (by simpa using hcone')
    let stepIn (acc : List (Finset (Fin 26))) (g : Gate) : List (Finset (Fin 26)) :=
      acc ++ [if g.op = GateOp.or then (g.inputs.map fun w => acc.getD w ∅).foldr (· ∪ ·) ∅ else ∅]
    let initIn : List (Finset (Fin 26)) := List.ofFn fun i : Fin 26 => {i}
    have hStepInProp : ∀ (gs : List Gate) (acc : List (Finset (Fin 26))),
        acc.length = 26 →
        (∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, w < 26 + j) →
        (gs.foldl stepIn acc).length = 26 + gs.length ∧
        (∀ i < 26, (gs.foldl stepIn acc).getD i ∅ = acc.getD i ∅) ∧
        (∀ j < gs.length, (gs.foldl stepIn acc).getD (26 + j) ∅ =
          if (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or then
            ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun w => (gs.foldl stepIn acc).getD w ∅).foldr (· ∪ ·) ∅
          else ∅) := by
      intro gs acc hacc
      induction gs using List.reverseRecOn with
      | nil => intro _; simp [hacc]
      | append_singleton gs g ih =>
        intro hrb
        have hrb' : ∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, w < 26 + j := by
          intro j hj w hw
          have h1 := hrb j (by simp; omega) w
          rw [List.getD_append _ _ _ _ hj] at h1
          exact h1 hw
        obtain ⟨ihLen, ihInit, ihGate⟩ := ih hrb'
        set prev := gs.foldl stepIn acc
        have hprevLen : prev.length = 26 + gs.length := ihLen
        let newSet := if g.op = GateOp.or then (g.inputs.map fun w => prev.getD w ∅).foldr (· ∪ ·) ∅ else ∅
        have hsnoc : (gs ++ [g]).foldl stepIn acc = prev ++ [newSet] := by
          rw [List.foldl_append]; rfl
        refine ⟨by rw [hsnoc, List.length_append, List.length_singleton, hprevLen, List.length_append, List.length_singleton]; omega, ?_, ?_⟩
        · intro i hi
          rw [hsnoc, List.getD_append _ _ _ _ (by rw [hprevLen]; omega)]
          exact ihInit i hi
        · intro j hj
          rw [hsnoc]
          by_cases hj' : j < gs.length
          · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
              List.getD_append _ _ _ _ hj'
            rw [hget, List.getD_append _ _ _ _ (by rw [hprevLen]; omega), ihGate j hj']
            by_cases hop : (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or
            · rw [ite_eq_left hop, ite_eq_left hop]
              congr 1
              apply List.map_congr_left
              intro w hw
              have hwlt := hrb' j hj' w hw
              rw [List.getD_append _ _ _ _ (by rw [hprevLen]; omega)]
            · rw [ite_eq_right hop, ite_eq_right hop]
          · have hjeq : j = gs.length := by rw [List.length_append] at hj; simp at hj; omega
            subst hjeq
            have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
              rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
            rw [hget, List.getD_append_right _ _ _ _ (by omega), hprevLen, Nat.sub_self]
            have hgetNew : [newSet].getD 0 ∅ = newSet := rfl
            rw [hgetNew]
            dsimp only [newSet]
            by_cases hop : g.op = GateOp.or
            · rw [ite_eq_left hop, ite_eq_left hop]
              congr 1
              apply List.map_congr_left
              intro w hw
              have hwlt := hrb gs.length (by simp) w (by rw [hget]; exact hw)
              have hwlt' : w < prev.length := by rw [hprevLen]; exact hwlt
              rw [List.getD_append _ _ _ _ hwlt']
            · rw [ite_eq_right hop, ite_eq_right hop]
    obtain ⟨hSILen, hSIInit, hSIGate⟩ := hStepInProp E.gates initIn (by simp [initIn]) hERB
    let orReachSet (w : ℕ) : Finset (Fin 26) := (E.gates.foldl stepIn initIn).getD w ∅
    have hORInput : ∀ i : Fin 26, orReachSet i.val = {i} := by
      intro i
      change (E.gates.foldl stepIn initIn).getD i.val ∅ = {i}
      rw [hSIInit i.val i.isLt]
      dsimp only [initIn]
      rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
    have hORGate : ∀ j < E.gates.length, orReachSet (26 + j) =
        if (gateAt E j).op = GateOp.or then
          ((gateAt E j).inputs.map orReachSet).foldr (· ∪ ·) ∅
        else ∅ := fun j hj => hSIGate j hj
    have hEGateVal : ∀ (j : ℕ) (hj : j < E.gates.length) (x : Fin 26 → Bool),
        (run E.gates (List.ofFn x)).getD (26 + j) false =
          (gateAt E j).op.eval ((gateAt E j).inputs.map fun w => (run E.gates (List.ofFn x)).getD w false) := by
      intro j hj x
      have htake : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (i : ℕ),
          k ≤ gs.length → i < w.length + k →
          (run gs w).getD i false = (run (gs.take k) w).getD i false := by
        intro gs w k i hk hi
        conv_lhs => rw [← List.take_append_drop k gs]
        have hpref : ∀ (pre post : List Gate) (w0 : List Bool) (i0 : ℕ), i0 < w0.length + pre.length →
            (run (pre ++ post) w0).getD i0 false = (run pre w0).getD i0 false := by
          intro pre post w0 i0 hi0
          induction post using List.reverseRecOn with
          | nil => simp
          | append_singleton post g0 ih =>
            have hlen := hRunLen (pre ++ post) w0
            have hne : i0 ≠ w0.length + (pre ++ post).length := by rw [List.length_append]; omega
            rw [← List.append_assoc, hRunSnoc, ite_eq_right hne]
            exact ih
        exact hpref _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)
      have h1 := htake E.gates (List.ofFn x) (j + 1) (26 + j) (Nat.succ_le_of_lt hj) (by simp)
      rw [h1, List.take_succ_eq_append_getElem hj, hRunSnoc]
      have hlen : (List.ofFn x).length + (E.gates.take j).length = 26 + j := by
        rw [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      rw [ite_eq_left hlen.symm]
      have hgate : E.gates[j] = gateAt E j := by
        change E.gates[j] = E.gates.getD j ⟨GateOp.or, []⟩
        rw [List.getD_eq_getElem _ _ hj]
      rw [hgate]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hwlt := hERB j hj w hw
      have h2 := htake E.gates (List.ofFn x) j w (Nat.le_of_lt hj) (by simp; exact hwlt)
      exact h2.symm
    have hOrReachSem : ∀ w < 26 + E.gates.length, noAndBelow w → ∀ x : Fin 26 → Bool,
        (run E.gates (List.ofFn x)).getD w false = true ↔ ∃ i ∈ orReachSet w, x i = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hno x
        by_cases hw26 : w < 26
        · let i0 : Fin 26 := ⟨w, hw26⟩
          have hkeep : ∀ (gs : List Gate) (w0 : List Bool) (i : ℕ), i < w0.length →
              (run gs w0).getD i false = w0.getD i false := by
            intro gs
            induction gs using List.reverseRecOn with
            | nil => intro w0 i _; rfl
            | append_singleton gs g ih =>
              intro w0 i hi
              have hlen := hRunLen gs w0
              rw [hRunSnoc, ite_eq_right (by omega)]
              exact ih w0 i hi
          rw [hkeep E.gates _ w (by simp [hw26]), List.getD_eq_getElem _ _ (by simp [hw26]),
            List.getElem_ofFn, hORInput i0]
          simp [i0]
        · have hj : w - 26 < E.gates.length := by omega
          have heq : 26 + (w - 26) = w := by omega
          have hop : (gateAt E (w - 26)).op = GateOp.or := hno.1 (w - 26) hj heq.symm
          rw [← heq, hEGateVal (w - 26) hj x, hop, hORGate (w - 26) hj, ite_eq_left hop, hEvalOr]
          simp only [List.any_map, List.any_eq_true, Function.comp, id]
          constructor
          · rintro ⟨u, hu, hvu⟩
            have hult := hERB (w - 26) hj u hu
            have hnoU := hNoAndStep (w - 26) hj (by rw [heq]; exact hno) u hu
            obtain ⟨i, hi, hxi⟩ := (ih u (by omega) (by omega) hnoU x).mp hvu
            refine ⟨i, ?_, hxi⟩
            have hfold : ∀ (l : List (Finset (Fin 26))) (s : Finset (Fin 26)),
                s ∈ l → s ⊆ l.foldr (· ∪ ·) ∅ := by
              intro l s hs
              induction l with
              | nil => simp at hs
              | cons a t iht =>
                rcases List.mem_cons.mp hs with rfl | ht
                · exact Finset.subset_union_left
                · exact (iht ht).trans Finset.subset_union_right
            exact hfold _ _ (List.mem_map.mpr ⟨u, hu, rfl⟩) hi
          · rintro ⟨i, hi, hxi⟩
            have hfold : ∀ (l : List (Finset (Fin 26))),
                i ∈ l.foldr (· ∪ ·) ∅ → ∃ s ∈ l, i ∈ s := by
              intro l hl
              induction l with
              | nil => simp at hl
              | cons a t iht =>
                rcases Finset.mem_union.mp hl with ha | ht
                · exact ⟨a, List.mem_cons_self, ha⟩
                · obtain ⟨s, hs, his⟩ := iht ht
                  exact ⟨s, List.mem_cons_of_mem _ hs, his⟩
            obtain ⟨s, hs, his⟩ := hfold _ hi
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
            have hult := hERB (w - 26) hj u hu
            have hnoU := hNoAndStep (w - 26) hj (by rw [heq]; exact hno) u hu
            exact ⟨u, hu, (ih u (by omega) (by omega) hnoU x).mpr ⟨i, his, hxi⟩⟩
    have hReplaceGate : ∀ (j : ℕ) (hj : j < E.gates.length) (gNew : Gate),
        (∀ x : Fin 26 → Bool,
          (run E.gates (List.ofFn x)).getD (26 + j) false =
            gNew.op.eval (gNew.inputs.map fun w => (run E.gates (List.ofFn x)).getD w false)) →
        gNew.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) → gNew.inputs.length < 2 →
        (∀ i ∈ gNew.inputs, i < 26 + j) → False := by
      intro j hj gNew hSemG hOpG hLenG hRBG
      let gs1 := E.gates.set j gNew
      let D1 : Circuit := ⟨gs1, E.output⟩
      have hgs1Len : gs1.length = E.gates.length := List.length_set
      have hD1Mono : Monotone2 D1 := by
        intro g hg
        obtain ⟨idx, hidx, hgk⟩ := List.mem_iff_getElem.mp hg
        rw [hgs1Len] at hidx
        by_cases hkj : idx = j
        · subst hkj
          rw [List.getElem_set_self (by rw [List.length_set]; exact hj)] at hgk
          subst hgk
          exact ⟨hOpG, hLenG.le⟩
        · rw [List.getElem_set_ne (Ne.symm hkj) (by rw [List.length_set]; exact hidx)] at hgk
          subst hgk
          exact hEMono _ (List.getElem_mem hidx)
      have hgs1RB : ∀ k < gs1.length, ∀ i ∈ (gs1.getD k ⟨GateOp.or, []⟩).inputs, i < 26 + k := by
        intro k hk i hi
        rw [hgs1Len] at hk
        by_cases hkj : k = j
        · subst hkj
          have hget : gs1.getD k ⟨GateOp.or, []⟩ = gNew := by
            rw [List.getD_eq_getElem _ _ (by rw [hgs1Len]; exact hk)]
            exact List.getElem_set_self (by rw [hgs1Len]; exact hk)
          rw [hget] at hi
          exact hRBG i hi
        · have hget : gs1.getD k ⟨GateOp.or, []⟩ = E.gates.getD k ⟨GateOp.or, []⟩ := by
            rw [List.getD_eq_getElem _ _ (by rw [hgs1Len]; exact hk),
              List.getD_eq_getElem _ _ hk]
            exact List.getElem_set_ne (Ne.symm hkj) (by rw [hgs1Len]; exact hk)
          rw [hget] at hi
          exact hERB k hk i hi
      have hgs1GateVal : ∀ (k : ℕ) (hk : k < gs1.length) (x : Fin 26 → Bool),
          (run gs1 (List.ofFn x)).getD (26 + k) false =
            (gs1.getD k ⟨GateOp.or, []⟩).op.eval
              ((gs1.getD k ⟨GateOp.or, []⟩).inputs.map fun w => (run gs1 (List.ofFn x)).getD w false) := by
        intro k hk x
        have htake : ∀ (gs : List Gate) (w : List Bool) (m : ℕ) (i : ℕ),
            m ≤ gs.length → i < w.length + m →
            (run gs w).getD i false = (run (gs.take m) w).getD i false := by
          intro gs w m i hm hi
          conv_lhs => rw [← List.take_append_drop m gs]
          have hpref : ∀ (pre post : List Gate) (w0 : List Bool) (i0 : ℕ), i0 < w0.length + pre.length →
              (run (pre ++ post) w0).getD i0 false = (run pre w0).getD i0 false := by
            intro pre post w0 i0 hi0
            induction post using List.reverseRecOn with
            | nil => simp
            | append_singleton post g0 ih =>
              have hlen := hRunLen (pre ++ post) w0
              have hne : i0 ≠ w0.length + (pre ++ post).length := by rw [List.length_append]; omega
              rw [← List.append_assoc, hRunSnoc, ite_eq_right hne]
              exact ih
          exact hpref _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hm]; exact hi)
        have h1 := htake gs1 (List.ofFn x) (k + 1) (26 + k) (Nat.succ_le_of_lt hk) (by simp)
        rw [h1, List.take_succ_eq_append_getElem hk, hRunSnoc]
        have hlen : (List.ofFn x).length + (gs1.take k).length = 26 + k := by
          rw [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
        rw [ite_eq_left hlen.symm, List.getD_eq_getElem _ _ hk]
        congr 1
        apply List.map_congr_left
        intro w hw
        have hwlt := hgs1RB k hk w (by rw [List.getD_eq_getElem _ _ hk]; exact hw)
        exact (htake gs1 (List.ofFn x) k w (Nat.le_of_lt hk) (by simp; exact hwlt)).symm
      have hWiresEq : ∀ x : Fin 26 → Bool, ∀ w : ℕ,
          (run gs1 (List.ofFn x)).getD w false = (run E.gates (List.ofFn x)).getD w false := by
        intro x w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          by_cases hw26 : w < 26
          · have hkeep : ∀ (gs : List Gate) (w0 : List Bool) (i : ℕ), i < w0.length →
                (run gs w0).getD i false = w0.getD i false := by
              intro gs
              induction gs using List.reverseRecOn with
              | nil => intro w0 i _; rfl
              | append_singleton gs g ih' =>
                intro w0 i hi; have hlen := hRunLen gs w0; rw [hRunSnoc, ite_eq_right (by omega)]; exact ih' w0 i hi
            rw [hkeep gs1 _ w (by simp [hw26]), hkeep E.gates _ w (by simp [hw26])]
          · by_cases hwEnd : 26 + E.gates.length ≤ w
            · rw [List.getD_eq_default _ _ (by rw [hRunLen, hgs1Len]; simp; exact hwEnd),
                List.getD_eq_default _ _ (by rw [hRunLen]; simp; exact hwEnd)]
            · have hk : w - 26 < E.gates.length := by omega
              have heq : 26 + (w - 26) = w := by omega
              rw [← heq, hgs1GateVal (w - 26) (by rw [hgs1Len]; exact hk) x]
              by_cases hkj : w - 26 = j
              · have hwEq : w = 26 + j := by omega
                rw [hkj] at *
                have hget : gs1.getD j ⟨GateOp.or, []⟩ = gNew := by
                  rw [List.getD_eq_getElem _ _ (by rw [hgs1Len]; exact hj)]
                  exact List.getElem_set_self (by rw [hgs1Len]; exact hj)
                rw [hget, hSemG x]
                congr 1
                apply List.map_congr_left
                intro u hu
                exact ih u (by have := hRBG u hu; omega)
              · have hget : gs1.getD (w - 26) ⟨GateOp.or, []⟩ = gateAt E (w - 26) := by
                  rw [List.getD_eq_getElem _ _ (by rw [hgs1Len]; exact hk)]
                  change gs1[w - 26] = E.gates.getD (w - 26) ⟨GateOp.or, []⟩
                  rw [List.getD_eq_getElem _ _ hk]
                  exact List.getElem_set_ne (Ne.symm hkj) (by rw [hgs1Len]; exact hk)
                rw [hget, hEGateVal (w - 26) hk x]
                congr 1
                apply List.map_congr_left
                intro u hu
                exact ih u (by have := hERB (w - 26) hk u hu; omega)
      have hD1Pos : RightOnIncidentPairs S D1 := by
        intro l p hp
        have hx : ∃ x : Fin 26 → Bool, incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x :=
          ⟨_, (List.ofFn_fin_append _ _).symm⟩
        obtain ⟨x, hx⟩ := hx
        change (run gs1 (incidenceInput {p} {l})).getD E.output false = true
        rw [hx, hWiresEq x E.output, ← hx]
        exact hEPos l p hp
      have hD1Neg : ∀ X Y : Finset (Fin 13), neg X Y → D1.eval (incidenceInput X Y) = false := by
        intro X Y hxy
        have hx : ∃ x : Fin 26 → Bool, incidenceInput X Y = List.ofFn x :=
          ⟨_, (List.ofFn_fin_append _ _).symm⟩
        obtain ⟨x, hx⟩ := hx
        change (run gs1 (incidenceInput X Y)).getD E.output false = false
        rw [hx, hWiresEq x E.output, ← hx]
        exact hENeg X Y hxy
      have hCntDrop : ∀ (l : List Gate) (k : ℕ), k < l.length →
          (l.set k gNew).countP (fun g => decide (2 ≤ g.inputs.length)) < l.length := by
        intro l
        induction l with
        | nil => intro k hk; simp at hk
        | cons a t ih =>
          intro k hk
          cases k with
          | zero =>
            rw [List.set_cons_zero, List.countP_cons_of_neg (by simp; omega), List.length_cons]
            have hle := List.countP_le_length (p := fun g : Gate => decide (2 ≤ g.inputs.length)) (l := t)
            omega
          | succ k =>
            rw [List.set_cons_succ, List.countP_cons]
            rw [List.length_cons] at hk
            have h1 := ih k (by omega)
            rw [List.length_cons]
            cases (decide (2 ≤ a.inputs.length)) <;> dsimp <;> omega
      obtain ⟨E2, hE2AO, hE2Sz, hE2Eq⟩ := hNormalize D1 hD1Mono hD1Pos hD1Neg
      have hE2good : good E2 := ⟨hE2AO, fun l p hp => by
        have hx : ∃ x : Fin 26 → Bool, incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x :=
          ⟨_, (List.ofFn_fin_append _ _).symm⟩
        obtain ⟨x, hx⟩ := hx; rw [hx, hE2Eq x, ← hx]; exact hD1Pos l p hp,
        fun X Y hxy => by
        have hx : ∃ x : Fin 26 → Bool, incidenceInput X Y = List.ofFn x :=
          ⟨_, (List.ofFn_fin_append _ _).symm⟩
        obtain ⟨x, hx⟩ := hx; rw [hx, hE2Eq x, ← hx]; exact hD1Neg X Y hxy⟩
      have hle := hEmin E2 hE2good
      have hlt := hCntDrop E.gates j hj
      have hE2Sz' : E2.size = E2.gates.length := rfl
      have hESz' : E.size = E.gates.length := rfl
      have hD1Gs : D1.gates = gs1 := rfl
      rw [hE2Sz', hD1Gs] at hE2Sz
      dsimp only [gs1] at hE2Sz
      rw [hESz', hE2Sz'] at hle
      omega
    have hOrReachGe2 : ∀ j < E.gates.length, noAndBelow (26 + j) → 2 ≤ (orReachSet (26 + j)).card := by
      intro j hj hno
      by_contra! hlt2
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt2) with h0 | h1
      · have hEmpty : orReachSet (26 + j) = ∅ := Finset.card_eq_zero.mp (by omega)
        apply hReplaceGate j hj ⟨GateOp.or, []⟩ (fun x => ?_) (by simp) (by simp) (by simp)
        cases hv : (run E.gates (List.ofFn x)).getD (26 + j) false with
        | false => rfl
        | true =>
          obtain ⟨i, hi, _⟩ := (hOrReachSem (26 + j) (by omega) hno x).mp hv
          rw [hEmpty] at hi
          simp at hi
      · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
        apply hReplaceGate j hj ⟨GateOp.or, [u.val]⟩ (fun x => ?_) (by simp) (by simp) (by
          intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rw [hi]; have := u.isLt; omega)
        rw [hEvalOr]
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have hkeep : ∀ (gs : List Gate) (w0 : List Bool) (i : ℕ), i < w0.length →
            (run gs w0).getD i false = w0.getD i false := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil => intro w0 i _; rfl
          | append_singleton gs g ih =>
            intro w0 i hi; have hlen := hRunLen gs w0; rw [hRunSnoc, ite_eq_right (by omega)]; exact ih w0 i hi
        rw [hkeep E.gates _ u.val (by rw [List.length_ofFn]; exact u.isLt)]
        rw [List.getD_eq_getElem (List.ofFn x) false (by rw [List.length_ofFn]; exact u.isLt), List.getElem_ofFn]
        apply Bool.eq_iff_iff.mpr
        rw [hOrReachSem (26 + j) (by omega) hno x, hu]
        simp
    let downStep (k : ℕ) (S0 : Finset ℕ) : Finset ℕ :=
      if (gateAt E k).op = GateOp.or ∧ 26 + k ∈ S0 then S0 ∪ (gateAt E k).inputs.toFinset else S0
    let downClosure (m : ℕ) (seeds : Finset ℕ) : Finset ℕ :=
      (List.range m).foldr downStep seeds
    have hDCSucc : ∀ m seeds, downClosure (m + 1) seeds = downClosure m (downStep m seeds) := by
      intro m seeds
      simp only [downClosure, List.range_succ, List.foldr_append]
      rfl
    have hDownSub : ∀ m seeds, seeds ⊆ downClosure m seeds := by
      intro m
      induction m with
      | zero => intro seeds; exact Finset.Subset.rfl
      | succ m ih =>
        intro seeds
        rw [hDCSucc]
        refine Finset.Subset.trans ?_ (ih (downStep m seeds))
        dsimp only [downStep]
        split_ifs
        · exact Finset.subset_union_left
        · exact Finset.Subset.rfl
    have hDownUpper : ∀ m seeds w, w ∈ downClosure m seeds →
        w ∈ seeds ∨ ∃ k < m, (gateAt E k).op = GateOp.or ∧ 26 + k ∈ downClosure m seeds ∧ w ∈ (gateAt E k).inputs := by
      intro m
      induction m with
      | zero => intro seeds w hw; left; exact hw
      | succ m ih =>
        intro seeds w hw
        rw [hDCSucc] at hw
        rcases ih (downStep m seeds) w hw with hw1 | ⟨k, hk, hopk, hmemk, hwk⟩
        · dsimp only [downStep] at hw1
          split_ifs at hw1 with hcond
          · rcases Finset.mem_union.mp hw1 with hws | hwin
            · exact Or.inl hws
            · refine Or.inr ⟨m, Nat.lt_succ_self m, hcond.1, ?_, List.mem_toFinset.mp hwin⟩
              rw [hDCSucc]
              exact hDownSub m _ (by dsimp only [downStep]; rw [ite_eq_left hcond]; exact Finset.mem_union_left _ hcond.2)
          · exact Or.inl hw1
        · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, hopk, by rw [hDCSucc]; exact hmemk, hwk⟩
    have hDownClosed : ∀ m, m ≤ E.gates.length → ∀ seeds k, k < m → (gateAt E k).op = GateOp.or →
        26 + k ∈ downClosure m seeds → (gateAt E k).inputs.toFinset ⊆ downClosure m seeds := by
      intro m
      induction m with
      | zero => intro _ _ k hk; omega
      | succ m ih =>
        intro hm seeds k hk hopk hmem
        rw [hDCSucc] at hmem ⊢
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
        · exact ih (Nat.le_of_lt hm) (downStep m seeds) k hlt hopk hmem
        · have hmSeeds : 26 + k ∈ seeds := by
            rcases hDownUpper k (downStep k seeds) (26 + k) hmem with hm1 | ⟨r, hr, _, _, hwr⟩
            · dsimp only [downStep] at hm1
              split_ifs at hm1 with hcond
              · rcases Finset.mem_union.mp hm1 with h1 | h2
                · exact h1
                · have hlt := hERB k hm (26 + k) (List.mem_toFinset.mp h2)
                  omega
              · exact hm1
            · have hlt := hERB r (by omega) (26 + k) hwr
              omega
          refine Finset.Subset.trans ?_ (hDownSub k (downStep k seeds))
          dsimp only [downStep]
          rw [ite_eq_left ⟨hopk, hmSeeds⟩]
          exact Finset.subset_union_right
    have hDownUp : ∀ m, m ≤ E.gates.length → ∀ seeds (x : Fin 26 → Bool),
        (∃ w ∈ downClosure m seeds, (run E.gates (List.ofFn x)).getD w false = true) →
        ∃ w ∈ seeds, (run E.gates (List.ofFn x)).getD w false = true := by
      intro m
      induction m with
      | zero => intro _ seeds x h; exact h
      | succ m ih =>
        intro hm seeds x h
        rw [hDCSucc] at h
        obtain ⟨w, hw, hv⟩ := ih (Nat.le_of_lt hm) (downStep m seeds) x h
        dsimp only [downStep] at hw
        split_ifs at hw with hcond
        · rcases Finset.mem_union.mp hw with hws | hwin
          · exact ⟨w, hws, hv⟩
          · refine ⟨26 + m, hcond.2, ?_⟩
            rw [hEGateVal m hm x, hcond.1, hEvalOr]
            simp only [List.any_map, List.any_eq_true, Function.comp, id]
            exact ⟨w, List.mem_toFinset.mp hwin, hv⟩
        · exact ⟨w, hw, hv⟩
    have hDownEval : ∀ seeds (x : Fin 26 → Bool),
        (∃ w ∈ downClosure E.gates.length seeds, w < 26 + E.gates.length ∧ (run E.gates (List.ofFn x)).getD w false = true) →
        ∃ w ∈ downClosure E.gates.length seeds,
          (w < 26 ∨ (26 ≤ w ∧ w < 26 + E.gates.length ∧ (gateAt E (w - 26)).op = GateOp.and)) ∧
          (run E.gates (List.ofFn x)).getD w false = true := by
      intro seeds x hEx
      obtain ⟨w, hw, hwlt, hv⟩ := hEx
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        by_cases hw26 : w < 26
        · exact ⟨w, hw, Or.inl hw26, hv⟩
        · have hk : w - 26 < E.gates.length := by omega
          have heq : 26 + (w - 26) = w := by omega
          rcases hOpCases (w - 26) hk with hand | hor
          · exact ⟨w, hw, Or.inr ⟨by omega, hwlt, hand⟩, hv⟩
          · have hv' := hv
            rw [← heq, hEGateVal (w - 26) hk x, hor, hEvalOr] at hv'
            simp only [List.any_map, List.any_eq_true, Function.comp, id] at hv'
            obtain ⟨u, hu, hvu⟩ := hv'
            have hult := hERB (w - 26) hk u hu
            have huMem : u ∈ downClosure E.gates.length seeds :=
              hDownClosed E.gates.length (le_refl _) seeds (w - 26) hk hor (by rw [heq]; exact hw) (List.mem_toFinset.mpr hu)
            exact ih u (by omega) huMem (by omega) hvu
    let Stop := downClosure E.gates.length {E.output}
    have hStopBound : ∀ w ∈ Stop, 26 ≤ w ∧ w < 26 + E.gates.length := by
      have hUpper : ∀ w ∈ Stop, w < 26 + E.gates.length := by
        intro w hw
        rcases hDownUpper E.gates.length {E.output} w hw with h1 | ⟨k, hk, _, _, hwk⟩
        · simp only [Finset.mem_singleton] at h1
          rw [h1]; exact hEOutBound.2
        · have := hERB k hk w hwk
          omega
      have hNoInput : ∀ w ∈ Stop, 26 ≤ w := by
        intro w hw
        by_contra! hw26
        have hkeep : ∀ (gs : List Gate) (w0 : List Bool) (i : ℕ), i < w0.length →
            (run gs w0).getD i false = w0.getD i false := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil => intro w0 i _; rfl
          | append_singleton gs g ih =>
            intro w0 i hi; have hlen := hRunLen gs w0; rw [hRunSnoc, ite_eq_right (by omega)]; exact ih w0 i hi
        by_cases h13 : w < 13
        · let p : Fin 13 := ⟨w, h13⟩
          have hneg : neg {p} ∅ := ⟨fun l hl => by simp at hl, Or.inl ⟨p, fun q hq => by
            rw [Finset.mem_singleton.mp hq]; exact hptSelf p⟩⟩
          let x : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13) (fun q => decide (q = p)) (fun _ => false)
          have hrow : incidenceInput ({p} : Finset (Fin 13)) (∅ : Finset (Fin 13)) = List.ofFn x := by
            rw [hIncInDef]
            rw [← List.ofFn_fin_append]
            congr 1
            funext u
            refine Fin.addCases (m := 13) (n := 13) (fun q => by simp [x, Fin.append])
              (fun _ => by simp [x, Fin.append]) u
          have hvw : (run E.gates (List.ofFn x)).getD w false = true := by
            rw [hkeep E.gates _ w (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
            change x (Fin.castAdd 13 p) = true
            simp [x]
          obtain ⟨u, hu, hvu⟩ := hDownUp E.gates.length (le_refl _) {E.output} x ⟨w, hw, hvw⟩
          rw [Finset.mem_singleton.mp hu] at hvu
          have hbad := hENeg {p} ∅ hneg
          rw [hrow] at hbad
          change (run E.gates (List.ofFn x)).getD E.output false = false at hbad
          rw [hbad] at hvu
          cases hvu
        · let l : Fin 13 := ⟨w - 13, by omega⟩
          have hneg : neg ∅ {l} := ⟨fun m _ => Finset.disjoint_empty_right _, Or.inl ⟨0, by simp⟩⟩
          let x : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13) (fun _ => false) (fun m => decide (m = l))
          have hrow : incidenceInput (∅ : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x := by
            rw [hIncInDef]
            rw [← List.ofFn_fin_append]
            congr 1
            funext u
            refine Fin.addCases (m := 13) (n := 13) (fun _ => by simp [x, Fin.append])
              (fun m => by simp [x, Fin.append]) u
          have hvw : (run E.gates (List.ofFn x)).getD w false = true := by
            rw [hkeep E.gates _ w (by rw [List.length_ofFn]; omega),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]
            have hidx : (⟨w, hw26⟩ : Fin 26) = Fin.natAdd 13 l := by ext; dsimp [l]; omega
            change x ⟨w, hw26⟩ = true
            rw [hidx]
            dsimp only [x]
            rw [Fin.addCases_right]
            simp
          obtain ⟨u, hu, hvu⟩ := hDownUp E.gates.length (le_refl _) {E.output} x ⟨w, hw, hvw⟩
          rw [Finset.mem_singleton.mp hu] at hvu
          have hbad := hENeg ∅ {l} hneg
          rw [hrow] at hbad
          change (run E.gates (List.ofFn x)).getD E.output false = false at hbad
          rw [hbad] at hvu
          cases hvu
      exact fun w hw => ⟨hNoInput w hw, hUpper w hw⟩
    let T := (Finset.range E.gates.length).filter fun j => 26 + j ∈ Stop ∧ (gateAt E j).op = GateOp.or
    let Aused := (Finset.range E.gates.length).filter fun j => 26 + j ∈ Stop ∧ (gateAt E j).op = GateOp.and
    have hATDisj : Disjoint Aused T := by
      rw [Finset.disjoint_left]
      intro j hjA hjT
      have h1 := (Finset.mem_filter.mp hjA).2.2
      have h2 := (Finset.mem_filter.mp hjT).2.2
      rw [h1] at h2
      cases h2
    have hACardLeT : Aused.card ≤ T.card + 1 := by
      let outIdx := E.output - 26
      have houtIdx : outIdx < E.gates.length := by omega
      have houtEq : 26 + outIdx = E.output := by omega
      have hOutStop : E.output ∈ Stop := hDownSub E.gates.length {E.output} (Finset.mem_singleton_self _)
      rcases hOpCases outIdx houtIdx with handOut | horOut
      · have hTEmpty : T = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro j hjT
          have hmem : ∀ w ∈ Stop, w ≠ E.output → ∃ k ∈ T, w ∈ (gateAt E k).inputs := by
            intro w hw hne
            rcases hDownUpper E.gates.length {E.output} w hw with h1 | ⟨k, hk, hopk, hkStop, hwk⟩
            · exfalso; exact hne (Finset.mem_singleton.mp h1)
            · exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkStop, hopk⟩, hwk⟩
          have hne : T.Nonempty := ⟨j, hjT⟩
          let m := T.max' hne
          have hmT : m ∈ T := Finset.max'_mem T hne
          have hmStop : 26 + m ∈ Stop := (Finset.mem_filter.mp hmT).2.1
          have hmNe : 26 + m ≠ E.output := by
            intro heq
            have hmeq : m = outIdx := by omega
            have hmOp := (Finset.mem_filter.mp hmT).2.2
            rw [hmeq, handOut] at hmOp
            cases hmOp
          obtain ⟨k, hkT, hmk⟩ := hmem (26 + m) hmStop hmNe
          have hklt := (Finset.mem_filter.mp hkT).1
          have hkLt : k < E.gates.length := Finset.mem_range.mp hklt
          have hlt := hERB k hkLt (26 + m) hmk
          have hle := Finset.le_max' T k hkT
          omega
        have hAOne : Aused = {outIdx} := by
          ext j
          simp only [Aused, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨hj, hjStop, hjOp⟩
            by_contra hne
            rcases hDownUpper E.gates.length {E.output} (26 + j) hjStop with h1 | ⟨k, hk, hopk, hkStop, _⟩
            · exact hne (by have := Finset.mem_singleton.mp h1; omega)
            · have hkT : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkStop, hopk⟩
              rw [hTEmpty] at hkT
              simp at hkT
          · intro rfl
            exact ⟨houtIdx, houtEq.symm ▸ hOutStop, handOut⟩
        rw [hTEmpty, hAOne]
        simp
      · have houtT : outIdx ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr houtIdx, houtEq.symm ▸ hOutStop, horOut⟩
        let srcs := Aused.image (26 + ·) ∪ (T.erase outIdx).image (26 + ·)
        have hSub : srcs ⊆ T.biUnion (fun k => (gateAt E k).inputs.toFinset) := by
          intro w hw
          have hwStop : w ∈ Stop := by
            rcases Finset.mem_union.mp hw with hwA | hwT
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hwA
              exact (Finset.mem_filter.mp hj).2.1
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hwT
              exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2.1
          have hwNe : w ≠ E.output := by
            rcases Finset.mem_union.mp hw with hwA | hwT
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hwA
              have hjOp := (Finset.mem_filter.mp hj).2.2
              intro heq
              have hjeq : j = outIdx := by omega
              rw [hjeq, horOut] at hjOp
              cases hjOp
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hwT
              have hjNe := (Finset.mem_erase.mp hj).1
              omega
          rcases hDownUpper E.gates.length {E.output} w hwStop with h1 | ⟨k, hk, hopk, hkStop, hwk⟩
          · exfalso; exact hwNe (Finset.mem_singleton.mp h1)
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkStop, hopk⟩,
              List.mem_toFinset.mpr hwk⟩
        have hSrcCard : srcs.card = Aused.card + (T.card - 1) := by
          have hDisjImg : Disjoint (Aused.image (26 + ·)) ((T.erase outIdx).image (26 + ·)) := by
            rw [Finset.disjoint_left]
            intro w h1 h2
            obtain ⟨j1, hj1, rfl⟩ := Finset.mem_image.mp h1
            obtain ⟨j2, hj2, heq⟩ := Finset.mem_image.mp h2
            have hjeq : j1 = j2 := by omega
            subst hjeq
            exact Finset.disjoint_left.mp hATDisj hj1 (Finset.mem_of_mem_erase hj2)
          rw [Finset.card_union_of_disjoint hDisjImg,
            Finset.card_image_of_injective _ (fun x y h => by omega),
            Finset.card_image_of_injective _ (fun x y h => by omega),
            Finset.card_erase_of_mem houtT]
        have hBiCard : (T.biUnion (fun k => (gateAt E k).inputs.toFinset)).card ≤ 2 * T.card := by
          refine Finset.card_biUnion_le.trans ?_
          calc
            ∑ k ∈ T, (gateAt E k).inputs.toFinset.card
                ≤ ∑ k ∈ T, (gateAt E k).inputs.length := Finset.sum_le_sum (fun _ _ => List.toFinset_card_le _)
            _ = ∑ _ ∈ T, 2 := Finset.sum_congr rfl (fun k hk => hELen2 _ (by
                have hklt := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
                change E.gates.getD k ⟨GateOp.or, []⟩ ∈ E.gates
                rw [List.getD_eq_getElem _ _ hklt]
                exact List.getElem_mem hklt))
            _ = 2 * T.card := by simp [mul_comm]
        have hle := Finset.card_le_card hSub
        have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨outIdx, houtT⟩
        omega
    have hAdjSymm : ∀ u v : Fin 26, adj26 u v → adj26 v u := by
      rintro u v ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨p, l, hpl, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
    have hPairAdj : ∀ k ∈ Aused,
        ∀ i ∈ orReachSet (opnd E k 0), ∀ j ∈ orReachSet (opnd E k 1), adj26 i j := by
      intro k hk i hi j hj
      have hkLt : k < E.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hkStop : 26 + k ∈ Stop := (Finset.mem_filter.mp hk).2.1
      have hkAnd : (gateAt E k).op = GateOp.and := (Finset.mem_filter.mp hk).2.2
      have hkLen : (gateAt E k).inputs.length = 2 := hELen2 _ (by
        change E.gates.getD k ⟨GateOp.or, []⟩ ∈ E.gates; rw [List.getD_eq_getElem _ _ hkLt]; exact List.getElem_mem hkLt)
      obtain ⟨w0, w1, hkw⟩ := List.length_eq_two.mp hkLen
      have hop0 : opnd E k 0 = w0 := by rw [hOpndDef, hkw]; rfl
      have hop1 : opnd E k 1 = w1 := by rw [hOpndDef, hkw]; rfl
      rw [hop0] at hi; rw [hop1] at hj
      have hw0mem : w0 ∈ (gateAt E k).inputs := by rw [hkw]; simp
      have hw1mem : w1 ∈ (gateAt E k).inputs := by rw [hkw]; simp
      have hw0lt := hERB k hkLt w0 hw0mem
      have hw1lt := hERB k hkLt w1 hw1mem
      have hno0 := hNoAndOfAnd k hkLt hkAnd w0 hw0mem
      have hno1 := hNoAndOfAnd k hkLt hkAnd w1 hw1mem
      have hTrueAt : ∀ x : Fin 26 → Bool, x i = true → x j = true → E.eval (List.ofFn x) = true := by
        intro x hxi hxj
        have hv0 : (run E.gates (List.ofFn x)).getD w0 false = true :=
          (hOrReachSem w0 (by omega) hno0 x).mpr ⟨i, hi, hxi⟩
        have hv1 : (run E.gates (List.ofFn x)).getD w1 false = true :=
          (hOrReachSem w1 (by omega) hno1 x).mpr ⟨j, hj, hxj⟩
        have hvk : (run E.gates (List.ofFn x)).getD (26 + k) false = true := by
          rw [hEGateVal k hkLt x, hkAnd, hkw, hEvalAnd]
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          exact Bool.and_eq_true_iff.mpr ⟨hv0, hv1⟩
        obtain ⟨u, hu, hvu⟩ := hDownUp E.gates.length (le_refl _) {E.output} x ⟨26 + k, hkStop, hvk⟩
        rw [Finset.mem_singleton.mp hu] at hvu
        exact hvu
      have hPtFalse : ∀ p q : Fin 13, E.eval (incidenceInput ({p, q} : Finset (Fin 13)) (∅ : Finset (Fin 13))) = false := by
        intro p q
        apply hENeg {p, q} ∅
        refine ⟨fun l hl => by simp at hl, Or.inl ?_⟩
        obtain ⟨l, hpl, hql⟩ := hTwoOnLine p q
        exact ⟨l, fun r hr => by rcases Finset.mem_insert.mp hr with rfl | hr'; exact hpl; rw [Finset.mem_singleton.mp hr']; exact hql⟩
      have hLnFalse : ∀ l1 l2 : Fin 13, E.eval (incidenceInput (∅ : Finset (Fin 13)) ({l1, l2} : Finset (Fin 13))) = false := by
        intro l1 l2
        apply hENeg ∅ {l1, l2}
        refine ⟨fun l _ => Finset.disjoint_empty_right _, Or.inr ?_⟩
        obtain ⟨p, hp1, hp2⟩ := hTwoMeet l1 l2
        exact ⟨p, fun l hl => by rcases Finset.mem_insert.mp hl with rfl | hl'; exact hp1; rw [Finset.mem_singleton.mp hl']; exact hp2⟩
      have hNonIncFalse : ∀ p l : Fin 13, p ∉ S l → E.eval (incidenceInput {p} {l}) = false := by
        intro p l hni
        apply hENeg {p} {l}
        refine ⟨fun m hm => by
          rw [Finset.mem_singleton.mp hm]
          exact Finset.disjoint_singleton_right.mpr hni, Or.inl ?_⟩
        obtain ⟨m, hpm⟩ := hPtOnLine p
        exact ⟨m, fun q hq => (Finset.mem_singleton.mp hq).symm ▸ hpm⟩
      refine Fin.addCases (m := 13) (n := 13) (motive := fun u => i = u → adj26 u j) (fun p => ?_) (fun l => ?_) i rfl
      · intro rfl
        refine Fin.addCases (m := 13) (n := 13) (motive := fun v => j = v → adj26 (Fin.castAdd 13 p) v) (fun q => ?_) (fun l => ?_) j rfl
        · intro rfl
          exfalso
          let x : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13) (fun r => decide (r ∈ ({p, q} : Finset (Fin 13)))) (fun _ => false)
          have hrow : incidenceInput ({p, q} : Finset (Fin 13)) (∅ : Finset (Fin 13)) = List.ofFn x := by
            rw [hIncInDef, ← List.ofFn_fin_append]; congr 1
          have ht := hTrueAt x
            (by dsimp only [x]; rw [Fin.addCases_left]; simp)
            (by dsimp only [x]; rw [Fin.addCases_left]; simp)
          rw [← hrow, hPtFalse p q] at ht
          cases ht
        · intro rfl
          by_cases hpl : p ∈ S l
          · exact ⟨p, l, hpl, Or.inl ⟨rfl, rfl⟩⟩
          · exfalso
            let x : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13) (fun r => decide (r = p)) (fun m => decide (m = l))
            have hrow : incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x := by
              rw [hIncInDef, ← List.ofFn_fin_append]; congr 1
              funext u
              refine Fin.addCases (m := 13) (n := 13) (fun r => by simp [x, Fin.append]) (fun m => by simp [x, Fin.append]) u
            have ht := hTrueAt x
              (by dsimp only [x]; rw [Fin.addCases_left]; simp)
              (by dsimp only [x]; rw [Fin.addCases_right]; simp)
            rw [← hrow, hNonIncFalse p l hpl] at ht
            cases ht
      · intro rfl
        refine Fin.addCases (m := 13) (n := 13) (motive := fun v => j = v → adj26 (Fin.natAdd 13 l) v) (fun p => ?_) (fun l2 => ?_) j rfl
        · intro rfl
          by_cases hpl : p ∈ S l
          · exact ⟨p, l, hpl, Or.inr ⟨rfl, rfl⟩⟩
          · exfalso
            let x : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13) (fun r => decide (r = p)) (fun m => decide (m = l))
            have hrow : incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x := by
              rw [hIncInDef, ← List.ofFn_fin_append]; congr 1
              funext u
              refine Fin.addCases (m := 13) (n := 13) (fun r => by simp [x, Fin.append]) (fun m => by simp [x, Fin.append]) u
            have ht := hTrueAt x
              (by dsimp only [x]; rw [Fin.addCases_right]; simp)
              (by dsimp only [x]; rw [Fin.addCases_left]; simp)
            rw [← hrow, hNonIncFalse p l hpl] at ht
            cases ht
        · intro rfl
          exfalso
          let x : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13) (fun _ => false) (fun m => decide (m ∈ ({l, l2} : Finset (Fin 13))))
          have hrow : incidenceInput (∅ : Finset (Fin 13)) ({l, l2} : Finset (Fin 13)) = List.ofFn x := by
            rw [hIncInDef, ← List.ofFn_fin_append]; congr 1
          have ht := hTrueAt x
            (by dsimp only [x]; rw [Fin.addCases_right]; simp)
            (by dsimp only [x]; rw [Fin.addCases_right]; simp)
          rw [← hrow, hLnFalse l l2] at ht
          cases ht
    let Aact := Aused.filter fun k => (orReachSet (opnd E k 0)).Nonempty ∧ (orReachSet (opnd E k 1)).Nonempty
    have hAactCard : Aact.card ≤ Aused.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hSideCard1 : ∀ k ∈ Aact, (orReachSet (opnd E k 0)).card = 1 ∨ (orReachSet (opnd E k 1)).card = 1 := by
      intro k hk
      have hkU := (Finset.mem_filter.mp hk).1
      have hne0 := (Finset.mem_filter.mp hk).2.1
      have hne1 := (Finset.mem_filter.mp hk).2.2
      by_contra! hboth
      have h10 : 1 < (orReachSet (opnd E k 0)).card := by have := Finset.card_pos.mpr hne0; omega
      have h11 : 1 < (orReachSet (opnd E k 1)).card := by have := Finset.card_pos.mpr hne1; omega
      obtain ⟨c1, hc1, c2, hc2, hneC⟩ := Finset.one_lt_card.mp h10
      obtain ⟨i1, hi1, i2, hi2, hneI⟩ := Finset.one_lt_card.mp h11
      exact hNoC4 c1 c2 i1 i2 hneC hneI
        ⟨hPairAdj k hkU c1 hc1 i1 hi1, hPairAdj k hkU c1 hc1 i2 hi2,
          hPairAdj k hkU c2 hc2 i1 hi1, hPairAdj k hkU c2 hc2 i2 hi2⟩
    let center (k : ℕ) : Fin 26 :=
      if h0 : (orReachSet (opnd E k 0)).card = 1 then (orReachSet (opnd E k 0)).min' (Finset.card_pos.mp (by omega))
      else if h1 : (orReachSet (opnd E k 1)).card = 1 then (orReachSet (opnd E k 1)).min' (Finset.card_pos.mp (by omega))
      else 0
    let leafWire (k : ℕ) : ℕ :=
      if (orReachSet (opnd E k 0)).card = 1 then opnd E k 1 else opnd E k 0
    have hCenterSpec : ∀ k ∈ Aact,
        (orReachSet (if (orReachSet (opnd E k 0)).card = 1 then opnd E k 0 else opnd E k 1) = {center k}) ∧
        (orReachSet (leafWire k)).Nonempty ∧
        (∀ i ∈ orReachSet (leafWire k), adj26 (center k) i) ∧
        (∃ w ∈ (gateAt E k).inputs, leafWire k = w) := by
      intro k hk
      have hkU := (Finset.mem_filter.mp hk).1
      have hkLt : k < E.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hkU).1
      have hkLen : (gateAt E k).inputs.length = 2 := hELen2 _ (by
        change E.gates.getD k ⟨GateOp.or, []⟩ ∈ E.gates; rw [List.getD_eq_getElem _ _ hkLt]; exact List.getElem_mem hkLt)
      obtain ⟨w0, w1, hkw⟩ := List.length_eq_two.mp hkLen
      have hop0 : opnd E k 0 = w0 := by rw [hOpndDef, hkw]; rfl
      have hop1 : opnd E k 1 = w1 := by rw [hOpndDef, hkw]; rfl
      have hne0 := (Finset.mem_filter.mp hk).2.1
      have hne1 := (Finset.mem_filter.mp hk).2.2
      by_cases h0 : (orReachSet (opnd E k 0)).card = 1
      · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h0
        have hmin : center k = c := by
          dsimp only [center]
          split_ifs
          have hm : (orReachSet (opnd E k 0)).min' (Finset.card_pos.mp (by omega)) ∈ ({c} : Finset (Fin 26)) := by
            rw [← hc]; exact Finset.min'_mem _ _
          exact Finset.mem_singleton.mp hm
        rw [hmin]
        refine ⟨by simp [hc], ?_, ?_, ⟨w1, by rw [hkw]; simp, by simp [leafWire, h0, hop1]⟩⟩
        · simp [leafWire, h0, hne1]
        · intro i hi
          simp only [leafWire, ite_eq_left h0] at hi
          exact hPairAdj k hkU c (by rw [hc]; exact Finset.mem_singleton_self c) i hi
      · have h1 : (orReachSet (opnd E k 1)).card = 1 := (hSideCard1 k hk).resolve_left h0
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1
        have hmin : center k = c := by
          dsimp only [center]
          split_ifs
          have hm : (orReachSet (opnd E k 1)).min' (Finset.card_pos.mp (by omega)) ∈ ({c} : Finset (Fin 26)) := by
            rw [← hc]; exact Finset.min'_mem _ _
          exact Finset.mem_singleton.mp hm
        rw [hmin]
        refine ⟨by rw [ite_eq_right h0]; exact hc, ?_, ?_, ⟨w0, by rw [hkw]; simp, by dsimp only [leafWire]; rw [ite_eq_right h0, hop0]⟩⟩
        · simp [leafWire, h0, hne0]
        · intro i hi
          simp only [leafWire, ite_eq_right h0] at hi
          exact hAdjSymm i c (hPairAdj k hkU i hi c (by rw [hc]; exact Finset.mem_singleton_self c))
    let B (c : Fin 26) : Finset ℕ :=
      (Finset.range E.gates.length).filter fun j =>
        (gateAt E j).op = GateOp.or ∧ 2 ≤ (orReachSet (26 + j)).card ∧ ∀ i ∈ orReachSet (26 + j), adj26 c i
    have hBDisj : ∀ c1 c2 : Fin 26, c1 ≠ c2 → Disjoint (B c1) (B c2) := by
      intro c1 c2 hne
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have h1 := (Finset.mem_filter.mp hj1).2
      have h2 := (Finset.mem_filter.mp hj2).2
      have hlt : 1 < (orReachSet (26 + j)).card := by omega
      obtain ⟨i1, hi1, i2, hi2, hneI⟩ := Finset.one_lt_card.mp hlt
      exact hNoC4 c1 c2 i1 i2 hne hneI ⟨h1.2.2 i1 hi1, h1.2.2 i2 hi2, h2.2.2 i1 hi1, h2.2.2 i2 hi2⟩
    have hBDisjA : ∀ c : Fin 26, Disjoint (B c) Aused := by
      intro c
      rw [Finset.disjoint_left]
      intro j hjB hjA
      have h1 := (Finset.mem_filter.mp hjB).2.1
      have h2 := (Finset.mem_filter.mp hjA).2.2
      rw [h1] at h2
      cases h2
    have hStopEmpty : ∀ w ∈ Stop, orReachSet w = ∅ := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        obtain ⟨hw26, hwlt⟩ := hStopBound w hw
        have hk : w - 26 < E.gates.length := by omega
        have heq : 26 + (w - 26) = w := by omega
        rcases hOpCases (w - 26) hk with hand | hor
        · rw [← heq, hORGate (w - 26) hk, ite_eq_right (by rw [hand]; exact GateOp.noConfusion)]
        · rw [← heq, hORGate (w - 26) hk, ite_eq_left hor]
          have hsub : (gateAt E (w - 26)).inputs.toFinset ⊆ Stop :=
            hDownClosed E.gates.length (le_refl _) {E.output} (w - 26) hk hor (by rw [heq]; exact hw)
          have hzero : ∀ l : List ℕ, (∀ u ∈ l, u < w ∧ u ∈ Stop) →
              (l.map orReachSet).foldr (· ∪ ·) ∅ = ∅ := by
            intro l hl
            induction l with
            | nil => rfl
            | cons u t iht =>
              have hu := hl u List.mem_cons_self
              have h1 := ih u hu.1 hu.2
              have h2 := iht (fun v hv => hl v (List.mem_cons_of_mem _ hv))
              change orReachSet u ∪ (t.map orReachSet).foldr (· ∪ ·) ∅ = ∅
              rw [h1, h2, Finset.union_empty]
          exact hzero _ (fun u hu => ⟨by have := hERB (w - 26) hk u hu; omega, hsub (List.mem_toFinset.mpr hu)⟩)
    have hBDisjT : ∀ c : Fin 26, Disjoint (B c) T := by
      intro c
      rw [Finset.disjoint_left]
      intro j hjB hjT
      have h1 := (Finset.mem_filter.mp hjB).2.2.1
      have h2 := hStopEmpty (26 + j) (Finset.mem_filter.mp hjT).2.1
      rw [h2] at h1
      simp at h1
    let Ac (c : Fin 26) : Finset ℕ := Aact.filter fun k => center k = c
    let Uc (c : Fin 26) : Finset (Fin 26) := (Ac c).biUnion fun k => orReachSet (leafWire k)
    have hLeafBound : ∀ c : Fin 26, (Uc c).card ≤ (Ac c).card + (B c).card := by
      intro c
      let Sc := downClosure E.gates.length ((Ac c).image leafWire)
      let Bc' := (B c).filter fun j => 26 + j ∈ Sc
      have hScProp : ∀ m, m ≤ E.gates.length → ∀ w ∈ downClosure m ((Ac c).image leafWire),
          w < 26 + E.gates.length ∧ noAndBelow w ∧ ∀ i ∈ orReachSet w, adj26 c i := by
        intro m
        induction m with
        | zero =>
          intro _ w hw
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
          have hkAct := (Finset.mem_filter.mp hk).1
          have hkC := (Finset.mem_filter.mp hk).2
          have hkU := (Finset.mem_filter.mp hkAct).1
          have hkLt : k < E.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hkU).1
          have hkAnd : (gateAt E k).op = GateOp.and := (Finset.mem_filter.mp hkU).2.2
          obtain ⟨_, _, hadj, w0, hw0mem, hw0eq⟩ := hCenterSpec k hkAct
          rw [hw0eq]
          have hw0lt := hERB k hkLt w0 hw0mem
          refine ⟨by omega, hNoAndOfAnd k hkLt hkAnd w0 hw0mem, ?_⟩
          intro i hi
          rw [← hkC]
          exact hadj i (hw0eq ▸ hi)
        | succ m ih =>
          intro hm w hw
          rw [hDCSucc] at hw
          have hStepProp : ∀ u ∈ downStep m ((Ac c).image leafWire),
              u < 26 + E.gates.length ∧ noAndBelow u ∧ ∀ i ∈ orReachSet u, adj26 c i := by
            intro u hu
            dsimp only [downStep] at hu
            split_ifs at hu with hcond
            · rcases Finset.mem_union.mp hu with h1 | h2
              · exact ih (Nat.le_of_lt hm) u (hDownSub m _ h1)
              · obtain ⟨hmLt, hmNo, hmAdj⟩ := ih (Nat.le_of_lt hm) (26 + m) (hDownSub m _ hcond.2)
                have humem : u ∈ (gateAt E m).inputs := List.mem_toFinset.mp h2
                have hult := hERB m hm u humem
                refine ⟨by omega, hNoAndStep m hm hmNo u humem, fun i hi => hmAdj i ?_⟩
                rw [hORGate m hm, ite_eq_left hcond.1]
                have hfold : ∀ (l : List (Finset (Fin 26))) (s : Finset (Fin 26)),
                    s ∈ l → s ⊆ l.foldr (· ∪ ·) ∅ := by
                  intro l s hs
                  induction l with
                  | nil => simp at hs
                  | cons a t iht =>
                    rcases List.mem_cons.mp hs with rfl | ht
                    · exact Finset.subset_union_left
                    · exact (iht ht).trans Finset.subset_union_right
                exact hfold _ _ (List.mem_map.mpr ⟨u, humem, rfl⟩) hi
            · exact ih (Nat.le_of_lt hm) u (hDownSub m _ hu)
          have hInd : ∀ (l : List ℕ) (S0 : Finset ℕ),
              (∀ u ∈ S0, u < 26 + E.gates.length ∧ noAndBelow u ∧ ∀ i ∈ orReachSet u, adj26 c i) →
              (∀ k ∈ l, k < E.gates.length) →
              ∀ w ∈ l.foldr downStep S0, w < 26 + E.gates.length ∧ noAndBelow w ∧ ∀ i ∈ orReachSet w, adj26 c i := by
            intro l
            induction l using List.reverseRecOn with
            | nil => intro S0 hS0 _; exact hS0
            | append_singleton l k ihl =>
              intro S0 hS0 hkl w hw
              rw [List.foldr_append, List.foldr_cons, List.foldr_nil] at hw
              apply ihl _ _ (fun r hr => hkl r (by simp [hr])) w hw
              intro u hu
              dsimp only [downStep] at hu
              split_ifs at hu with hcond
              · rcases Finset.mem_union.mp hu with h1 | h2
                · exact hS0 u h1
                · have hkLt : k < E.gates.length := hkl k (by simp)
                  obtain ⟨_, hkNo, hkAdj⟩ := hS0 (26 + k) hcond.2
                  have humem : u ∈ (gateAt E k).inputs := List.mem_toFinset.mp h2
                  have hult := hERB k hkLt u humem
                  refine ⟨by omega, hNoAndStep k hkLt hkNo u humem, fun i hi => hkAdj i ?_⟩
                  rw [hORGate k hkLt, ite_eq_left hcond.1]
                  have hfold : ∀ (ls : List (Finset (Fin 26))) (s : Finset (Fin 26)),
                      s ∈ ls → s ⊆ ls.foldr (· ∪ ·) ∅ := by
                    intro ls s hs
                    induction ls with
                    | nil => simp at hs
                    | cons a t iht =>
                      rcases List.mem_cons.mp hs with rfl | ht
                      · exact Finset.subset_union_left
                      · exact (iht ht).trans Finset.subset_union_right
                  exact hfold _ _ (List.mem_map.mpr ⟨u, humem, rfl⟩) hi
              · exact hS0 u hu
          have hw' : w ∈ (List.range m).foldr downStep (downStep m ((Ac c).image leafWire)) := hw
          exact hInd (List.range m) (downStep m ((Ac c).image leafWire)) hStepProp
            (fun r hr => by have := List.mem_range.mp hr; omega) w hw'
      have hBc'Mem : ∀ j, 26 + j ∈ Sc → j ∈ Bc' := by
        intro j hjSc
        obtain ⟨hjLt, hjNo, hjAdj⟩ := hScProp E.gates.length (le_refl _) (26 + j) hjSc
        have hjLt' : j < E.gates.length := by omega
        have hjOp : (gateAt E j).op = GateOp.or := hjNo.1 j hjLt' rfl
        have hjCard : 2 ≤ (orReachSet (26 + j)).card := hOrReachGe2 j hjLt' hjNo
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjLt', hjOp, hjCard, hjAdj⟩, hjSc⟩
      have hUcSubSc : (Uc c).image Fin.val ⊆ Sc := by
        have hReachSub : ∀ w, w ∈ Sc → ∀ i ∈ orReachSet w, i.val ∈ Sc := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hwSc i hi
            obtain ⟨hwLt, hwNo, _⟩ := hScProp E.gates.length (le_refl _) w hwSc
            by_cases hw26 : w < 26
            · let u0 : Fin 26 := ⟨w, hw26⟩
              have h1 : orReachSet w = {u0} := hORInput u0
              rw [h1] at hi
              rw [Finset.mem_singleton.mp hi]
              exact hwSc
            · have hk : w - 26 < E.gates.length := by omega
              have heq : 26 + (w - 26) = w := by omega
              have hop : (gateAt E (w - 26)).op = GateOp.or := hwNo.1 (w - 26) hk heq.symm
              rw [← heq, hORGate (w - 26) hk, ite_eq_left hop] at hi
              have hfold : ∀ (l : List (Finset (Fin 26))), i ∈ l.foldr (· ∪ ·) ∅ → ∃ s ∈ l, i ∈ s := by
                intro l hl
                induction l with
                | nil => simp at hl
                | cons a t iht =>
                  rcases Finset.mem_union.mp hl with ha | ht
                  · exact ⟨a, List.mem_cons_self, ha⟩
                  · obtain ⟨s, hs, his⟩ := iht ht
                    exact ⟨s, List.mem_cons_of_mem _ hs, his⟩
              obtain ⟨s, hs, his⟩ := hfold _ hi
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
              have hult := hERB (w - 26) hk u hu
              have huSc : u ∈ Sc := hDownClosed E.gates.length (le_refl _) ((Ac c).image leafWire) (w - 26) hk hop (by rw [heq]; exact hwSc) (List.mem_toFinset.mpr hu)
              exact ih u (by omega) huSc i his
        intro n hn
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
        obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
        exact hReachSub (leafWire k) (hDownSub E.gates.length _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)) i hik
      have hScUpper : Sc ⊆ (Ac c).image leafWire ∪ Bc'.biUnion (fun j => (gateAt E j).inputs.toFinset) := by
        intro w hw
        rcases hDownUpper E.gates.length ((Ac c).image leafWire) w hw with h1 | ⟨k, hk, hopk, hkSc, hwk⟩
        · exact Finset.mem_union_left _ h1
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hBc'Mem k hkSc, List.mem_toFinset.mpr hwk⟩)
      have hDisjSub : Disjoint ((Uc c).image Fin.val) (Bc'.image (26 + ·)) := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨j, _, heq⟩ := Finset.mem_image.mp h2
        omega
      have hBothSub : (Uc c).image Fin.val ∪ Bc'.image (26 + ·) ⊆ Sc := by
        apply Finset.union_subset hUcSubSc
        intro w hw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hj).2
      have hCard1 : (Uc c).card + Bc'.card ≤ Sc.card := by
        have h := Finset.card_le_card hBothSub
        rw [Finset.card_union_of_disjoint hDisjSub,
          Finset.card_image_of_injective _ Fin.val_injective,
          Finset.card_image_of_injective _ (fun x y h => by omega)] at h
        exact h
      have hCard2 : Sc.card ≤ (Ac c).card + 2 * Bc'.card := by
        have h := Finset.card_le_card hScUpper
        refine h.trans (Finset.card_union_le _ _ |>.trans ?_)
        have h1 : ((Ac c).image leafWire).card ≤ (Ac c).card := Finset.card_image_le
        have h2 : (Bc'.biUnion fun j => (gateAt E j).inputs.toFinset).card ≤ 2 * Bc'.card := by
          refine Finset.card_biUnion_le.trans ?_
          calc
            ∑ j ∈ Bc', (gateAt E j).inputs.toFinset.card
                ≤ ∑ j ∈ Bc', (gateAt E j).inputs.length := Finset.sum_le_sum (fun _ _ => List.toFinset_card_le _)
            _ = ∑ _ ∈ Bc', 2 := Finset.sum_congr rfl (fun j hj => hELen2 _ (by
                have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
                change E.gates.getD j ⟨GateOp.or, []⟩ ∈ E.gates
                rw [List.getD_eq_getElem _ _ hjlt]
                exact List.getElem_mem hjlt))
            _ = 2 * Bc'.card := by simp [mul_comm]
        omega
      have hBc'Le : Bc'.card ≤ (B c).card := Finset.card_le_card (Finset.filter_subset _ _)
      omega
    have hEdgesCovered : 52 ≤ ∑ c : Fin 26, (Uc c).card := by
      let f (e : Fin 13 × Fin 13) : Σ _ : Fin 26, Fin 26 :=
        if _ : Fin.natAdd 13 e.2 ∈ Uc (Fin.castAdd 13 e.1) then ⟨Fin.castAdd 13 e.1, Fin.natAdd 13 e.2⟩
        else ⟨Fin.natAdd 13 e.2, Fin.castAdd 13 e.1⟩
      have hfMem : ∀ e ∈ incidences S, f e ∈ (Finset.univ : Finset (Fin 26)).sigma Uc := by
        intro e hpl
        rcases e with ⟨p, l⟩
        have hpSl : p ∈ S l := (Finset.mem_filter.mp hpl).2
        have hpos := hEPos l p hpSl
        let x : Fin 26 → Bool := Fin.addCases (m := 13) (n := 13) (fun q => decide (q = p)) (fun m => decide (m = l))
        have hrow : incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = List.ofFn x := by
          rw [hIncInDef]
          rw [← List.ofFn_fin_append]
          congr 1
          funext u
          refine Fin.addCases (m := 13) (n := 13) (fun q => by simp [x, Fin.append])
            (fun m => by simp [x, Fin.append]) u
        rw [hrow] at hpos
        change (run E.gates (List.ofFn x)).getD E.output false = true at hpos
        have hOutMem : E.output ∈ Stop := hDownSub E.gates.length {E.output} (Finset.mem_singleton_self _)
        obtain ⟨w, hwStop, hwCond, hvw⟩ := hDownEval {E.output} x ⟨E.output, hOutMem, hEOutBound.2, hpos⟩
        have hw26 := (hStopBound w hwStop).1
        rcases hwCond with hlt | ⟨_, hwlt, hand⟩
        · exfalso; omega
        · let k := w - 26
          have hkA : k ∈ Aused := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by
            have : 26 + k = w := by omega
            rwa [this], hand⟩
          have hkLt : k < E.gates.length := by omega
          have hkLen : (gateAt E k).inputs.length = 2 := hELen2 _ (by
            change E.gates.getD k ⟨GateOp.or, []⟩ ∈ E.gates; rw [List.getD_eq_getElem _ _ hkLt]; exact List.getElem_mem hkLt)
          obtain ⟨w0, w1, hkw⟩ := List.length_eq_two.mp hkLen
          have hop0 : opnd E k 0 = w0 := by rw [hOpndDef, hkw]; rfl
          have hop1 : opnd E k 1 = w1 := by rw [hOpndDef, hkw]; rfl
          have hw0mem : w0 ∈ (gateAt E k).inputs := by rw [hkw]; simp
          have hw1mem : w1 ∈ (gateAt E k).inputs := by rw [hkw]; simp
          have hw0lt := hERB k hkLt w0 hw0mem
          have hw1lt := hERB k hkLt w1 hw1mem
          have hno0 := hNoAndOfAnd k hkLt hand w0 hw0mem
          have hno1 := hNoAndOfAnd k hkLt hand w1 hw1mem
          have hvk : (run E.gates (List.ofFn x)).getD (26 + k) false = true := by
            have : 26 + k = w := by omega
            rwa [this]
          rw [hEGateVal k hkLt x, hand, hkw, hEvalAnd] at hvk
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, Bool.and_eq_true] at hvk
          obtain ⟨i0, hi0, hxi0⟩ := (hOrReachSem w0 (by omega) hno0 x).mp hvk.1
          obtain ⟨i1, hi1, hxi1⟩ := (hOrReachSem w1 (by omega) hno1 x).mp hvk.2
          have hkAct : k ∈ Aact := Finset.mem_filter.mpr ⟨hkA, ⟨i0, hop0.symm ▸ hi0⟩, ⟨i1, hop1.symm ▸ hi1⟩⟩
          have hxMem : ∀ u : Fin 26, x u = true → u = Fin.castAdd 13 p ∨ u = Fin.natAdd 13 l := by
            intro u hu
            have hu26 : u.val < 26 := u.isLt
            by_cases h13 : u.val < 13
            · have huc : u = Fin.castAdd 13 ⟨u.val, h13⟩ := Fin.ext rfl
              rw [huc] at hu ⊢
              simp only [x, Fin.addCases_left, decide_eq_true_eq] at hu
              exact Or.inl (by rw [hu])
            · have hun : u = Fin.natAdd 13 (⟨u.val - 13, by omega⟩ : Fin 13) :=
                Fin.ext (by show u.val = 13 + (u.val - 13); omega)
              rw [hun] at hu ⊢
              simp only [x, Fin.addCases_right, decide_eq_true_eq] at hu
              exact Or.inr (by rw [hu])
          have hi0' := hxMem i0 hxi0
          have hi1' := hxMem i1 hxi1
          have hAdj01 := hPairAdj k hkA i0 (hop0.symm ▸ hi0) i1 (hop1.symm ▸ hi1)
          have hNotSameP : i0 ≠ i1 := by
            rintro rfl
            rcases hAdj01 with ⟨p', l', _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
            · have := congrArg Fin.val (h1.symm.trans h2); simp at this; omega
            · have := congrArg Fin.val (h1.symm.trans h2); simp at this; omega
          obtain ⟨hCenterEq, _, _, _⟩ := hCenterSpec k hkAct
          have hEither : Fin.natAdd 13 l ∈ Uc (Fin.castAdd 13 p) ∨ Fin.castAdd 13 p ∈ Uc (Fin.natAdd 13 l) := by
            by_cases h0 : (orReachSet (opnd E k 0)).card = 1
            · rw [ite_eq_left h0] at hCenterEq
              have hc : i0 = center k := by
                have hi0c : i0 ∈ ({center k} : Finset (Fin 26)) := hCenterEq ▸ (hop0.symm ▸ hi0)
                exact Finset.mem_singleton.mp hi0c
              have hl : leafWire k = opnd E k 1 := by simp [leafWire, h0]
              have hkAc : k ∈ Ac (center k) := Finset.mem_filter.mpr ⟨hkAct, rfl⟩
              have hi1Uc : i1 ∈ Uc (center k) := Finset.mem_biUnion.mpr ⟨k, hkAc, by rw [hl, hop1]; exact hi1⟩
              rcases hi0' with rfl | rfl <;> rcases hi1' with rfl | rfl
              · exact absurd rfl hNotSameP
              · exact Or.inl (by rw [hc]; exact hi1Uc)
              · exact Or.inr (by rw [hc]; exact hi1Uc)
              · exact absurd rfl hNotSameP
            · rw [ite_eq_right h0] at hCenterEq
              have hc : i1 = center k := by
                have hi1c : i1 ∈ ({center k} : Finset (Fin 26)) := hCenterEq ▸ (hop1.symm ▸ hi1)
                exact Finset.mem_singleton.mp hi1c
              have hl : leafWire k = opnd E k 0 := by simp [leafWire, h0]
              have hkAc : k ∈ Ac (center k) := Finset.mem_filter.mpr ⟨hkAct, rfl⟩
              have hi0Uc : i0 ∈ Uc (center k) := Finset.mem_biUnion.mpr ⟨k, hkAc, by rw [hl, hop0]; exact hi0⟩
              rcases hi0' with rfl | rfl <;> rcases hi1' with rfl | rfl
              · exact absurd rfl hNotSameP
              · exact Or.inr (by rw [hc]; exact hi0Uc)
              · exact Or.inl (by rw [hc]; exact hi0Uc)
              · exact absurd rfl hNotSameP
          dsimp only [f]
          split_ifs with hcond
          · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hcond⟩
          · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hEither.resolve_left hcond⟩
      have hfInj : ∀ e1 ∈ incidences S, ∀ e2 ∈ incidences S, f e1 = f e2 → e1 = e2 := by
        intro e1 _ e2 _ heq
        rcases e1 with ⟨p1, l1⟩
        rcases e2 with ⟨p2, l2⟩
        dsimp only [f] at heq
        split_ifs at heq with h1 h2 h2
        · have hf := congrArg Sigma.fst heq
          have hs := congrArg Sigma.snd heq
          dsimp at hf hs
          have hp : p1 = p2 := Fin.ext (by have := congrArg Fin.val hf; simpa using this)
          have hl : l1 = l2 := Fin.ext (by have := congrArg Fin.val hs; simp at this; omega)
          exact Prod.ext hp hl
        · have hf := congrArg Sigma.fst heq
          dsimp at hf
          have := congrArg Fin.val hf; simp at this; omega
        · have hf := congrArg Sigma.fst heq
          dsimp at hf
          have := congrArg Fin.val hf; simp at this; omega
        · have hf := congrArg Sigma.fst heq
          have hs := congrArg Sigma.snd heq
          dsimp at hf hs
          have hl : l1 = l2 := Fin.ext (by have := congrArg Fin.val hf; simp at this; omega)
          have hp : p1 = p2 := Fin.ext (by have := congrArg Fin.val hs; simpa using this)
          exact Prod.ext hp hl
      have hCard := Finset.card_le_card_of_injOn f (fun e he => Finset.mem_coe.mpr (hfMem e he))
        (fun e1 he1 e2 he2 heq => hfInj e1 he1 e2 he2 heq)
      rw [Finset.card_sigma, hIncidCard] at hCard
      simpa using hCard
    have hUcLe4Ac : ∀ c : Fin 26, (Uc c).card ≤ 4 * (Ac c).card := by
      intro c
      calc
        (Uc c).card ≤ ∑ k ∈ Ac c, (orReachSet (leafWire k)).card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ Ac c, 4 := Finset.sum_le_sum (fun k hk => by
          have hkAct := (Finset.mem_filter.mp hk).1
          have hkC := (Finset.mem_filter.mp hk).2
          obtain ⟨_, _, hadj, _⟩ := hCenterSpec k hkAct
          rw [← hDeg4 c]
          exact Finset.card_le_card (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkC ▸ hadj i hi⟩))
        _ = 4 * (Ac c).card := by simp [mul_comm]
    have hSumAc : ∑ c : Fin 26, (Ac c).card = Aact.card := by
      have hPart : (Finset.univ : Finset (Fin 26)).biUnion Ac = Aact := by
        ext k
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Ac, Finset.mem_filter]
        exact ⟨fun h => by obtain ⟨c, h1, _⟩ := h; exact h1, fun h => ⟨center k, h, rfl⟩⟩
      have hDisj : ∀ c1 c2 : Fin 26, c1 ≠ c2 → Disjoint (Ac c1) (Ac c2) := by
        intro c1 c2 hne
        rw [Finset.disjoint_left]
        intro k h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [← hPart, Finset.card_biUnion (fun c1 _ c2 _ hne => hDisj c1 c2 hne)]
    have hAactGe13 : 13 ≤ Aact.card := by
      have h1 : 52 ≤ ∑ c : Fin 26, 4 * (Ac c).card :=
        hEdgesCovered.trans (Finset.sum_le_sum fun c _ => hUcLe4Ac c)
      rw [← Finset.mul_sum, hSumAc] at h1
      omega
    have hSumB : ∑ c : Fin 26, (B c).card = ((Finset.univ : Finset (Fin 26)).biUnion B).card := by
      rw [Finset.card_biUnion (fun c1 _ c2 _ hne => hBDisj c1 c2 hne)]
    have hAllSub : Aused ∪ T ∪ (Finset.univ : Finset (Fin 26)).biUnion B ⊆ Finset.range E.gates.length := by
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _
      · exact Finset.biUnion_subset.mpr (fun c _ => Finset.filter_subset _ _)
    have hDisjAT_B : Disjoint (Aused ∪ T) ((Finset.univ : Finset (Fin 26)).biUnion B) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      obtain ⟨c, _, hjB⟩ := Finset.mem_biUnion.mp hj2
      rcases Finset.mem_union.mp hj1 with hjA | hjT
      · exact Finset.disjoint_left.mp (hBDisjA c) hjB hjA
      · exact Finset.disjoint_left.mp (hBDisjT c) hjB hjT
    have hTotalGates : Aused.card + T.card + ∑ c : Fin 26, (B c).card ≤ E.size := by
      have h1 := Finset.card_le_card hAllSub
      rw [Finset.card_union_of_disjoint hDisjAT_B, Finset.card_union_of_disjoint hATDisj,
        ← hSumB, Finset.card_range] at h1
      exact h1
    have hSumLeaf : ∑ c : Fin 26, (Uc c).card ≤ Aact.card + ∑ c : Fin 26, (B c).card := by
      have h1 : ∑ c : Fin 26, (Uc c).card ≤ ∑ c : Fin 26, ((Ac c).card + (B c).card) :=
        Finset.sum_le_sum (fun c _ => hLeafBound c)
      rw [Finset.sum_add_distrib, hSumAc] at h1
      exact h1
    omega
  by_cases hZero : andPairs 26 E = 0
  · have h64 := hAndNotZero hZero
    omega
  · by_cases hOne : andPairs 26 E = 1
    · have h64 := oneAndPair E hEgood hEmin hOne
      omega
    · have hTwo : 2 ≤ andPairs 26 E := by omega
      have h64 := manyAndPairs E hEgood hEmin hTwo
      omega


