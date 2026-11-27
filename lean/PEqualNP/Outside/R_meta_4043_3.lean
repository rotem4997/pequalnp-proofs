import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4043_3
    (twoLevel : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x1 (x3 - x4) = Bool.true → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x1 (x6 - x5) = Bool.true}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x1 (x7 - x6) = Bool.false)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → x2 x3 → (¬∃ (x7 : ℕ) (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x7 x8) → (64 : ℕ) ≤ x3.size)
    (nested : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (∃ (x8 : ℕ) (x9 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x8 x9) → (58 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  intro C v hmono hspec
  by_cases hnest : ∃ (i : ℕ) (j : ℕ), (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j
  · exact nested C v hmono hspec hnest

  obtain ⟨m, hm⟩ : ∃ m, C.gates.length = m := ⟨_, rfl⟩

  obtain ⟨n0, n1, n2, n3, hstar⟩ : ∃ n0 n1 n2 n3 : Fin 26, ∀ y : Fin 26 → Bool,
      ((y n0 || y n1 || y n2 || y n3) && y v) = true ↔ ∃ a b : Fin 13,
        (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) ∧ y (Fin.castAdd 13 a) = true ∧
          y (Fin.natAdd 13 b) = true ∧ (v = Fin.castAdd 13 a ∨ v = Fin.natAdd 13 b) := by
    have hcn : ∀ a b : Fin 13, Fin.castAdd 13 a ≠ Fin.natAdd 13 b := by decide
    have hv : (∃ p : Fin 13, v = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, v = Fin.natAdd 13 l :=
      if h : v.1 < 13 then Or.inl ⟨⟨v.1, h⟩, Fin.ext rfl⟩
      else Or.inr ⟨⟨v.1 - 13, by omega⟩, Fin.ext (by simp; omega)⟩
    rcases hv with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · have hinc : ∀ a b : Fin 13, (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) ↔
          (b = a ∨ b = a - 1 ∨ b = a - 3 ∨ b = a - 9) := by decide
      refine ⟨Fin.natAdd 13 p, Fin.natAdd 13 (p - 1), Fin.natAdd 13 (p - 3), Fin.natAdd 13 (p - 9),
        fun y => ⟨fun h => ?_, ?_⟩⟩
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        obtain ⟨((h | h) | h) | h, hp⟩ := h <;>
          exact ⟨p, _, (hinc _ _).2 (by simp), hp, h, Or.inl rfl⟩
      · rintro ⟨a, b, hab, ha, hb, h | h⟩
        · obtain rfl := Fin.castAdd_inj.1 h
          rcases (hinc _ _).1 hab with rfl | rfl | rfl | rfl <;>
            simp only [ha, hb, Bool.or_true, Bool.true_or, Bool.and_true]
        · exact absurd h (hcn p b)
    · refine ⟨Fin.castAdd 13 l, Fin.castAdd 13 (l + 1), Fin.castAdd 13 (l + 3), Fin.castAdd 13 (l + 9),
        fun y => ⟨fun h => ?_, ?_⟩⟩
      · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        obtain ⟨((h | h) | h) | h, hl⟩ := h <;>
          exact ⟨_, l, by simp, h, hl, Or.inr rfl⟩
      · rintro ⟨a, b, hab, ha, hb, h | h⟩
        · exact absurd h.symm (hcn a l)
        · obtain rfl := (Fin.natAdd_inj 13).1 h
          rcases hab with rfl | rfl | rfl | rfl <;>
            simp only [ha, hb, Bool.or_true, Bool.true_or, Bool.and_true]

  let f : ℕ → ℕ → ℕ := fun k w =>
    if w = v.1 then 26 else if w < 26 then w else if w < 26 + k then w + 1 else 26
  have hfle : ∀ k w, f k w ≤ 26 + k := by intro k w; simp only [f]; split_ifs <;> omega
  let G : List Gate := C.gates.mapIdx fun k g => ⟨g.op, g.inputs.map (f k)⟩
  let star : List Gate := [⟨GateOp.or, [n0.1, n1.1]⟩, ⟨GateOp.or, [26 + (m + 1), n2.1]⟩,
    ⟨GateOp.or, [26 + (m + 2), n3.1]⟩, ⟨GateOp.and, [26 + (m + 3), v.1]⟩,
    ⟨GateOp.or, [f m C.output, 26 + (m + 4)]⟩]
  let D : Circuit := ⟨⟨GateOp.or, []⟩ :: (G ++ star), 26 + (m + 5)⟩
  have hG : G.length = m := by simp only [G, List.length_mapIdx, hm]
  have hDlen : D.gates.length = m + 6 := by simp [D, hG, star]
  have hg0 : gateAt D 0 = ⟨GateOp.or, []⟩ := rfl
  have hgk : ∀ k < m, gateAt D (k + 1) = ⟨(gateAt C k).op, (gateAt C k).inputs.map (f k)⟩ := by
    intro k hk
    have hk' : k < G.length := by omega
    have hCk : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ (by omega)
    show List.getD (⟨GateOp.or, []⟩ :: (G ++ star)) (k + 1) ⟨GateOp.or, []⟩ = _
    rw [List.getD_cons_succ, List.getD_append _ _ _ _ hk', List.getD_eq_getElem _ _ hk', hCk]
    simp only [G, List.getElem_mapIdx]
  have hgs : ∀ t, gateAt D (m + 1 + t) = star.getD t ⟨GateOp.or, []⟩ := by
    intro t
    show List.getD (⟨GateOp.or, []⟩ :: (G ++ star)) (m + 1 + t) ⟨GateOp.or, []⟩ = _
    rw [show m + 1 + t = m + t + 1 by omega, List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by omega), hG, Nat.add_sub_cancel_left]
  have hsplit : ∀ j, j = 0 ∨ (∃ k < m, j = k + 1) ∨ ∃ t, j = m + 1 + t := by
    intro j
    rcases j with _ | k
    · exact Or.inl rfl
    · exact if hk : k < m then Or.inr (Or.inl ⟨k, hk, rfl⟩) else Or.inr (Or.inr ⟨k - m, by omega⟩)
  have hmonoD : Monotone2 D := by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨Or.inr rfl, by simp⟩
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.1 hg
      obtain ⟨h1, h2⟩ := hmono _ (List.getElem_mem hk)
      exact ⟨h1, by simpa using h2⟩
    · simp only [star, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
  have hrb : ReadsBack 26 D := by
    intro j hj i hi
    rw [hDlen] at hj
    have := hfle m C.output
    rcases hsplit j with rfl | ⟨k, hk, rfl⟩ | ⟨t, rfl⟩
    · exact absurd hi List.not_mem_nil
    · rw [hgk k hk] at hi
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hi
      have := hfle k u
      omega
    · rw [hgs] at hi
      rcases t with _ | _ | _ | _ | _ | t <;> simp [star] at hi <;> omega

  have wsnoc : ∀ (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool),
      Circuit.wires ⟨gs ++ [g], o⟩ x = Circuit.wires ⟨gs, o⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
    fun gs g o x => List.foldl_append
  have run : ∀ (gs : List Gate) (o : ℕ) (x : List Bool),
      (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length ∧
      (∀ i < x.length, (Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false) ∧
      ∀ (j : ℕ) (h : j < gs.length), (Circuit.wires ⟨gs, o⟩ x).getD (x.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then
          (Circuit.wires ⟨gs, o⟩ x).getD i false else false) := by
    intro gs o x
    induction gs using List.reverseRecOn with
    | nil => exact ⟨rfl, fun i _ => rfl, fun j h => absurd h (Nat.not_lt_zero _)⟩
    | append_singleton gs g ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [wsnoc gs g o x]
      generalize Circuit.wires ⟨gs, o⟩ x = W at h1 h2 h3 ⊢
      generalize hval : g.op.eval (g.inputs.map fun i => W.getD i false) = val
      have old : ∀ i < W.length, (W ++ [val]).getD i false = W.getD i false := fun i hi =>
        List.getD_append _ _ _ _ hi
      refine ⟨by simp [h1]; omega, fun i hi => by rw [old i (by omega)]; exact h2 i hi, ?_⟩
      intro j hj
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · rw [old _ (by omega), h3 j hlt, List.getElem_append_left hlt]
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · rfl
      · have hj' : j = gs.length := by simp at hj; omega
        subst hj'
        rw [← h1, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero, List.getElem_concat_length]
        refine hval.symm.trans ?_
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · exact List.getD_eq_default _ _ (by omega)
  have hW : ∀ (E : Circuit) (y : Fin 26 → Bool),
      (∀ i : Fin 26, (E.wires (List.ofFn y)).getD i false = y i) ∧
      (∀ k < E.gates.length, (E.wires (List.ofFn y)).getD (26 + k) false =
        (gateAt E k).op.eval ((gateAt E k).inputs.map fun i =>
          if i < 26 + k then (E.wires (List.ofFn y)).getD i false else false)) ∧
      ∀ i, 26 + E.gates.length ≤ i → (E.wires (List.ofFn y)).getD i false = false := by
    intro E y
    obtain ⟨h1, h2, h3⟩ := run E.gates E.output (List.ofFn y)
    rw [List.length_ofFn] at h1 h2 h3
    have h1 : (E.wires (List.ofFn y)).length = 26 + E.gates.length := h1
    refine ⟨fun i => (h2 i i.2).trans ?_, fun k hk => (h3 k hk).trans ?_,
      fun i hi => List.getD_eq_default _ _ (by omega)⟩
    · rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    · rw [show gateAt E k = E.gates[k] from List.getD_eq_getElem _ _ hk]
  have hev : ∀ (y : Fin 26 → Bool) (k : ℕ) (g : Gate), k < m + 6 → gateAt D k = g →
      (D.wires (List.ofFn y)).getD (26 + k) false =
        g.op.eval (g.inputs.map fun i => (D.wires (List.ofFn y)).getD i false) := by
    intro y k g hk hg
    subst hg
    rw [(hW D y).2.1 k (by omega)]
    exact congrArg _ (List.map_congr_left fun i hi => ite_eq_left (hrb k (by omega) i hi))
  have hor : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl
  have hand : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl

  have hval : ∀ y : Fin 26 → Bool, D.eval (List.ofFn y) =
      (C.eval (List.ofFn fun u => decide (u ≠ v) && y u) || ((y n0 || y n1 || y n2 || y n3) && y v)) := by
    intro y
    obtain ⟨d0, -, -⟩ := hW D y
    obtain ⟨c0, c1, c2⟩ := hW C fun u => decide (u ≠ v) && y u
    have ev := hev y
    show (D.wires (List.ofFn y)).getD (26 + (m + 5)) false =
      ((C.wires (List.ofFn fun u => decide (u ≠ v) && y u)).getD C.output false || _)
    generalize D.wires (List.ofFn y) = LD at d0 ev ⊢
    generalize C.wires (List.ofFn fun u => decide (u ≠ v) && y u) = LC at c0 c1 c2 ⊢
    have h26 : LD.getD 26 false = false := ev 0 _ (by omega) hg0
    have hfw : ∀ k, (∀ j < k, LD.getD (26 + (j + 1)) false = LC.getD (26 + j) false) →
        ∀ w, LD.getD (f k w) false = if w < 26 + k then LC.getD w false else false := by
      intro k ih w
      simp only [f]
      split_ifs with h1 h2 h3 h4
      · rw [h26, h1, c0 v]; simp
      · omega
      · have hw : (⟨w, h3⟩ : Fin 26) ≠ v := fun h => h1 (congrArg Fin.val h)
        exact (d0 ⟨w, h3⟩).trans ((c0 ⟨w, h3⟩).trans (by simp [hw])).symm
      · omega
      · have := ih (w - 26) (by omega)
        rwa [show 26 + (w - 26 + 1) = w + 1 by omega, show 26 + (w - 26) = w by omega] at this
      · exact h26
    have hsh : ∀ k < m, LD.getD (26 + (k + 1)) false = LC.getD (26 + k) false := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        rw [ev (k + 1) _ (by omega) (hgk k hk), c1 k (by omega)]
        dsimp only
        rw [List.map_map]
        exact congrArg _ (List.map_congr_left fun w _ => hfw k (fun j hj => ih j hj (by omega)) w)
    have hout : LD.getD (f m C.output) false = LC.getD C.output false := by
      rw [hfw m hsh]
      split_ifs with h
      · rfl
      · exact (c2 _ (by omega)).symm
    have h1 := ev (m + 1) _ (by omega) (hgs 0)
    have h2 := ev (m + 2) _ (by omega) (hgs 1)
    have h3 := ev (m + 3) _ (by omega) (hgs 2)
    have h4 := ev (m + 4) _ (by omega) (hgs 3)
    have h5 := ev (m + 5) _ (by omega) (hgs 4)
    simp only [star, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil] at h1 h2 h3 h4 h5
    simp only [h5, h4, h3, h2, h1, hor, hand, hout, d0]

  have hD : ∀ y : Fin 26 → Bool, D.eval (List.ofFn y) = true ↔ ∃ a b : Fin 13,
      (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) ∧ y (Fin.castAdd 13 a) = true ∧
        y (Fin.natAdd 13 b) = true := by
    intro y
    rw [hval, Bool.or_eq_true, hspec (fun u => decide (u ≠ v) && y u) (by simp), hstar]
    constructor
    · rintro (⟨a, b, hab, ha, hb⟩ | ⟨a, b, hab, ha, hb, -⟩)
      · simp only [Bool.and_eq_true] at ha hb
        exact ⟨a, b, hab, ha.2, hb.2⟩
      · exact ⟨a, b, hab, ha, hb⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      by_cases h : v = Fin.castAdd 13 a ∨ v = Fin.natAdd 13 b
      · exact Or.inr ⟨a, b, hab, ha, hb, h⟩
      · have ha' : Fin.castAdd 13 a ≠ v := fun e => h (Or.inl e.symm)
        have hb' : Fin.natAdd 13 b ≠ v := fun e => h (Or.inr e.symm)
        exact Or.inl ⟨a, b, hab, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨ha', ha⟩,
          by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hb', hb⟩⟩
  have hD' : ∀ a b : Fin 13 → Bool, D.eval (List.ofFn a ++ List.ofFn b) = true ↔
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ a p = true ∧ b l = true := by
    intro a b
    have e : D.eval (List.ofFn (Fin.append a b)) = true ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ Fin.append a b (Fin.castAdd 13 p) = true ∧
          Fin.append a b (Fin.natAdd 13 l) = true := hD (Fin.append a b)
    simpa only [List.ofFn_fin_append, Fin.append_left, Fin.append_right] using e

  have coneStep_eq : ∀ (cs : List (List ℕ)) (g : Gate), coneStep 26 cs g =
      cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])] := fun _ _ => rfl
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; rfl
    | cons g gs ih => intro cs; rw [List.foldl_cons, ih, coneStep_eq]; simp; omega
  have cones_char : ∀ (gs : List Gate) (i j : ℕ), i ∈ (gs.foldl (coneStep 26) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, 26 ≤ w ∧ w < 26 + j ∧
        (i = w - 26 ∨ i ∈ (gs.foldl (coneStep 26) []).getD (w - 26) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      have hl : (gs.foldl (coneStep 26) []).length = gs.length := by rw [cones_len]; simp
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, coneStep_eq]
      generalize gs.foldl (coneStep 26) [] = cs at ih hl ⊢
      have old : ∀ k < gs.length, ∀ x, (cs ++ [x]).getD k [] = cs.getD k [] :=
        fun k hk _ => List.getD_append _ _ _ _ (by omega)
      rcases Nat.lt_trichotomy j gs.length with h | rfl | h
      · rw [old j h, ih, List.getD_append _ _ _ _ h, List.length_append, List.length_singleton]
        constructor
        · rintro ⟨-, w, hw, h1, h2, h3⟩
          exact ⟨by omega, w, hw, h1, h2, by rwa [old _ (by omega)]⟩
        · rintro ⟨-, w, hw, h1, h2, h3⟩
          exact ⟨h, w, hw, h1, h2, by rwa [old _ (by omega)] at h3⟩
      · rw [List.getD_append_right _ _ _ _ hl.le, hl, Nat.sub_self, List.getD_cons_zero,
          List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero,
          List.mem_flatMap]
        simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons, List.length_append,
          List.length_singleton]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          exact ⟨by omega, w, hw, h1, h2, by rwa [old _ (by omega)]⟩
        · rintro ⟨-, w, hw, h1, h2, h3⟩
          exact ⟨w, ⟨hw, h1, h2⟩, by rwa [old _ (by omega)] at h3⟩
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp only [List.not_mem_nil, false_iff, List.length_append, List.length_singleton, not_and]
        intro h'
        omega
  have hcone : ∀ (E : Circuit) (i j : ℕ), InCone 26 E i j ↔ j < E.gates.length ∧
      ∃ w ∈ (gateAt E j).inputs, 26 ≤ w ∧ w < 26 + j ∧ (i = w - 26 ∨ InCone 26 E i (w - 26)) :=
    fun E => cones_char E.gates
  have hlt : ∀ (E : Circuit) (j i : ℕ), InCone 26 E i j → i < j := by
    intro E j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i h
      obtain ⟨-, w, -, h1, h2, h3 | h3⟩ := (hcone E i j).1 h
      · omega
      · exact Nat.lt_trans (ih _ (by omega) i h3) (by omega)
  have hc0 : ∀ i, ¬InCone 26 D i 0 := fun i h => by
    obtain ⟨-, w, hw, -⟩ := (hcone D i 0).1 h
    exact absurd hw List.not_mem_nil

  have hsc : ∀ k < m, ∀ i, InCone 26 D i (k + 1) → i = 0 ∨ ∃ i', i = i' + 1 ∧ InCone 26 C i' k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i h
      obtain ⟨-, w, hw, h1, h2, h3⟩ := (hcone D i (k + 1)).1 h
      rw [hgk k hk] at hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
      have hu' : f k u = 26 ∨ (26 ≤ u ∧ u < 26 + k ∧ f k u = u + 1) := by
        simp only [f] at h1 ⊢; split_ifs at h1 ⊢ <;> omega
      rcases hu' with e | ⟨e1, e2, e⟩
      · rw [e] at h3
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact absurd h3 (hc0 i)
      · rw [e, show u + 1 - 26 = u - 26 + 1 by omega] at h3
        have hin : ∀ i', (i' = u - 26 ∨ InCone 26 C i' (u - 26)) → InCone 26 C i' k :=
          fun i' h' => (hcone C i' k).2 ⟨by omega, u, hu, e1, e2, h'⟩
        rcases h3 with h3 | h3
        · exact Or.inr ⟨u - 26, h3, hin _ (Or.inl rfl)⟩
        · rcases ih (u - 26) (by omega) (by omega) i h3 with h0 | ⟨i', rfl, h'⟩
          · exact Or.inl h0
          · exact Or.inr ⟨i', rfl, hin _ (Or.inr h')⟩

  have hstarc : ∀ t < 4, ∀ i, InCone 26 D i (m + 1 + t) → m + 1 ≤ i := by
    have hsg : ∀ t < 4, ∀ w ∈ (gateAt D (m + 1 + t)).inputs, w < 26 ∨ (1 ≤ t ∧ w = 26 + (m + t)) := by
      intro t ht w hw
      rw [hgs] at hw
      rcases t with _ | _ | _ | _ | t <;> simp [star] at hw <;> omega
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht i h
      obtain ⟨-, w, hw, h1, -, h3⟩ := (hcone D i _).1 h
      rcases hsg t ht w hw with h4 | ⟨h4, rfl⟩
      · omega
      · rw [show 26 + (m + t) - 26 = m + 1 + (t - 1) by omega] at h3
        rcases h3 with h3 | h3
        · omega
        · exact ih (t - 1) (by omega) (by omega) i h3
  have hnoD : ¬∃ i j, (gateAt D i).op = GateOp.and ∧ (gateAt D j).op = GateOp.and ∧
      InCone 26 D i j := by
    rintro ⟨i, j, hi, hj, hij⟩
    have hil := hlt D j i hij
    rcases hsplit j with rfl | ⟨k, hk, rfl⟩ | ⟨t, rfl⟩
    · exact hc0 i hij
    · rw [hgk k hk] at hj
      rcases hsc k hk i hij with rfl | ⟨i', rfl, hc⟩
      · exact GateOp.noConfusion hi
      · rw [hgk i' (by have := hlt C k i' hc; omega)] at hi
        exact hnest ⟨i', k, hi, hj, hc⟩
    · rw [hgs] at hj
      have ht : t = 3 := by
        rcases t with _ | _ | _ | _ | _ | t
        all_goals first | rfl | exact GateOp.noConfusion hj
      subst ht
      obtain ⟨s, rfl⟩ : ∃ s, i = m + 1 + s := ⟨i - (m + 1), by have := hstarc 3 (by omega) i hij; omega⟩
      rw [hgs] at hi
      rcases s with _ | _ | _ | s
      all_goals first | exact GateOp.noConfusion hi | omega

  have hx : ∀ a b : Fin 13, decide (a - b = 0 ∨ a - b = 1 ∨ a - b = 3 ∨ a - b = 9) = true ↔
      (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) := by decide
  have h64 : 64 ≤ D.size := by
    refine twoLevel D hmonoD hrb ⟨fun p l h => (hD' _ _).2 ⟨p, l, (hx p l).1 h, by simp, by simp⟩,
      fun S _ _ => ?_⟩ hnoD
    rw [← Bool.not_eq_true, hD']
    rintro ⟨p, l, hpl, hp, hl⟩
    exact Bool.noConfusion (((hx p l).2 hpl).symm.trans (of_decide_eq_true hl p (of_decide_eq_true hp)))
  have hDs : D.size = m + 6 := hDlen
  have hCs : C.size = m := hm
  omega
