import PEqualNP.Defs

-- For every exceptional partition the two edge sets require eight vertices
-- when covered separately. The two budget inequalities would provide seven.
-- The first premise is the checked gate count and cover bound of L-meta-1491.
-- The second concerns the triangle on 5, 8, 9 and the edges 4-8 and 4-10.
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_4133_751
    (account : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (junkBudget : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 21 →
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        2 ≤ (PEqualNP.TopForm.junk G C).card →
        let U := PEqualNP.TopForm.Ustar G C
        let B := 2 * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
        U.card ≤ B → B < 2 * U.card →
          s(4,8) ∈ U → s(4,10) ∈ U → s(5,8) ∈ U → s(5,9) ∈ U → s(8,9) ∈ U →
          ∃ J : Finset (Fin 11), (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ J ∨ v ∈ J) ∧
            U.card + J.card ≤ B + 1) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; have x3 : Finset (Sym2 (Fin (11 : ℕ))) → BitVec (16 : ℕ) := fun (x3 : Finset (Sym2 (Fin (11 : ℕ)))) =>   BitVec.ofNat (16 : ℕ)     (PEqualNP.MetaComplexity.tableIndex fun (x4 : Fin (16 : ℕ)) =>       have x5 : ℕ × ℕ := x1.getD ↑x4 ((0 : ℕ), (0 : ℕ));       Decidable.decide (s(Fin.ofNat (11 : ℕ) x5.1, Fin.ofNat (11 : ℕ) x5.2) ∈ x3)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x4 →       PEqualNP.TopForm.TopForm x2 x4 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card →           have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;           have x10 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;           x9.card ≤ x10 → x10 < (2 : ℕ) * x9.card → x3 x9 ∉ [(36608 : BitVec (16 : ℕ)), (44800 : BitVec (16 : ℕ)), (44864 : BitVec (16 : ℕ)), (44992 : BitVec (16 : ℕ)), (48960 : BitVec (16 : ℕ)), (52992 : BitVec (16 : ℕ)), (53120 : BitVec (16 : ℕ)), (53184 : BitVec (16 : ℕ)), (57216 : BitVec (16 : ℕ)), (61184 : BitVec (16 : ℕ)), (61248 : BitVec (16 : ℕ)), (61312 : BitVec (16 : ℕ)), (61376 : BitVec (16 : ℕ)), (65280 : BitVec (16 : ℕ)), (65344 : BitVec (16 : ℕ)), (65408 : BitVec (16 : ℕ)), (65472 : BitVec (16 : ℕ))] := by
  let es : List (ℕ × ℕ) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let G := PEqualNP.EdgeOwnership.edgeGraph 11 es
  dsimp only
  intro C short least top junk low high
  let U := PEqualNP.TopForm.Ustar G C
  let B := 2 * (PEqualNP.TopForm.centreless G C).card +
    (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
  let f (i : Fin 16) : Bool := let e := es.getD i.val (0,0)
    decide (s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2) ∈ U)
  let mask := BitVec.ofNat 16 (PEqualNP.MetaComplexity.tableIndex f)
  have step {n : ℕ} (x : Fin (n+1) → Bool) :
      PEqualNP.MetaComplexity.tableIndex x =
        PEqualNP.MetaComplexity.tableIndex (fun i : Fin n => x i.castSucc) +
        (if x (Fin.last n) = true then 2^n else 0) := by
    change (∑ i : Fin (n+1), if x i = true then 2 ^ i.val else 0) = _
    rw [Fin.sum_univ_castSucc]
    rfl
  have bound {n : ℕ} (x : Fin n → Bool) : PEqualNP.MetaComplexity.tableIndex x < 2^n := by
    induction n with
    | zero =>
      change (∑ i : Fin 0, if x i = true then 2 ^ i.val else 0) < 1
      simp
    | succ n ih =>
      have h := ih (fun i : Fin n => x i.castSucc)
      rw [step, pow_succ]
      split <;> omega
  have read {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
      (PEqualNP.MetaComplexity.tableIndex x).testBit i.val = x i := by
    induction n with
    | zero => exact i.elim0
    | succ n ih =>
      have hlt := bound (fun j : Fin n => x j.castSucc)
      rw [step]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.val_last]
        cases x (Fin.last n) <;> simp only [ Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        · exact Nat.testBit_lt_two_pow hlt
        · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
          rfl
      · change Nat.testBit (_ + _) j.val = x j.castSucc
        cases x (Fin.last n) <;> simp only [ Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        · exact ih _ j
        · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
          exact ih _ j
  have bit (i : Fin 16) : mask.getLsbD i.val = f i := by
    simp only [mask, BitVec.getLsbD_ofNat, decide_eq_true i.isLt, Bool.true_and, read]
  change mask ∉ ([36608, 44800, 44864, 44992, 48960, 52992, 53120, 53184, 57216, 61184, 61248, 61312, 61376, 65280, 65344, 65408, 65472] : List (BitVec 16))
  intro bad
  have common : mask &&& (36608 : BitVec 16) = 36608 := by
    have cases := bad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
    rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals rw [h]; decide
  have present (i : Fin 16) (hi : (36608 : BitVec 16).getLsbD i.val = true) : f i = true := by
    have he := congrArg (fun z : BitVec 16 => z.getLsbD i.val) common
    simp only [BitVec.getLsbD_and, hi, Bool.and_true] at he
    exact (bit i).symm.trans he
  have p8 : s((4 : Fin 11), 8) ∈ U := of_decide_eq_true (present 8 (by decide))
  have p9 : s((4 : Fin 11), 10) ∈ U := of_decide_eq_true (present 9 (by decide))
  have p10 : s((5 : Fin 11), 8) ∈ U := of_decide_eq_true (present 10 (by decide))
  have p11 : s((5 : Fin 11), 9) ∈ U := of_decide_eq_true (present 11 (by decide))
  have p15 : s((8 : Fin 11), 9) ∈ U := of_decide_eq_true (present 15 (by decide))
  have four : PEqualNP.TopForm.NoFourCycle G := by decide +kernel
  have edges : G.edgeFinset.card = 16 := by decide +kernel
  have nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨count, centres⟩ := account 11 G C four nonempty least top
  let H := G.deleteEdges (↑U)
  let attainable (k : ℕ) := ∃ S : Finset (Fin 11), H.IsVertexCover ↑S ∧ S.card = k
  letI : DecidablePred attainable := Classical.decPred _
  have existsCover : ∃ k, attainable k := ⟨_, Finset.univ, by simp, rfl⟩
  obtain ⟨K, coverK, cardK⟩ := Nat.find_spec existsCover
  have minimal : PEqualNP.MetaComplexity.NestedCover.IsMinCover H K :=
    ⟨coverK, fun T ht => cardK.trans_le (Nat.find_min' existsCover ⟨T, ht, rfl⟩)⟩
  have boundK : K.card + B ≤ U.card + 6 := by
    have hk := centres K minimal
    rw [edges] at count
    change 16 + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
      2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
      (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + U.card + 1 at count
    dsimp only [B]
    omega
  obtain ⟨J, coverJ, boundJ⟩ := junkBudget C short least top junk low high p8 p9 p10 p11 p15
  change K.card + B ≤ U.card + 6 at boundK
  change U.card + J.card ≤ B + 1 at boundJ
  have small : K.card + J.card ≤ 7 := by omega
  let w (T : Finset (Fin 11)) (v : Fin 11) : ℕ := if v ∈ T then 1 else 0
  have charge (T : Finset (Fin 11)) (a b : Fin 11) (h : a ∈ T ∨ b ∈ T) :
      1 ≤ w T a + w T b := by
    rcases h with ha | hb
    · simp [w, ha]
    · simp [w, hb]
  have total (T : Finset (Fin 11)) : (∑ i, w T i) = T.card := by simp [w]
  have sumK := total K
  have sumJ := total J
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, Nat.add_zero] at sumK sumJ
  change w K 0 + (w K 1 + (w K 2 + (w K 3 + (w K 4 + (w K 5 + (w K 6 + (w K 7 + (w K 8 + (w K 9 + (w K 10)))))))))) = K.card at sumK
  change w J 0 + (w J 1 + (w J 2 + (w J 3 + (w J 4 + (w J 5 + (w J 6 + (w J 7 + (w J 8 + (w J 9 + (w J 10)))))))))) = J.card at sumJ
  have rule (i : Fin 16) (a b : Fin 11)
      (h : f i = decide (s(a,b) ∈ U)) (adj : G.Adj a b) :
      if mask.getLsbD i.val then 1 ≤ w J a + w J b else 1 ≤ w K a + w K b := by
    rw [bit, h]
    by_cases e : s(a,b) ∈ U
    · simpa [e] using charge J a b (coverJ a b e)
    · have hab := coverK (SimpleGraph.deleteEdges_adj.mpr ⟨adj, e⟩)
      simpa [e] using charge K a b hab
  have e0 := rule 0 0 9 rfl (by decide +kernel)
  have e1 := rule 1 0 10 rfl (by decide +kernel)
  have e2 := rule 2 1 4 rfl (by decide +kernel)
  have e3 := rule 3 1 8 rfl (by decide +kernel)
  have e4 := rule 4 2 5 rfl (by decide +kernel)
  have e5 := rule 5 2 10 rfl (by decide +kernel)
  have e6 := rule 6 3 6 rfl (by decide +kernel)
  have e7 := rule 7 3 7 rfl (by decide +kernel)
  have e8 := rule 8 4 8 rfl (by decide +kernel)
  have e9 := rule 9 4 10 rfl (by decide +kernel)
  have e10 := rule 10 5 8 rfl (by decide +kernel)
  have e11 := rule 11 5 9 rfl (by decide +kernel)
  have e12 := rule 12 6 7 rfl (by decide +kernel)
  have e13 := rule 13 6 10 rfl (by decide +kernel)
  have e14 := rule 14 7 9 rfl (by decide +kernel)
  have e15 := rule 15 8 9 rfl (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at bad
  rcases bad with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    simp (disch := decide) only [h, ite_eq_left, ite_eq_right] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
    omega
