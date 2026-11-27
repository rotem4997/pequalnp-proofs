import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.FlagCore

/-!
# The modes of the flag rewiring

`mode`: for each operand of `g` there is a valid feed keeping the edges off the corner, and the corner too unless it
is one vertex and no AND reading `g` has `zz i` among its partners. `flag_lt`: the flag case.
-/

namespace PEqualNP.MetaComplexity.FlagCore

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ} {s : Fin n → Bool}
  {zz : Fin 2 → Fin n}

/-- Two vertices share at most one neighbour. -/
theorem c4 (h4 : NoFourCycle G) (a b u w : Fin n) (hab : a ≠ b) (h1 : G.Adj a u) (h2 : G.Adj b u)
    (h3 : G.Adj a w) (h4' : G.Adj b w) : u = w :=
  Finset.card_le_one.1 (h4 a b hab) u (by simp [h1, h2]) w (by simp [h3, h4'])

theorem gate_val (F : Flag G C g s zz) (i : Fin 2) (x : Fin n → Bool) (k : ℕ)
    (h : (Mode.gate k : Mode n).val C g zz i x = true) : graphFun G ∅ x = true := by
  have h' : (x (zz i) && wireVal n C (opnd C g (1 - i)) x) = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨y, hy, hw⟩ := (opnd_val F.one (1 - i) x).1 h'.2
  exact (graphFun_empty G x).2 ⟨zz i, y, F.adj i y hw, h'.1, hy⟩

theorem opnd_on (F : Flag G C g s zz) (i : Fin 2) (x : Fin n → Bool) (y : Fin n) (hy : V C g i y) (hx : x y = true) :
    wireVal n C (opnd C g i) x = true := (opnd_val F.one i x).2 ⟨y, hx, hy⟩

theorem corner_on (d : Fin 2) : pairInput (zz 0) (zz 1) (zz d) = true := by
  fin_cases d <;> simp [pairInput]

theorem gate_on (F : Flag G C g s zz) (i : Fin 2) (x : Fin n → Bool) (k : ℕ) (hz : x (zz i) = true) (y : Fin n)
    (hy : V C g (1 - i) y) (hx : x y = true) : (Mode.gate k : Mode n).val C g zz i x = true := by
  show (x (zz i) && wireVal n C (opnd C g (1 - i)) x) = true
  rw [hz, opnd_on F (1 - i) x y hy hx]
  rfl

/-- A partner vertex on the side of `zz i`, other than `zz i`, is adjacent to the other variables of the other
operand. -/
theorem triple (F : Flag G C g s zz) (h4 : NoFourCycle G) (two : ∀ i, ∃ u v : Fin n, u ≠ v ∧ V C g i u ∧ V C g i v)
    (i : Fin 2) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and) (q : Fin n)
    (hp : PZ C g k q) (hs : s q = s (zz i)) (y : Fin n) (hy : V C g (1 - i) y)
    (hyz : y ≠ zz (1 - i)) : G.Adj q y := by
  have H := F.one
  obtain ⟨a, ha, haz⟩ : ∃ a, V C g i a ∧ a ≠ zz i := by
    obtain ⟨u, w, huw, hu, hw⟩ := two i
    by_cases h : u = zz i
    · exact ⟨w, hw, fun h' => huw (h.trans h'.symm)⟩
    · exact ⟨u, hu, h⟩
  have hazo : G.Adj (zz (1 - i)) a := F.adj (1 - i) a (by rw [fin2_inv]; exact ha)
  have hzy : G.Adj (zz i) y := F.adj i y hy
  have hzz : G.Adj (zz i) (zz (1 - i)) := F.adj i _ (F.mem (1 - i))
  have hnay : ¬ G.Adj a y := fun h =>
    hyz (c4 h4 a (zz i) y (zz (1 - i)) haz h hzy hazo.symm hzz)
  have hsa : s a = s (zz i) := F.side i a ha
  let x : Fin n → Bool := fun w => decide (w = a ∨ w = y ∨ w = q)
  have hxa : x a = true := by simp [x]
  have hxy : x y = true := by simp [x]
  have hxq : x q = true := by simp [x]
  have hgx : gateVal n C g x = true :=
    (val_and' C H.ao g H.hg H.gand x i).2 ⟨opnd_on F i x a ha hxa, opnd_on F (1 - i) x y hy hxy⟩
  obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G x).1 (pz_F H k hk ho q hp x hgx hxq)
  have hnaq : ¬ G.Adj a q := fun h => F.bip _ _ h (hsa.trans hs.symm)
  simp only [x, decide_eq_true_eq] at hu hw
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  · exact absurd huw (G.loopless.irrefl _)
  · exact absurd huw hnay
  · exact absurd huw hnaq
  · exact absurd huw.symm hnay
  · exact absurd huw (G.loopless.irrefl _)
  · exact huw.symm
  · exact absurd huw.symm hnaq
  · exact huw
  · exact absurd huw (G.loopless.irrefl _)

theorem mode (F : Flag G C g s zz) (h4 : NoFourCycle G) (two : ∀ i, ∃ u v : Fin n, u ≠ v ∧ V C g i u ∧ V C g i v)
    (i : Fin 2) : ∃ M : Mode n, (∀ k, M = Mode.gate k → Killer C g zz i k) ∧
      (∀ x k q, k < C.gates.length → (gateAt C k).op = GateOp.and → PZ C g k q → s q = s (zz i) →
        M.val C g zz i x = true → x q = true → graphFun G ∅ x = true) ∧
      (∀ y, V C g (1 - i) y → y ≠ zz (1 - i) → M.val C g zz i (pairInput (zz i) y) = true) ∧
      (M.val C g zz i (pairInput (zz 0) (zz 1)) = true ∨ ((∃ t, M = Mode.vtx t) ∧ ∀ k, ¬ Killer C g zz i k)) := by
  by_cases hk : ∃ k, Killer C g zz i k
  · obtain ⟨k0, hk0⟩ := hk
    refine ⟨Mode.gate k0, ?_, ?_, ?_, Or.inl ?_⟩
    · intro k h
      injection h with h
      rw [← h]; exact hk0
    · intro x k q _ _ _ _ hm _
      exact gate_val F i x k0 hm
    · intro y hy _
      exact gate_on F i _ k0 (by simp [pairInput]) y hy (by simp [pairInput])
    · exact gate_on F i _ k0 (corner_on i) (zz (1 - i)) (F.mem _) (corner_on _)
  · have hno : ∀ k, ¬ Killer C g zz i k := fun k h => hk ⟨k, h⟩
    by_cases hall : ∀ k q, k < C.gates.length → (gateAt C k).op = GateOp.and → PZ C g k q → s q = s (zz i) →
        q = zz i
    · refine ⟨Mode.fac, (fun k h => by cases h), ?_, ?_, Or.inl ?_⟩
      · intro x k q hkl ho hp hs hm hq
        have hm' : wireVal n C (opnd C g (1 - i)) x = true := hm
        obtain ⟨y, hy, hw⟩ := (opnd_val F.one (1 - i) x).1 hm'
        rw [hall k q hkl ho hp hs] at hq
        exact (graphFun_empty G x).2 ⟨zz i, y, F.adj i y hw, hq, hy⟩
      · intro y hy _
        exact opnd_on F (1 - i) _ y hy (by simp [pairInput])
      · exact opnd_on F (1 - i) _ (zz (1 - i)) (F.mem _) (corner_on _)
    · push Not at hall
      obtain ⟨k1, q1, hk1, ho1, hp1, hs1, hq1⟩ := hall
      obtain ⟨t, ht, htz⟩ : ∃ t, V C g (1 - i) t ∧ t ≠ zz (1 - i) := by
        obtain ⟨u, w, huw, hu, hw⟩ := two (1 - i)
        by_cases h : u = zz (1 - i)
        · exact ⟨w, hw, fun h' => huw (h.trans h'.symm)⟩
        · exact ⟨u, hu, h⟩
      refine ⟨Mode.vtx t, (fun k h => by cases h), ?_, ?_, Or.inr ⟨⟨t, rfl⟩, hno⟩⟩
      · intro x k q hkl ho hp hs hm hq
        have hm' : x t = true := hm
        refine (graphFun_empty G x).2 ⟨q, t, triple F h4 two i k hkl ho q hp hs t ht htz, hq, hm'⟩
      · intro y hy hyz
        have hyt : y = t := by
          have a1 := triple F h4 two i k1 hk1 ho1 q1 hp1 hs1 y hy hyz
          have a2 := triple F h4 two i k1 hk1 ho1 q1 hp1 hs1 t ht htz
          exact c4 h4 q1 (zz i) y t hq1 a1 (F.adj i y hy) a2 (F.adj i t ht)
        show pairInput (zz i) y t = true
        rw [hyt]
        simp [pairInput]

theorem flag_lt (F : Flag G C g s zz) (h4 : NoFourCycle G) (two : ∀ i, ∃ u v : Fin n, u ≠ v ∧ V C g i u ∧ V C g i v) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have H := F.one
  have hAO := H.ao
  have hgl := H.hg
  choose M hMg hMv hMe hMc using mode F h4 two
  by_cases hcor : (∃ i, (M i).val C g zz i (pairInput (zz 0) (zz 1)) = true) ∨
      ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ T ≠ g ∧
        ∀ c, ∃ y, pairInput (zz 0) (zz 1) y = true ∧ wireVal n C (opnd C T c) (unitInput y) = true
  · exact core F M none (fun i k h => Or.inl (hMg i k h)) (fun h => absurd rfl h) (fun ia h => by simp at h)
      hMv hMe hcor
  · push Not at hcor
    obtain ⟨hc1, hc2⟩ := hcor
    have hvt : ∀ i, (∃ t, M i = Mode.vtx t) ∧ ∀ k, ¬ Killer C g zz i k := fun i =>
      (hMc i).resolve_left (hc1 i)
    -- operand 0 of `g` is a gate
    obtain ⟨u0, w0, huw0, hu0, hw0⟩ := two 0
    obtain ⟨ia, hia⟩ : ∃ ia, opnd C g 0 = n + ia := by
      rcases srcOf_cases (n := n) (opnd C g 0) with ⟨a, ha⟩ | h
      · exfalso
        have key : ∀ y, V C g 0 y → a = y := by
          intro y hy
          unfold V at hy
          rw [ha, wireVal_lt C _ a.2] at hy
          simpa [unitInput] using hy
        exact huw0 ((key u0 hu0).symm.trans (key w0 hw0))
      · exact h
    have hlt0 := opnd_lt C hAO g hgl 0
    have hial : ia < C.gates.length := by omega
    -- no AND other than `g` has the variables of operand 0 among those of an operand
    have hnoT : ∀ T < C.gates.length, (gateAt C T).op = GateOp.and → T ≠ g → ∀ d,
        (∀ y, V C g 0 y → wireVal n C (opnd C T d) (unitInput y) = true) → False := by
      intro T hT hTo hTg d hsub
      have hlt := opnd_lt C hAO T hT (1 - d)
      by_cases hr : OrReaches n C (opnd C T (1 - d)) g
      · have hp : ∀ y, V C g 0 y → PZ C g T y := fun y hy =>
          (pz_iff C g T y).2 ⟨1 - d, hr, by rw [fin2_inv]; exact hsub y hy⟩
        have e1 := F.uniq 0 T u0 hT hTo (hp u0 hu0) hu0
        have e2 := F.uniq 0 T w0 hT hTo (hp w0 hw0) hw0
        exact huw0 (e1.trans e2.symm)
      · obtain ⟨q, _, hq⟩ := (pure_val H T hT hTo (1 - d) hr (fun _ => true)).1 (ones_val C hAO _ (by omega))
        have hadj : ∀ y, V C g 0 y → G.Adj y q := fun y hy => and_pair' H T hT hTo hTg d y q (hsub y hy) hq
        have hadj1 : ∀ y, V C g 0 y → G.Adj y (zz 1) := fun y hy => (F.adj 1 y hy).symm
        have hqz : q = zz 1 := c4 h4 u0 w0 q (zz 1) huw0 (hadj u0 hu0) (hadj w0 hw0) (hadj1 u0 hu0) (hadj1 w0 hw0)
        obtain ⟨c, hc⟩ := hc2 T hT hTo hTg
        have hd : c = d ∨ c = 1 - d := fin2_or d c
        rcases hd with rfl | rfl
        · exact hc (zz 0) (corner_on 0) (hsub _ (F.mem 0))
        · exact hc (zz 1) (corner_on 1) (by rw [← hqz]; exact hq)
    have hunit : ∀ y, V C g 0 y → wireVal n C (n + ia) (unitInput y) = true := by
      intro y hy
      rw [← hia]; exact hy
    have honly : ∀ k < C.gates.length, k ≠ g → ∀ c, opnd C k c ≠ n + ia := by
      intro k hk hkg c hc
      have hltk := opnd_lt C hAO k hk c
      rcases LeafBound.ao_op hAO hk with ho | ho
      · exact hnoT k hk ho hkg c fun y hy => by rw [hc]; exact hunit y hy
      · have hsub : ∀ y, V C g 0 y → gateVal n C k (unitInput y) = true := fun y hy =>
          (val_or' C hAO k hk ho _).2 ⟨c, by rw [hc]; exact hunit y hy⟩
        have hlow : Low G C (n + k) := by
          intro hb
          have h2 := hb (unitInput (zz 0)) (hsub _ (F.mem 0))
          rw [unit_false] at h2
          exact absurd h2 (by decide)
        obtain ⟨T, hT, hTo, d, hd⟩ := above_and H k hk hlow
        have hltT := opnd_lt C hAO T hT d
        have hle := reach_le C hAO k _ (by omega) hd
        have hsub' : ∀ y, V C g 0 y → wireVal n C (opnd C T d) (unitInput y) = true := fun y hy =>
          hle.2 _ (hsub y hy)
        by_cases hTg : T = g
        · subst hTg
          have hd2 : d = 0 ∨ d = 1 := fin2_or 0 d
          rcases hd2 with rfl | rfl
          · have := hle.1
            omega
          · exact F.opp (F.side 1 _ (hsub' _ (F.mem 0)))
        · exact hnoT T hT hTo hTg d hsub'
    let M' : Fin 2 → Mode n := fun i => if i = 0 then Mode.gate ia else M 1
    have hM0 : M' 0 = Mode.gate ia := rfl
    have hM1 : M' 1 = M 1 := rfl
    refine core F M' (some ia) ?_ (fun _ => ⟨by rw [hM1]; exact (hvt 1).1, (hvt 1).2⟩) ?_ ?_ ?_ (Or.inl ⟨0, ?_⟩)
    · intro i k h
      have hi : i = 0 ∨ i = 1 := fin2_or 0 i
      rcases hi with rfl | rfl
      · rw [hM0] at h
        injection h with h
        exact Or.inr ⟨rfl, by rw [h]⟩
      · rw [hM1] at h
        exact Or.inl (hMg 1 k h)
    · intro ib h
      have : ia = ib := by simpa using h
      subst this
      exact ⟨hial, hia, honly⟩
    · intro i x k q hk ho hp hs hm hq
      have hi : i = 0 ∨ i = 1 := fin2_or 0 i
      rcases hi with rfl | rfl
      · exact gate_val F 0 x ia hm
      · exact hMv 1 x k q hk ho hp hs hm hq
    · intro i y hy hyz
      have hi : i = 0 ∨ i = 1 := fin2_or 0 i
      rcases hi with rfl | rfl
      · exact gate_on F 0 _ ia (by simp [pairInput]) y hy (by simp [pairInput])
      · exact hMe 1 y hy hyz
    · exact gate_on F 0 _ ia (corner_on 0) (zz 1) (F.mem 1) (corner_on 1)

end PEqualNP.MetaComplexity.FlagCore
