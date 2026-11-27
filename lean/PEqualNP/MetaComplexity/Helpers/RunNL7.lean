import PEqualNP.MetaComplexity.Helpers.RunNL6

/-!
# Theorem NL, part 7: the count, and the statement of the row

The removed list `L` has `|C| - |R|` gates and computes `F` with `x_e := 1`. If no circuit of one
gate fewer computes that function, `L` is minimal, the free-input-chain statement gives its chain
at the last input, and `nl_lift` contradicts the two points. So the restriction has a circuit of
`|C| - |R| - 1` gates; `R` is the three gates of the NOT state, or four with the private operand.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunNL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem nl_ofFn_getD {m : ℕ} (f : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The free-input-chain conclusion on `L`, indexed by naturals. -/
theorem nl_chain_of (n : ℕ) (L : Circuit) (k : ℕ) (c : Fin (k + 1) → Fin L.gates.length)
    (hmono : StrictMono c) (hout : L.output = n + 1 + (c (Fin.last k)).val)
    (hor : ∀ i : Fin (k + 1), (L.gates.get (c i)).op = GateOp.or ∧
      (L.gates.get (c i)).inputs.length = 2)
    (h0 : n ∈ (L.gates.get (c 0)).inputs)
    (hstep : ∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (L.gates.get (c i.succ)).inputs)
    (habove : ∀ j : Fin L.gates.length,
      Relation.TransGen (nlFR n L) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j)
    (hw0 : ∃ w ∈ (L.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧
      ¬ Relation.TransGen (nlFR n L) n w)
    (hw : ∀ i : Fin k, ∃ w ∈ (L.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧
      w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (nlFR n L) n w) :
    nlChain n L k (fun i => if h : i ≤ k then (c ⟨i, by omega⟩).val else 0) := by
  have hc : ∀ i (hi : i ≤ k), (fun i => if h : i ≤ k then (c ⟨i, by omega⟩).val else 0) i =
      (c ⟨i, by omega⟩).val := by
    intro i hi; simp [hi]
  have hg : ∀ i (hi : i ≤ k), L.gates.getD (c ⟨i, by omega⟩).val nlG0 =
      L.gates.get (c ⟨i, by omega⟩) := by
    intro i hi
    rw [nl_getD (c ⟨i, by omega⟩).isLt]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [dif_pos hi]; exact (c _).isLt
  · intro i j hij hj
    rw [dif_pos (show i ≤ k by omega), dif_pos hj]
    exact hmono (show (⟨i, by omega⟩ : Fin (k + 1)) < ⟨j, by omega⟩ from hij)
  · intro i hi; rw [dif_pos hi, hg i hi]; exact hor _
  · intro i hi
    rw [dif_pos hi, hg i hi]
    by_cases h00 : i = 0
    · subst h00
      simp only [if_true]
      exact h0
    · rw [if_neg h00, dif_pos (show i - 1 ≤ k by omega)]
      have := hstep ⟨i - 1, by omega⟩
      have e1 : (⟨i - 1, by omega⟩ : Fin k).succ = ⟨i, by omega⟩ := by
        ext; simp; omega
      have e2 : (⟨i - 1, by omega⟩ : Fin k).castSucc = ⟨i - 1, by omega⟩ := rfl
      rw [e1, e2] at this
      exact this
  · intro i hi
    rw [dif_pos hi, hg i hi]
    by_cases h00 : i = 0
    · subst h00
      obtain ⟨w, h1, h2, _, h4⟩ := hw0
      exact ⟨w, h1, by simpa using h2, h2, h4⟩
    · rw [if_neg h00, dif_pos (show i - 1 ≤ k by omega)]
      obtain ⟨w, h1, h2, h3, _, h5⟩ := hw ⟨i - 1, by omega⟩
      have e1 : (⟨i - 1, by omega⟩ : Fin k).succ = ⟨i, by omega⟩ := by
        ext; simp; omega
      have e2 : (⟨i - 1, by omega⟩ : Fin k).castSucc = ⟨i - 1, by omega⟩ := rfl
      rw [e1] at h1
      rw [e2] at h2
      exact ⟨w, h1, h2, h3, h5⟩
  · intro i hi
    rw [dif_pos hi]
    exact (habove _).2 ⟨_, rfl⟩
  · rw [dif_pos (le_refl k), hout]; rfl

/-- The core: removing a set `R` leaves a circuit for the restriction one gate smaller. -/
theorem nl_core (FP : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w)) (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (e : Fin (n + 1)) (pn pm pS : ℕ) (R : Finset ℕ)
    (hN : nlState n C.gates e.val pn pm pS) (hR : nlRSpec n C.gates pn pm pS R)
    (hRin : pn ∈ R ∧ pm ∈ R ∧ pS ∈ R) (hRle : ∀ j ∈ R, j ≤ pS)
    (hfan : FanInTwo C) (hH : ∃ y y' : Fin n → Bool, H y ≠ H y')
    (hF1 : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) C (Function.update x e true) =
      (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)))
    (hoe : C.output ≠ e.val)
    (X0 X1 : List Bool) (hX0 : X0.length = n + 1) (hX1 : X1.length = n + 1)
    (he1 : X1.getD e.val false = true) (hq0 : X0.getD n false = true)
    (hag : ∀ i, i < n + 1 → i ≠ e.val → X0.getD i false = X1.getD i false)
    (hF0 : nlV C.gates X0 C.output = false) (hFt : nlV C.gates X1 C.output = true) :
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool =>
      circuitFun (n + 1) C (Function.update x e true)) (C.gates.length - R.card - 1) := by
  by_contra hno
  set L := nlL n C.gates R pm pS C.output with hL
  have hlen : L.gates.length = C.gates.length - R.card :=
    nlL_len n C.gates R pm pS C.output (fun j hj => (hR j hj).1)
  have hoR : n + 1 ≤ C.output → C.output < n + 1 + C.gates.length → C.output - (n + 1) ∈ R →
      C.output = n + 1 + pS ∨ C.output = n + 1 + pn ∨ C.output = n + 1 + pm := by
    intro h1 _ h3
    rcases nl_o_above C.output hN X0 X1 hX0 hX1 he1 hag hF0 hFt hoe with h | h
    · exact Or.inl h
    · have := nlE_lt h
      have := hRle _ h3
      omega
  have hcomp : ∀ x : Fin (n + 1) → Bool, circuitFun (n + 1) L x =
      circuitFun (n + 1) C (Function.update x e true) := by
    intro x
    show nlV L.gates (List.ofFn x) L.output =
      nlV C.gates (List.ofFn (Function.update x e true)) C.output
    apply nl_outEq C.output hN hR (List.ofFn x) (List.ofFn (Function.update x e true))
      (by simp) (by simp)
    · rw [nl_ofFn_getD _ _ e.isLt]; simp
    · intro i hi hie
      rw [nl_ofFn_getD _ _ hi, nl_ofFn_getD _ _ hi]
      rw [Function.update_of_ne]
      intro h; apply hie; rw [← h]
    · exact hRin
    · exact hoe
    · exact hoR
  have hfanL : FanInTwo L := nlL_fan n C.gates R pm pS C.output hfan
  have hmin : IsMinimalCircuit (n + 1) L := by
    refine ⟨hfanL, ?_⟩
    intro D hD hDf
    by_contra hlt
    apply hno
    refine ⟨D, hD, ?_, ?_⟩
    · have : D.size < L.gates.length := by
        have : ¬ L.gates.length ≤ D.size := hlt
        omega
      rw [hlen] at this
      omega
    · intro x
      have := congrFun hDf x
      rw [hcomp] at this
      exact this
  obtain ⟨k, c, hmono, _, hout, hor, h0, hstep, _, _, habove, hw0, hw⟩ :=
    FP n L H hmin hH (fun x => by rw [hcomp]; exact hF1 x)
  have hC := nl_chain_of n L k c hmono hout hor h0 hstep habove hw0 hw
  exact nl_lift C.output hN hR hRin hRle X0 X1 hX0 hX1 he1 hq0 hag hF0 hFt hoe k _ hC

/-- The row statement of Theorem NL, both forms. -/
theorem nl_main : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w)) → ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool) (e : Fin (n + 1)) (pn pm pS : Fin C.gates.length), PEqualNP.MetaComplexity.FanInTwo C → e ≠ Fin.last n → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Function.update x e true) = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → PEqualNP.MetaComplexity.circuitFun (n + 1) C (fun i : Fin (n + 1) => decide (i = Fin.last n)) = false → (C.gates.get pn).op = PEqualNP.CircuitLowerBounds.GateOp.not → (C.gates.get pn).inputs.head? = some e.val → (C.gates.get pm).op = PEqualNP.CircuitLowerBounds.GateOp.and → n + 1 + pn.val ∈ (C.gates.get pm).inputs → (C.gates.get pS).op = PEqualNP.CircuitLowerBounds.GateOp.or → n + 1 + pm.val ∈ (C.gates.get pS).inputs → (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (e.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (e.val) ∈ (C.gates.get j).inputs) → j = pn) → (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + pn.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + pn.val) ∈ (C.gates.get j).inputs) → j = pm) → (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + pm.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + pm.val) ∈ (C.gates.get j).inputs) → j = pS) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Function.update x e true)) (C.gates.length - 4) ∧ (∀ ph : Fin C.gates.length, ph ≠ pn → n + 1 + ph.val ∈ (C.gates.get pm).inputs → (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + ph.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + ph.val) ∈ (C.gates.get j).inputs) → j = pm) → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Function.update x e true)) (C.gates.length - 5)) := by
  intro FP n C H e pn pm pS hfan he hH hF1 hF0 hn_op hn_hd hm_op hm_in hS_op hS_in rd_e rd_n rd_m
  have gd : ∀ j : Fin C.gates.length, C.gates.get j = C.gates.getD j.val nlG0 := by
    intro j; rw [nl_getD j.isLt]; rfl
  have hfan' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    exact ⟨by simpa using h1, h2⟩
  have rdc : ∀ (w : ℕ) (p : Fin C.gates.length),
      (∀ j : Fin C.gates.length, ((C.gates.get j).op = GateOp.not ∧
        (C.gates.get j).inputs.head? = some w ∨ (C.gates.get j).op ≠ GateOp.not ∧
        w ∈ (C.gates.get j).inputs) → j = p) →
      ∀ j, j < C.gates.length → nlRel (C.gates.getD j nlG0) w → j = p.val := by
    intro w p h j hj hr
    have := h ⟨j, hj⟩ (by rw [gd]; exact hr)
    rw [← this]
  have hN : nlState n C.gates e.val pn.val pm.val pS.val :=
    { fan := hfan'
      ev_lt := e.isLt
      pn_lt := pn.isLt
      pm_lt := pm.isLt
      pS_lt := pS.isLt
      n_op := by rw [← gd]; exact hn_op
      n_hd := by rw [← gd]; exact hn_hd
      m_op := by rw [← gd]; exact hm_op
      m_in := by rw [← gd]; exact hm_in
      S_op := by rw [← gd]; exact hS_op
      S_in := by rw [← gd]; exact hS_in
      rd_e := rdc _ _ rd_e
      rd_n := rdc _ _ rd_n
      rd_m := rdc _ _ rd_m }
  have hev : e.val ≠ n := by
    intro h; apply he; ext; simp [h]
  let x0 : Fin (n + 1) → Bool := fun i => decide (i = Fin.last n)
  have hX0 : (List.ofFn x0).length = n + 1 := by simp
  have hX1 : (List.ofFn (Function.update x0 e true)).length = n + 1 := by simp
  have he1 : (List.ofFn (Function.update x0 e true)).getD e.val false = true := by
    rw [nl_ofFn_getD _ _ e.isLt]; simp
  have hq0 : (List.ofFn x0).getD n false = true := by
    rw [nl_ofFn_getD _ _ (by omega)]
    simp [x0, Fin.ext_iff]
  have hag : ∀ i, i < n + 1 → i ≠ e.val →
      (List.ofFn x0).getD i false = (List.ofFn (Function.update x0 e true)).getD i false := by
    intro i hi hie
    rw [nl_ofFn_getD _ _ hi, nl_ofFn_getD _ _ hi, Function.update_of_ne]
    intro h; apply hie; rw [← h]
  have hF0' : nlV C.gates (List.ofFn x0) C.output = false := hF0
  have hFt : nlV C.gates (List.ofFn (Function.update x0 e true)) C.output = true := by
    have h := hF1 x0
    have hl : x0 (Fin.last n) = true := by simp [x0]
    rw [hl, Bool.true_or] at h
    exact h
  have hoe : C.output ≠ e.val := by
    intro ho
    obtain ⟨y, hy⟩ : ∃ y, H y = false := by
      obtain ⟨y, y', hne⟩ := hH
      cases h1 : H y
      · exact ⟨y, h1⟩
      · cases h2 : H y'
        · exact ⟨y', h2⟩
        · rw [h1, h2] at hne; exact absurd rfl hne
    let x : Fin (n + 1) → Bool := fun i => if h : i.val < n then y ⟨i.val, h⟩ else false
    have h := hF1 x
    have hl : x (Fin.last n) = false := by simp [x]
    have hc : (fun i : Fin n => x i.castSucc) = y := by
      funext i; simp [x, i.isLt]
    rw [hl, hc, hy] at h
    have h' : circuitFun (n + 1) C (Function.update x e true) = true := by
      show nlV C.gates (List.ofFn _) C.output = true
      rw [ho, nlV_input _ _ _ (by rw [List.length_ofFn]; exact e.isLt), nl_ofFn_getD _ _ e.isLt]
      simp
    rw [h'] at h
    cases h
  obtain ⟨hmS, _⟩ := nl_shape C.output hN _ _ hX0 hX1 he1 hag hF0' hFt hoe
  have hmlt := nl_m_lt C.output hN _ _ hX0 hX1 he1 hag hF0' hFt hoe
  have hnm : pn.val < pm.val := by
    have := hmlt _ hN.m_in; omega
  have core := fun (R : Finset ℕ) (hR : nlRSpec n C.gates pn.val pm.val pS.val R)
      (hRin : pn.val ∈ R ∧ pm.val ∈ R ∧ pS.val ∈ R) (hRle : ∀ j ∈ R, j ≤ pS.val) =>
    nl_core FP n C H e pn.val pm.val pS.val R hN hR hRin hRle hfan hH hF1 hoe _ _ hX0 hX1
      he1 hq0 hag hF0' hFt
  constructor
  · have h3 : ({pn.val, pm.val, pS.val} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have := core {pn.val, pm.val, pS.val}
      (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · exact ⟨pn.isLt, Or.inl rfl⟩
        · exact ⟨pm.isLt, Or.inr (Or.inl rfl)⟩
        · exact ⟨pS.isLt, Or.inr (Or.inr (Or.inl rfl))⟩)
      (by simp)
      (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        omega)
    rw [h3, show C.gates.length - 3 - 1 = C.gates.length - 4 by omega] at this
    exact this
  · intro ph hph hph_in hph_rd
    have hphv : ph.val ≠ pn.val := fun h => hph (Fin.ext h)
    have hphm : ph.val < pm.val := by
      have := hmlt _ (by rw [← gd]; exact hph_in); omega
    have h4 : ({pn.val, pm.val, pS.val, ph.val} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have := core {pn.val, pm.val, pS.val, ph.val}
      (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl | rfl
        · exact ⟨pn.isLt, Or.inl rfl⟩
        · exact ⟨pm.isLt, Or.inr (Or.inl rfl)⟩
        · exact ⟨pS.isLt, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨ph.isLt, Or.inr (Or.inr (Or.inr (rdc _ _ hph_rd)))⟩)
      (by simp)
      (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        omega)
    rw [h4, show C.gates.length - 4 - 1 = C.gates.length - 5 by omega] at this
    exact this

end PEqualNP.MetaComplexity.Helpers.RunNL
