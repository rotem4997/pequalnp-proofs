import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.ReadTwo PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_8203_73
    (nested :
      let G : SimpleGraph (Fin 11) := edgeGraph 11
        (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map
          fun k => (k / 11, k % 11))
      ∀ (C : Circuit) (a b : ℕ),
        IsLeastAO G C → TopForm G C → C.size ≤ 21 →
        a ∈ junk G C → b ∈ junk G C → a < b →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
          2 * (Ustar G C).card →
        (∃ t : Fin 2, OrReaches 11 C (opnd C b t) a) →
        (∀ v : Fin 11, v.val < 4 → ∀ t : Fin 2, side (n := 11) C a t = {v} → opnd C a t = v.val) →
        (∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
          wval C x (11 + j) = true ↔ ∀ t : Fin 2,
            (∃ v ∈ side (n := 11) C j t, x v = true) ∨
            (j = b ∧ OrReaches 11 C (opnd C j t) a ∧ wval C x (11 + a) = true)) →
        ∃ v : Fin 11, v.val < 4 ∧
          have rep : ℕ → Prop := fun j =>
            ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x k
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ rep i ∧ rep j ∧ rep k)
    (parallel :
      let G : SimpleGraph (Fin 11) := edgeGraph 11
        (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map
          fun k => (k / 11, k % 11))
      ∀ (C : Circuit) (a b : ℕ),
        IsLeastAO G C → TopForm G C → C.size ≤ 21 →
        a ∈ junk G C → b ∈ junk G C → a < b →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
          2 * (Ustar G C).card →
        (∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
          wval C x (11 + j) = true ↔ ∀ t : Fin 2, ∃ v ∈ side (n := 11) C j t, x v = true) →
        (∀ j ∈ ([a, b] : List ℕ), ∃ u ∈ side (n := 11) C j 0, ∃ w ∈ side (n := 11) C j 1, ¬ G.Adj u w) →
        (∀ v : Fin 11, v.val < 4 →
          (∀ j ∈ ([a, b] : List ℕ), ∀ t : Fin 2, side (n := 11) C j t = {v} → opnd C j t = v.val) ∧
          ((Finset.range C.size).filter fun k => v.val ∈ (gateAt C k).inputs).card ≤ 2) →
        ∃ v : Fin 11, v.val < 4 ∧
          have rep : ℕ → Prop := fun j =>
            ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x k
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ rep i ∧ rep j ∧ rep k) :
    have x1 : ℕ := (11 : ℕ); let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x2 : ℕ) => (x2 / (11 : ℕ), x2 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   PEqualNP.TopForm.IsLeastAO x2 x3 →     PEqualNP.TopForm.TopForm x2 x3 →       x3.size ≤ (21 : ℕ) →         x4 ∈ PEqualNP.TopForm.junk x2 x3 →           x5 ∈ PEqualNP.TopForm.junk x2 x3 →             x4 < x5 →               (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x3).card →                 (∀ x13 ∈ [x4, x5], ∀ (x15 : Fin x1 → Bool), PEqualNP.ReadTwo.wval x3 x15 (x1 + x13) = Bool.true ↔ ∀ (x16 : Fin (2 : ℕ)), (∃ x17 ∈ PEqualNP.TopForm.side x3 x13 x16, x15 x17 = Bool.true) ∨ x13 = x5 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x3 (PEqualNP.TopForm.opnd x3 x13 x16) x4 ∧ PEqualNP.ReadTwo.wval x3 x15 (x1 + x4) = Bool.true) →                   ∃ (x14 : Fin (11 : ℕ)),                     ↑x14 < (4 : ℕ) ∧                       have x15 : ℕ → Prop := fun (x15 : ℕ) => ∃ x16 < (11 : ℕ) + x15, ∀ (x17 : Fin (11 : ℕ) → Bool), x17 x14 = Bool.false → PEqualNP.ReadTwo.wval x3 x17 ((11 : ℕ) + x15) = PEqualNP.ReadTwo.wval x3 x17 x16;                       ∃ (x16 : ℕ) (x17 : ℕ) (x18 : ℕ), x16 < x17 ∧ x17 < x18 ∧ x18 < x3.size ∧ x15 x16 ∧ x15 x17 ∧ x15 x18 := by
  classical
  intro N G C a b hLeast hTop hSize ha hb hab hDeficit hSem
  change IsLeastAO G C at hLeast
  dsimp only [N] at hSem
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [stepW]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepW w g) i (by simp [stepW]; omega)]
      simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepW w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt gs (stepW w g) w.length (by simp [stepW])]
        simp only [List.getElem_cons_zero]
        have hstep : (stepW w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepW, List.getD_eq_getElem?_getD]
        rw [hstep]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt gs (stepW w g) i (by simp [stepW]; omega)]
          simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have hrec := ih (stepW w g) j hj'
        have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
        rw [hl] at hrec
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact hrec
  have wval_input : ∀ (D : Circuit) (x : Fin 11 → Bool) (i : Fin 11),
      wval D x i.val = x i := by
    intro D x i
    change (D.gates.foldl stepW (List.ofFn x)).getD i.val false = x i
    rw [foldl_getD_lt D.gates (List.ofFn x) i.val (by simp)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), Option.getD_some,
      List.getElem_ofFn]
  have wval_ge : ∀ (D : Circuit) (x : Fin 11 → Bool) (w : ℕ),
      11 + D.gates.length ≤ w → wval D x w = false := by
    intro D x w hw
    change (D.gates.foldl stepW (List.ofFn x)).getD w false = false
    apply getD_ge
    rw [foldl_len, List.length_ofFn]
    exact hw
  have gateAt_eq : ∀ (D : Circuit) {j : ℕ} (hj : j < D.gates.length), gateAt D j = D.gates[j] := by
    intro D j hj
    change D.gates.getD j ⟨GateOp.or, []⟩ = D.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]
  have wval_gate : ∀ (D : Circuit) (hRB : ReadsBack 11 D) (x : Fin 11 → Bool) (j : ℕ)
      (hj : j < D.gates.length),
      wval D x (11 + j) = (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => wval D x i) := by
    intro D hRB x j hj
    change (D.gates.foldl stepW (List.ofFn x)).getD (11 + j) false = _
    have hgate := foldl_getD_gate D.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hgate
    rw [hgate, gateAt_eq D hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hlt : i < 11 + j := hRB j hj i (by rwa [gateAt_eq D hj])
    rw [ite_eq_left hlt]
    rfl
  have and2 : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have or2 : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl
  have gate_pair : ∀ (D : Circuit) (hAO : IsAO2 11 D) {j : ℕ} (hj : j < D.gates.length),
      ∃ p q : ℕ, (gateAt D j).inputs = [p, q] ∧ p < 11 + j ∧ q < 11 + j ∧
        ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) := by
    intro D hAO j hj
    have hmem : gateAt D j ∈ D.gates := by rw [gateAt_eq D hj]; exact List.getElem_mem hj
    have hlen : (gateAt D j).inputs.length = 2 := hAO.2.2 _ hmem
    rcases hlist : (gateAt D j).inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
    · simp [hlist] at hlen
    · simp [hlist] at hlen
    · refine ⟨p, q, rfl, hAO.2.1 j hj p (by simp [hlist]), hAO.2.1 j hj q (by simp [hlist]), ?_⟩
      exact hAO.1 _ hmem
    · simp [hlist] at hlen
  have delete_gate : ∀ (k u : ℕ), k < C.gates.length → u < 11 + k →
      ((∀ x : Fin 11 → Bool, wval C x (11 + k) = wval C x u) ∨
        (C.output ≠ 11 + k ∧ ∀ j < C.gates.length, 11 + k ∉ (gateAt C j).inputs)) → False := by
    intro k u hk hu hcond
    let rm (w : ℕ) : ℕ := if w < 11 + k then w else if w = 11 + k then u else w - 1
    let D : Circuit := ⟨(C.gates.eraseIdx k).map (fun g => ⟨g.op, g.inputs.map rm⟩), rm C.output⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by
      simp [D, List.length_eraseIdx_of_lt hk]
    have hDget : ∀ (j : ℕ) (hj : j < D.gates.length),
        gateAt D j = ⟨(gateAt C (if j < k then j else j + 1)).op,
          (gateAt C (if j < k then j else j + 1)).inputs.map rm⟩ := by
      intro j hj
      rw [gateAt_eq D hj]
      simp only [D, List.getElem_map]
      have hj' : j < (C.gates.eraseIdx k).length := by simpa [D] using hj
      rw [List.getElem_eraseIdx]
      split_ifs with hjk
      · rw [gateAt_eq C (by omega)]
      · rw [gateAt_eq C (by omega)]
    have hDAO : IsAO2 11 D := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [D, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        exact hLeast.1.1 g0 (List.mem_of_mem_eraseIdx hg0)
      · intro j hj w hw
        rw [hDget j hj] at hw
        simp only [List.mem_map] at hw
        obtain ⟨w0, hw0, rfl⟩ := hw
        by_cases hjk : j < k
        · rw [ite_eq_left hjk] at hw0
          have hwlt : w0 < 11 + j := hLeast.1.2.1 j (by omega) w0 hw0
          simp only [rm, ite_eq_left (show w0 < 11 + k by omega)]
          omega
        · rw [ite_eq_right hjk] at hw0
          have hwlt : w0 < 11 + (j + 1) := hLeast.1.2.1 (j + 1) (by omega) w0 hw0
          dsimp only [rm]
          split_ifs <;> omega
      · intro g hg
        simp only [D, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        simpa using hLeast.1.2.2 g0 (List.mem_of_mem_eraseIdx hg0)
    have hsim : ∀ (x : Fin 11 → Bool) (w : ℕ),
        w < 11 + C.gates.length →
        ((∀ x' : Fin 11 → Bool, wval C x' (11 + k) = wval C x' u) ∨ w ≠ 11 + k) →
        wval D x (rm w) = wval C x w := by
      intro x w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hok
        by_cases hw11 : w < 11
        · have hrm : rm w = w := by simp [rm, show w < 11 + k by omega]
          rw [hrm]
          exact (wval_input D x ⟨w, hw11⟩).trans (wval_input C x ⟨w, hw11⟩).symm
        · by_cases hwk : w = 11 + k
          · subst hwk
            rcases hok with heq | hne
            · have hrm : rm (11 + k) = u := by simp [rm]
              have hrmu : rm u = u := by simp [rm, hu]
              calc wval D x (rm (11 + k)) = wval D x u := by rw [hrm]
                _ = wval D x (rm u) := by rw [hrmu]
                _ = wval C x u := ih u hu (by omega) (Or.inl heq)
                _ = wval C x (11 + k) := (heq x).symm
            · exact False.elim (hne rfl)
          · by_cases hlt : w < 11 + k
            · have hrm : rm w = w := by simp [rm, hlt]
              let j := w - 11
              have hjw : w = 11 + j := by omega
              have hjD : j < D.gates.length := by omega
              have hjC : j < C.gates.length := by omega
              rw [hrm, hjw, wval_gate D hDAO.2.1 x j hjD, wval_gate C hLeast.1.2.1 x j hjC]
              rw [hDget j hjD, ite_eq_left (show j < k by omega)]
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro w0 hw0
              have hw0lt : w0 < 11 + j := hLeast.1.2.1 j hjC w0 hw0
              exact ih w0 (by omega) (by omega) (Or.inr (by omega))
            · have hgt : 11 + k < w := by omega
              have hrm : rm w = w - 1 := by
                dsimp only [rm]
                rw [ite_eq_right (show ¬ w < 11 + k by omega),
                  ite_eq_right (show w ≠ 11 + k by omega)]
              let j := w - 12
              have hjw : w = 11 + (j + 1) := by omega
              have hjw' : w - 1 = 11 + j := by omega
              have hjD : j < D.gates.length := by omega
              have hjC : j + 1 < C.gates.length := by omega
              rw [hrm, hjw', hjw, wval_gate D hDAO.2.1 x j hjD,
                wval_gate C hLeast.1.2.1 x (j + 1) hjC]
              rw [hDget j hjD, ite_eq_right (show ¬ j < k by omega)]
              simp only [List.map_map]
              congr 1
              apply List.map_congr_left
              intro w0 hw0
              have hw0lt : w0 < 11 + (j + 1) := hLeast.1.2.1 (j + 1) hjC w0 hw0
              apply ih w0 (by omega) (by omega)
              rcases hcond with heq | ⟨_, hnoread⟩
              · exact Or.inl heq
              · exact Or.inr fun he => hnoread (j + 1) hjC (he ▸ hw0)
    have hfun : circuitFun 11 D = graphFun G ∅ := by
      rw [← hLeast.2.1]
      funext x
      change wval D x (rm C.output) = wval C x C.output
      by_cases hout : C.output < 11 + C.gates.length
      · apply hsim x C.output hout
        rcases hcond with heq | ⟨hne, _⟩
        · exact Or.inl heq
        · exact Or.inr hne
      · have hrm : 11 + D.gates.length ≤ rm C.output := by
          dsimp only [rm]
          rw [ite_eq_right (show ¬ C.output < 11 + k by omega),
            ite_eq_right (show C.output ≠ 11 + k by omega)]
          omega
        rw [wval_ge D x _ hrm, wval_ge C x _ (by omega)]
    have hmin := hLeast.2.2 D hDAO hfun
    change C.gates.length ≤ D.gates.length at hmin
    omega
  have exists_reader : ∀ (k : ℕ), k < C.gates.length → C.output ≠ 11 + k →
      ∃ r ∈ readers 11 C k, k < r ∧ r < C.gates.length := by
    intro k hk hout
    by_contra! hnone
    apply delete_gate k 0 hk (by omega)
    refine Or.inr ⟨hout, fun j hj hmem => ?_⟩
    have hmemR : j ∈ readers 11 C k := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hmem⟩
    have hlt := hLeast.1.2.1 j hj (11 + k) hmem
    exact Nat.not_lt_of_ge (hnone j hmemR (by omega)) hj
  have zero_not_output : ∀ (v : Fin 11), v.val < 4 → ∀ (k : ℕ),
      (∀ x : Fin 11 → Bool, x v = false → wval C x (11 + k) = false) → C.output ≠ 11 + k := by
    intro v hv k hzero heq
    let x0 : Fin 11 → Bool := fun i => decide (i.val = 4 ∨ i.val = 8)
    have hxv : x0 v = false := by
      simp only [x0, decide_eq_false_iff_not]
      omega
    have hval0 : wval C x0 C.output = false := by
      rw [heq]
      exact hzero x0 hxv
    have hfun : circuitFun 11 C x0 = graphFun G ∅ x0 := congrFun hLeast.2.1 x0
    have hge : graphFun G ∅ x0 = true := by
      change (decide (∃ a ∈ (∅ : Finset (Fin 11)), x0 a = true) ||
        decide (∃ u v : Fin 11, G.Adj u v ∧ x0 u = true ∧ x0 v = true)) = true
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      refine ⟨(4 : Fin 11), (8 : Fin 11), ?_, ?_, ?_⟩
      · show G.Adj (4 : Fin 11) (8 : Fin 11)
        dsimp only [G]
        decide
      · simp [x0]
      · simp [x0]
    have : wval C x0 C.output = true := hfun.trans hge
    rw [hval0] at this
    exact Bool.noConfusion this
  have vanishes_of_zero_input : ∀ (v : Fin 11) (j w0 : ℕ),
      j < C.gates.length → w0 ∈ (gateAt C j).inputs →
      (∀ x : Fin 11 → Bool, x v = false → wval C x w0 = false) →
      ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x k := by
    intro v j w0 hj hw0 hzero
    obtain ⟨p, q, hpq, hp, hq, hop⟩ := gate_pair C hLeast.1 hj
    rw [hpq, List.mem_cons, List.mem_singleton] at hw0
    rcases hop with hand | hor
    · refine ⟨v.val, by omega, fun x hxv => ?_⟩
      rw [wval_gate C hLeast.1.2.1 x j hj, hand, hpq, List.map_cons, List.map_singleton, and2,
        wval_input C x v, hxv]
      rcases hw0 with rfl | rfl
      · rw [hzero x hxv]; rfl
      · rw [hzero x hxv]; simp
    · rcases hw0 with rfl | rfl
      · refine ⟨q, hq, fun x hxv => ?_⟩
        rw [wval_gate C hLeast.1.2.1 x j hj, hor, hpq, List.map_cons, List.map_singleton, or2,
          hzero x hxv, Bool.false_or]
      · refine ⟨p, hp, fun x hxv => ?_⟩
        rw [wval_gate C hLeast.1.2.1 x j hj, hor, hpq, List.map_cons, List.map_singleton, or2,
          hzero x hxv, Bool.or_false]
  have three_from_distinct : ∀ (v : Fin 11), v.val < 4 →
      ∀ (x y z : ℕ), x ≠ y → x ≠ z → y ≠ z →
      x < C.size → y < C.size → z < C.size →
      (∃ k < 11 + x, ∀ inp : Fin 11 → Bool, inp v = false → wval C inp (11 + x) = wval C inp k) →
      (∃ k < 11 + y, ∀ inp : Fin 11 → Bool, inp v = false → wval C inp (11 + y) = wval C inp k) →
      (∃ k < 11 + z, ∀ inp : Fin 11 → Bool, inp v = false → wval C inp (11 + z) = wval C inp k) →
      ∃ v0 : Fin 11, v0.val < 4 ∧
        have rep : ℕ → Prop := fun j =>
          ∃ k < 11 + j, ∀ inp : Fin 11 → Bool, inp v0 = false → wval C inp (11 + j) = wval C inp k
        ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ rep i ∧ rep j ∧ rep k := by
    intro v hv x y z hxy hxz hyz hx hy hz px py pz
    refine ⟨v, hv, ?_⟩
    rcases lt_or_gt_of_ne hxy with h1 | h1
    · rcases lt_or_gt_of_ne hyz with h2 | h2
      · exact ⟨x, y, z, h1, h2, hz, px, py, pz⟩
      · rcases lt_or_gt_of_ne hxz with h3 | h3
        · exact ⟨x, z, y, h3, h2, hy, px, pz, py⟩
        · exact ⟨z, x, y, h3, h1, hy, pz, px, py⟩
    · rcases lt_or_gt_of_ne hxz with h2 | h2
      · exact ⟨y, x, z, h1, h2, hz, py, px, pz⟩
      · rcases lt_or_gt_of_ne hyz with h3 | h3
        · exact ⟨y, z, x, h3, h2, hx, py, pz, px⟩
        · exact ⟨z, y, x, h3, h1, hx, pz, py, px⟩
  have orReaches_le : ∀ (w o : ℕ), OrReaches 11 C w o → 11 + o ≤ w := by
    have step_inv : ∀ (gs : List Gate) (cs : List (List ℕ)),
        (∀ i < cs.length, ∀ o ∈ cs.getD i [], o ≤ i) →
        ∀ i < (gs.foldl (orStep 11) cs).length,
          ∀ o ∈ (gs.foldl (orStep 11) cs).getD i [], o ≤ i := by
      intro gs
      induction gs with
      | nil => intro cs hcs; exact hcs
      | cons g gs ih =>
        intro cs hcs
        rw [List.foldl_cons]
        apply ih
        intro i hi o ho
        have hlen : (orStep 11 cs g).length = cs.length + 1 := by
          change (cs ++ [_]).length = cs.length + 1
          simp
        by_cases hic : i < cs.length
        · have hget : (orStep 11 cs g).getD i [] = cs.getD i [] := by
            change (cs ++ [_]).getD i [] = cs.getD i []
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hic]
          rw [hget] at ho
          exact hcs i hic o ho
        · have hieq : i = cs.length := by omega
          subst hieq
          have hget : (orStep 11 cs g).getD cs.length [] =
              cs.length :: (if g.op = GateOp.or then
                (g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
                  (fun w => cs.getD (w - 11) []) else []) := by
            change (cs ++ [_]).getD cs.length [] = _
            simp [List.getD_eq_getElem?_getD]
          rw [hget, List.mem_cons] at ho
          rcases ho with rfl | ho
          · exact le_rfl
          · split_ifs at ho with hgor
            · rw [List.mem_flatMap] at ho
              obtain ⟨w, hw, how⟩ := ho
              rw [List.mem_filter] at hw
              have hwb : 11 ≤ w ∧ w < 11 + cs.length := of_decide_eq_true hw.2
              have hle := hcs (w - 11) (by omega) o how
              omega
            · simp at ho
    intro w o hor
    have hw : 11 ≤ w := hor.1
    have ho : o ∈ (orSets 11 C).getD (w - 11) [] := hor.2
    by_cases hlt : w - 11 < (orSets 11 C).length
    · have hle := step_inv C.gates [] (by intro i hi; simp at hi) (w - 11) hlt o ho
      omega
    · have hnil : (orSets 11 C).getD (w - 11) [] = [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
      rw [hnil] at ho
      simp at ho
  have dirty_nonedge : ∀ (j : ℕ), j ∈ junk G C →
      (∀ x : Fin 11 → Bool, wval C x (11 + j) = true ↔
        ∀ t : Fin 2, ∃ v ∈ side (n := 11) C j t, x v = true) →
      ∃ u ∈ side (n := 11) C j 0, ∃ w ∈ side (n := 11) C j 1, ¬ G.Adj u w := by
    intro j hj hbj
    have hdir : IsDirtyAnd 11 G C j := (Finset.mem_filter.mp hj).2
    obtain ⟨x, hxj, hxf⟩ := hdir.2.2
    have htrue : wval C x (11 + j) = true := hxj
    have hboth := (hbj x).mp htrue
    obtain ⟨u, hu, hxu⟩ := hboth 0
    obtain ⟨w, hw, hxw⟩ := hboth 1
    refine ⟨u, hu, w, hw, fun hadj => ?_⟩
    have hgt : graphFun G ∅ x = true := by
      change (decide (∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ||
        decide (∃ u v : Fin 11, G.Adj u v ∧ x u = true ∧ x v = true)) = true
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      exact ⟨u, w, hadj, hxu, hxw⟩
    rw [hxf] at hgt
    exact Bool.noConfusion hgt
  have singleton_rigid_or_win : ∀ (j : ℕ), j ∈ junk G C →
      (∀ x : Fin 11 → Bool, wval C x (11 + j) = true ↔
        ∀ t : Fin 2, ∃ v ∈ side (n := 11) C j t, x v = true) →
      ∀ (v : Fin 11), v.val < 4 → ∀ (t : Fin 2),
      side (n := 11) C j t = {v} → opnd C j t ≠ v.val →
      ∃ v0 : Fin 11, v0.val < 4 ∧
        have rep : ℕ → Prop := fun k =>
          ∃ i < 11 + k, ∀ x : Fin 11 → Bool, x v0 = false → wval C x (11 + k) = wval C x i
        ∃ i k m : ℕ, i < k ∧ k < m ∧ m < C.size ∧ rep i ∧ rep k ∧ rep m := by
    intro j hj hbj v hv t hside hne
    have hjlt : j < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hvmem : v ∈ side (n := 11) C j t := by rw [hside]; simp
    have horin : (v : ℕ) = opnd C j t ∨ ∃ k < C.gates.length,
        OrReaches 11 C (opnd C j t) k ∧ (gateAt C k).op = GateOp.or ∧
        (v : ℕ) ∈ (gateAt C k).inputs := by
      let : DecidableEq GateOp := gateOpDecEq
      exact (Finset.mem_filter.mp hvmem).2
    rcases horin with heq | ⟨o, holt, hreach, hoop, hvino⟩
    · exact False.elim (hne heq.symm)
    · have hole : 11 + o ≤ opnd C j t := orReaches_le (opnd C j t) o hreach
      obtain ⟨p, q, hpq, hp, hq, _⟩ := gate_pair C hLeast.1 hjlt
      have hopnd_lt : opnd C j t < 11 + j := by
        unfold opnd
        rw [hpq]
        fin_cases t
        · simpa using hp
        · simpa using hq
      have hoj : o < j := by omega
      have hjzero : ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = false := by
        intro x hxv
        cases hval : wval C x (11 + j) with
        | false => rfl
        | true =>
          obtain ⟨u, hu, hxu⟩ := ((hbj x).mp hval) t
          rw [hside, Finset.mem_singleton] at hu
          subst hu
          rw [hxv] at hxu
          exact Bool.noConfusion hxu
      have hjout : C.output ≠ 11 + j := zero_not_output v hv j hjzero
      obtain ⟨r, hrR, hjr, hrlt⟩ := exists_reader j hjlt hjout
      have hrin : 11 + j ∈ (gateAt C r).inputs := (Finset.mem_filter.mp hrR).2
      have hpo := vanishes_of_zero_input v o v.val holt hvino (fun x hxv => by rw [wval_input C x v, hxv])
      have hpj : ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x k :=
        ⟨v.val, by omega, fun x hxv => by rw [hjzero x hxv, wval_input C x v, hxv]⟩
      have hpr := vanishes_of_zero_input v r (11 + j) hrlt hrin hjzero
      exact ⟨v, hv, o, j, r, hoj, hjr, hrlt, hpo, hpj, hpr⟩
  have hsemA : ∀ x : Fin 11 → Bool, wval C x (11 + a) = true ↔
      ∀ t : Fin 2, ∃ v ∈ side (n := 11) C a t, x v = true := by
    intro x
    have h0 := hSem a (by simp) x
    have hne : a ≠ b := Nat.ne_of_lt hab
    simpa [hne] using h0
  by_cases hnest : ∃ t : Fin 2, OrReaches 11 C (opnd C b t) a
  · by_cases hrigA : ∀ v : Fin 11, v.val < 4 → ∀ t : Fin 2,
        side (n := 11) C a t = {v} → opnd C a t = v.val
    · exact nested C a b hLeast hTop hSize ha hb hab hDeficit hnest hrigA hSem
    · push Not at hrigA
      obtain ⟨v, hv, t, hside, hne⟩ := hrigA
      exact singleton_rigid_or_win a ha hsemA v hv t hside hne
  · push Not at hnest
    have hsemB : ∀ x : Fin 11 → Bool, wval C x (11 + b) = true ↔
        ∀ t : Fin 2, ∃ v ∈ side (n := 11) C b t, x v = true := by
      intro x
      have h0 := hSem b (by simp) x
      rw [h0]
      constructor
      · intro h t
        rcases h t with h1 | ⟨_, hor, _⟩
        · exact h1
        · exact False.elim (hnest t hor)
      · intro h t
        exact Or.inl (h t)
    have hsemAB : ∀ j ∈ ([a, b] : List ℕ), ∀ x : Fin 11 → Bool,
        wval C x (11 + j) = true ↔ ∀ t : Fin 2, ∃ v ∈ side (n := 11) C j t, x v = true := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with hja | hjb
      · rw [hja]; exact hsemA
      · rw [hjb]; exact hsemB
    by_cases hfan : ∀ v : Fin 11, v.val < 4 →
        ((Finset.range C.size).filter fun k => v.val ∈ (gateAt C k).inputs).card ≤ 2
    · by_cases hrigAB : ∀ v : Fin 11, v.val < 4 → ∀ j ∈ ([a, b] : List ℕ),
          ∀ t : Fin 2, side (n := 11) C j t = {v} → opnd C j t = v.val
      · refine parallel C a b hLeast hTop hSize ha hb hab hDeficit hsemAB ?_ ?_
        · intro j hj
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with hja | hjb
          · rw [hja]; exact dirty_nonedge a ha hsemA
          · rw [hjb]; exact dirty_nonedge b hb hsemB
        · intro v hv
          exact ⟨hrigAB v hv, hfan v hv⟩
      · push Not at hrigAB
        obtain ⟨v, hv, j, hjmem, t, hside, hne⟩ := hrigAB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hjmem
        rcases hjmem with hja | hjb
        · rw [hja] at hside hne; exact singleton_rigid_or_win a ha hsemA v hv t hside hne
        · rw [hjb] at hside hne; exact singleton_rigid_or_win b hb hsemB v hv t hside hne
    · push Not at hfan
      obtain ⟨v, hv, hcard3⟩ := hfan
      obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp hcard3
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      have hk' := Finset.mem_filter.mp hk
      exact three_from_distinct v hv i j k hij hik hjk
        (Finset.mem_range.mp hi'.1) (Finset.mem_range.mp hj'.1) (Finset.mem_range.mp hk'.1)
        (vanishes_of_zero_input v i v.val (Finset.mem_range.mp hi'.1) hi'.2
          (fun x hxv => by rw [wval_input C x v, hxv]))
        (vanishes_of_zero_input v j v.val (Finset.mem_range.mp hj'.1) hj'.2
          (fun x hxv => by rw [wval_input C x v, hxv]))
        (vanishes_of_zero_input v k v.val (Finset.mem_range.mp hk'.1) hk'.2
          (fun x hxv => by rw [wval_input C x v, hxv]))
