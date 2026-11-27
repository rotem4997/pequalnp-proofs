import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3791_1
    (topOr : ∀ (C : Circuit) (w1 a b : ℕ), Monotone2 C → ReadsBack 26 C →
      w1 < 26 + C.size → a < 26 + C.size → b < 26 + C.size → a ≠ b →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun p l : Fin 13 =>
        (List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun u : Fin 13 => decide (u = l)
      let N := fun Q : Finset (Fin 13) =>
        (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun u : Fin 13 => decide (∀ r ∈ Q, r - u ∉ D)
      let good := fun Q : Finset (Fin 13) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter fun u => u - k ∈ D).card ≤ 2
      let val := fun w x => (C.wires x).getD w false
      let w2v := fun x => val a x || val b x
      (∀ p l : Fin 13, p - l ∈ D → val w1 (P p l) = true ∨ w2v (P p l) = true) →
      (∀ Q : Finset (Fin 13), good Q → val w1 (N Q) = false ∧ w2v (N Q) = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ val w1 (P p l) = true ∧ w2v (P p l) = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ w2v (P p l) = true ∧ val w1 (P p l) = false) →
      62 ≤ C.size)
    (topAnd : ∀ (C : Circuit) (w1 a b : ℕ), Monotone2 C → ReadsBack 26 C →
      w1 < 26 + C.size → a < 26 + C.size → b < 26 + C.size → a ≠ b →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun p l : Fin 13 =>
        (List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun u : Fin 13 => decide (u = l)
      let N := fun Q : Finset (Fin 13) =>
        (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun u : Fin 13 => decide (∀ r ∈ Q, r - u ∉ D)
      let good := fun Q : Finset (Fin 13) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter fun u => u - k ∈ D).card ≤ 2
      let val := fun w x => (C.wires x).getD w false
      let w2v := fun x => val a x && val b x
      (∀ p l : Fin 13, p - l ∈ D → val w1 (P p l) = true ∨ w2v (P p l) = true) →
      (∀ Q : Finset (Fin 13), good Q → val w1 (N Q) = false ∧ w2v (N Q) = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ val w1 (P p l) = true ∧ w2v (P p l) = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ w2v (P p l) = true ∧ val w1 (P p l) = false) →
      62 ≤ C.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           ((26 : ℕ) ≤ x2 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x3 (x2 - (26 : ℕ))) →             ((26 : ℕ) ≤ x3 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x2 (x3 - (26 : ℕ))) →               have x10 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x11 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x11 x12 : Fin (13 : ℕ)) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x11)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x12);               have x12 : Finset (Fin (13 : ℕ)) → List Bool := fun (x12 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 ∈ x12)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (∀ x14 ∈ x12, x14 - x13 ∉ x10);               have x13 : Finset (Fin (13 : ℕ)) → Prop := fun (x13 : Finset (Fin (13 : ℕ))) => x13.card = (4 : ℕ) ∧ ∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x13 | x15 - x14 ∈ x10}.card ≤ (2 : ℕ);               have x14 : ℕ → List Bool → Bool := fun (x14 : ℕ) (x15 : List Bool) => (x1.wires x15).getD x14 Bool.false;               (∀ (x15 x16 : Fin (13 : ℕ)), x15 - x16 ∈ x10 → x14 x2 (x11 x15 x16) = Bool.true ∨ x14 x3 (x11 x15 x16) = Bool.true) → (∀ (x16 : Finset (Fin (13 : ℕ))), x13 x16 → x14 x2 (x12 x16) = Bool.false ∧ x14 x3 (x12 x16) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x10 ∧ x14 x2 (x11 x17 x18) = Bool.true ∧ x14 x3 (x11 x17 x18) = Bool.false) → (∃ (x18 : Fin (13 : ℕ)) (x19 : Fin (13 : ℕ)), x18 - x19 ∈ x10 ∧ x14 x3 (x11 x18 x19) = Bool.true ∧ x14 x2 (x11 x18 x19) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let P (p l : Fin 13) : List Bool :=
    (List.ofFn fun u : Fin 13 => decide (u = p)) ++ List.ofFn fun u : Fin 13 => decide (u = l)
  let N (Q : Finset (Fin 13)) : List Bool :=
    (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) ++ List.ofFn fun u : Fin 13 => decide (∀ r ∈ Q, r - u ∉ D)
  let good (Q : Finset (Fin 13)) : Prop :=
    Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter fun u => u - k ∈ D).card ≤ 2
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_def (C : Circuit) (xs : List Bool) : C.wires xs = C.gates.foldl step xs := rfl
  have gateAt_def (A : Circuit) (j : ℕ) : gateAt A j = A.gates.getD j ⟨GateOp.or, []⟩ := rfl
  have fold_len (gs : List Gate) : ∀ ws : List Bool, (gs.foldl step ws).length = ws.length + gs.length := by
    induction gs with
    | nil => intro ws; rfl
    | cons g gs ih =>
      intro ws
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, show (step ws g).length = ws.length + 1 by simp [step]]
      omega
  have fold_prefix (gs : List Gate) : ∀ (ws : List Bool) (i : ℕ), i < ws.length →
      (gs.foldl step ws).getD i false = ws.getD i false := by
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      simp only [List.foldl_cons]
      rw [ih _ _ (by simp [step]; omega)]
      exact List.getD_append ws _ _ i hi
  have fold_append_getD (pre post : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length + pre.length) :
      ((pre ++ post).foldl step ws).getD i false = (pre.foldl step ws).getD i false := by
    rw [List.foldl_append]
    apply fold_prefix
    rw [fold_len]
    exact hi
  have len_P (p l : Fin 13) : (P p l).length = 26 := by simp [P]
  have len_N (Q : Finset (Fin 13)) : (N Q).length = 26 := by simp [N]
  have q0_good : good ({0, 1, 2, 5} : Finset (Fin 13)) := by decide
  have bad_input_wire : ∀ w : Fin 26, ∃ Q : Finset (Fin 13), good Q ∧ (N Q).getD w.val false = true := by
    have check_all : ∀ w : Fin 26,
        let Q : Finset (Fin 13) :=
          if h : w.val < 13 then
            let p : Fin 13 := ⟨w.val, h⟩
            {p, p + 1, p + 2, p + 5}
          else
            let l : Fin 13 := ⟨w.val - 13, by omega⟩
            {l - 3, l - 2, l - 1, l + 2}
        good Q ∧ (N Q).getD w.val false = true := by
      decide
    intro w
    exact ⟨_, (check_all w).1, (check_all w).2⟩
  have step_no_input (C : Circuit) (w1 w2 : ℕ)
      (hCov : ∀ p l : Fin 13, p - l ∈ D → (C.wires (P p l)).getD w1 false = true ∨ (C.wires (P p l)).getD w2 false = true)
      (hRej : ∀ Q : Finset (Fin 13), good Q → (C.wires (N Q)).getD w1 false = false ∧ (C.wires (N Q)).getD w2 false = false) :
      ∀ w : ℕ, (∀ Q : Finset (Fin 13), good Q → (C.wires (N Q)).getD w false = false) → 26 ≤ w := by
    intro w hw
    by_contra hlt
    have hlt26 : w < 26 := Nat.lt_of_not_ge hlt
    obtain ⟨Q, hQgood, hQtrue⟩ := bad_input_wire ⟨w, hlt26⟩
    have hfalse := hw Q hQgood
    rw [wires_def, fold_prefix C.gates (N Q) w (by rw [len_N]; exact hlt26)] at hfalse
    rw [hQtrue] at hfalse
    contradiction
  have main_ind : ∀ (n : ℕ) (C : Circuit) (w1 w2 : ℕ),
      C.size = n → Monotone2 C → ReadsBack 26 C →
      w1 < 26 + C.size → w2 < 26 + C.size →
      (∀ p l : Fin 13, p - l ∈ D → (C.wires (P p l)).getD w1 false = true ∨ (C.wires (P p l)).getD w2 false = true) →
      (∀ Q : Finset (Fin 13), good Q → (C.wires (N Q)).getD w1 false = false ∧ (C.wires (N Q)).getD w2 false = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ (C.wires (P p l)).getD w1 false = true ∧ (C.wires (P p l)).getD w2 false = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ (C.wires (P p l)).getD w2 false = true ∧ (C.wires (P p l)).getD w1 false = false) →
      63 ≤ C.size := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro C w1 w2 hn hMono hBack hw1 hw2 hCov hRej hSep1 hSep2
      have hw1_26 : 26 ≤ w1 := step_no_input C w1 w2 hCov hRej w1 (fun Q hQ => (hRej Q hQ).1)
      have hw2_26 : 26 ≤ w2 := step_no_input C w1 w2 hCov hRej w2 (fun Q hQ => (hRej Q hQ).2)
      have hne : w1 ≠ w2 := by
        intro heq
        subst heq
        obtain ⟨p, l, _, ht, hf⟩ := hSep1
        rw [ht] at hf
        contradiction
      have peel_ordered : ∀ (u v : ℕ), 26 ≤ u → u < v → v < 26 + C.size →
          (∀ p l : Fin 13, p - l ∈ D → (C.wires (P p l)).getD u false = true ∨ (C.wires (P p l)).getD v false = true) →
          (∀ Q : Finset (Fin 13), good Q → (C.wires (N Q)).getD u false = false ∧ (C.wires (N Q)).getD v false = false) →
          (∃ p l : Fin 13, p - l ∈ D ∧ (C.wires (P p l)).getD u false = true ∧ (C.wires (P p l)).getD v false = false) →
          (∃ p l : Fin 13, p - l ∈ D ∧ (C.wires (P p l)).getD v false = true ∧ (C.wires (P p l)).getD u false = false) →
          63 ≤ C.size := by
        intro u v hu huv hv hCov_uv hRej_uv hSep_uv hSep_vu
        by_cases htrim : v + 1 < 26 + C.size
        · let k := v - 26 + 1
          have hk_lt : k < C.size := by omega
          let pre := C.gates.take k
          let post := C.gates.drop k
          have hsplit : C.gates = pre ++ post := (List.take_append_drop k C.gates).symm
          let C' : Circuit := ⟨pre, C.output⟩
          have hC'size : C'.size = k := List.length_take_of_le (le_of_lt hk_lt)
          have hC'mono : Monotone2 C' := fun g hg => hMono g (List.mem_of_mem_take hg)
          have hC'back : ReadsBack 26 C' := by
            intro j hj i hi
            have hj_lt : j < k := by rw [← hC'size]; exact hj
            have hgj : gateAt C' j = gateAt C j := by
              rw [gateAt_def, gateAt_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
              change ((C.gates.take k)[j]?).getD ⟨GateOp.or, []⟩ = (C.gates[j]?).getD ⟨GateOp.or, []⟩
              rw [List.getElem?_take_of_lt hj_lt]
            rw [hgj] at hi
            exact hBack j (lt_trans hj_lt hk_lt) i hi
          have hu_C' : u < 26 + C'.size := by omega
          have hv_C' : v < 26 + C'.size := by omega
          have agree (w : ℕ) (hw : w < 26 + C'.size) (ws : List Bool) (hws : ws.length = 26) :
              (C'.wires ws).getD w false = (C.wires ws).getD w false := by
            rw [wires_def, wires_def, hsplit]
            exact (fold_append_getD pre post ws w (by rw [hws]; exact hw)).symm
          have h63 : 63 ≤ C'.size := ih k (by omega) C' u v hC'size hC'mono hC'back hu_C' hv_C'
            (fun p l hpl => by simpa only [agree u hu_C' (P p l) (len_P p l), agree v hv_C' (P p l) (len_P p l)] using hCov_uv p l hpl)
            (fun Q hQ => by simpa only [agree u hu_C' (N Q) (len_N Q), agree v hv_C' (N Q) (len_N Q)] using hRej_uv Q hQ)
            (by obtain ⟨p, l, h1, h2, h3⟩ := hSep_uv; exact ⟨p, l, h1, (agree u hu_C' (P p l) (len_P p l)).trans h2, (agree v hv_C' (P p l) (len_P p l)).trans h3⟩)
            (by obtain ⟨p, l, h1, h2, h3⟩ := hSep_vu; exact ⟨p, l, h1, (agree v hv_C' (P p l) (len_P p l)).trans h2, (agree u hu_C' (P p l) (len_P p l)).trans h3⟩)
          omega
        · have hv_last : v + 1 = 26 + C.size := by omega
          have hgates_ne : C.gates ≠ [] := by
            intro hnil
            have hsz : C.size = 0 := by change C.gates.length = 0; rw [hnil]; rfl
            omega
          let pre := C.gates.dropLast
          let g := C.gates.getLast hgates_ne
          have hsplit : C.gates = pre ++ [g] := (List.dropLast_append_getLast hgates_ne).symm
          let C'' : Circuit := ⟨pre, C.output⟩
          have hC''size : C.size = C''.size + 1 := by
            change C.gates.length = pre.length + 1
            rw [hsplit]; simp
          have hv_idx : v = 26 + C''.size := by omega
          have hu_C'' : u < 26 + C''.size := by omega
          have hC''mono : Monotone2 C'' := fun x hx => hMono x (by rw [hsplit]; exact List.mem_append_left _ hx)
          have hC''back : ReadsBack 26 C'' := by
            intro j hj i hi
            have hj_pre : j < pre.length := hj
            have hj_lt : j < C.gates.length := by
              change C.gates.length = pre.length + 1 at hC''size
              omega
            have hgj : gateAt C'' j = gateAt C j := by
              rw [gateAt_def, gateAt_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
              change (pre[j]?).getD ⟨GateOp.or, []⟩ = (C.gates[j]?).getD ⟨GateOp.or, []⟩
              have heq1 : pre[j]? = some pre[j] := List.getElem?_eq_getElem hj_pre
              have heq2 : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj_lt
              have hpre_el : pre[j] = C.gates[j] := by
                have heql := congrArg (fun (l : List Gate) => l[j]?) hsplit
                rw [List.getElem?_append_left hj_pre, heq1, heq2] at heql
                exact Option.some.inj heql.symm
              rw [heq1, heq2, hpre_el]
            rw [hgj] at hi
            exact hBack j hj_lt i hi
          have hg_mem : g ∈ C.gates := List.getLast_mem hgates_ne
          have hg_mono := hMono g hg_mem
          have hg_back : ∀ i ∈ g.inputs, i < 26 + C''.size := by
            intro i hi
            have hidx : C''.size < C.gates.length := by
              change C.gates.length = pre.length + 1 at hC''size
              change pre.length < C.gates.length
              omega
            have hgg : gateAt C C''.size = g := by
              rw [gateAt_def, List.getD_eq_getElem?_getD]
              have heql := congrArg (fun (l : List Gate) => l[pre.length]?) hsplit
              have heq_r : (pre ++ [g])[pre.length]? = some g := by
                rw [List.getElem?_append_right (le_refl _)]
                simp
              change C.gates[pre.length]? = (pre ++ [g])[pre.length]? at heql
              rw [heq_r] at heql
              change (C.gates[pre.length]?).getD ⟨GateOp.or, []⟩ = g
              rw [heql, Option.getD_some]
            have := hBack C''.size hidx i (by rw [hgg]; exact hi)
            omega
          have agree_u (ws : List Bool) (hws : ws.length = 26) :
              (C''.wires ws).getD u false = (C.wires ws).getD u false := by
            rw [wires_def, wires_def, hsplit]
            exact (fold_append_getD pre [g] ws u (by rw [hws]; exact hu_C'')).symm
          have eval_v (ws : List Bool) (hws : ws.length = 26) :
              (C.wires ws).getD v false = g.op.eval (g.inputs.map fun i => (C''.wires ws).getD i false) := by
            rw [wires_def, hsplit, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hplen : (pre.foldl step ws).length = 26 + C''.size := by
              rw [fold_len, hws]; rfl
            change ((pre.foldl step ws) ++ [g.op.eval (g.inputs.map fun i => (pre.foldl step ws).getD i false)]).getD v false = _
            rw [hv_idx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hplen, Nat.sub_self]
            simp [wires_def, C'']
          have eval_and0 : GateOp.and.eval [] = true := rfl
          have eval_or0 : GateOp.or.eval [] = false := rfl
          have eval_and1 (b : Bool) : GateOp.and.eval [b] = b := by cases b <;> rfl
          have eval_or1 (b : Bool) : GateOp.or.eval [b] = b := by cases b <;> rfl
          have eval_and2 (b1 b2 : Bool) : GateOp.and.eval [b1, b2] = (b1 && b2) := by
            cases b1 <;> cases b2 <;> rfl
          have eval_or2 (b1 b2 : Bool) : GateOp.or.eval [b1, b2] = (b1 || b2) := by
            cases b1 <;> cases b2 <;> rfl
          have reduce_single (a : ℕ) (ha : a < 26 + C''.size)
              (heq : ∀ ws : List Bool, ws.length = 26 → (C.wires ws).getD v false = (C''.wires ws).getD a false) :
              63 ≤ C.size := by
            have h63 : 63 ≤ C''.size := ih C''.size (by omega) C'' u a rfl hC''mono hC''back hu_C'' ha
              (fun p l hpl => by simpa only [agree_u (P p l) (len_P p l), heq (P p l) (len_P p l)] using hCov_uv p l hpl)
              (fun Q hQ => by simpa only [agree_u (N Q) (len_N Q), heq (N Q) (len_N Q)] using hRej_uv Q hQ)
              (by obtain ⟨p, l, h1, h2, h3⟩ := hSep_uv; exact ⟨p, l, h1, (agree_u (P p l) (len_P p l)).trans h2, (heq (P p l) (len_P p l)).symm.trans h3⟩)
              (by obtain ⟨p, l, h1, h2, h3⟩ := hSep_vu; exact ⟨p, l, h1, (heq (P p l) (len_P p l)).symm.trans h2, (agree_u (P p l) (len_P p l)).trans h3⟩)
            omega
          rcases hg_mono with ⟨hop, hlen⟩
          have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
          cases hgin : g.inputs with
          | nil =>
            rcases hop' with hand | hor
            · have hf := (hRej_uv _ q0_good).2
              rw [eval_v (N {0, 1, 2, 5}) (len_N _), hgin, hand, List.map_nil, eval_and0] at hf
              exact Bool.noConfusion hf
            · obtain ⟨p, l, _, ht, _⟩ := hSep_vu
              rw [eval_v (P p l) (len_P p l), hgin, hor, List.map_nil, eval_or0] at ht
              exact Bool.noConfusion ht
          | cons a rest =>
            cases rest with
            | nil =>
              have ha : a < 26 + C''.size := hg_back a (by rw [hgin]; simp)
              apply reduce_single a ha
              intro ws hws
              rw [eval_v ws hws, hgin]
              rcases hop' with hand | hor
              · rw [hand, List.map_cons, List.map_nil, eval_and1]
              · rw [hor, List.map_cons, List.map_nil, eval_or1]
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                have ha : a < 26 + C''.size := hg_back a (by rw [hgin]; simp)
                have hb : b < 26 + C''.size := hg_back b (by rw [hgin]; simp)
                by_cases hab : a = b
                · rw [← hab] at hgin
                  apply reduce_single a ha
                  intro ws hws
                  rw [eval_v ws hws, hgin]
                  rcases hop' with hand | hor
                  · simp [hand, eval_and2]
                  · simp [hor, eval_or2]
                · rcases hop' with hand | hor
                  · have h62 : 62 ≤ C''.size := topAnd C'' u a b hC''mono hC''back hu_C'' ha hb hab
                      (fun p l hpl => by
                        have h := hCov_uv p l hpl
                        rw [← agree_u (P p l) (len_P p l), eval_v (P p l) (len_P p l), hgin, hand] at h
                        simpa only [List.map_cons, List.map_nil, eval_and2] using h)
                      (fun Q hQ => by
                        have h := hRej_uv Q hQ
                        rw [← agree_u (N Q) (len_N Q), eval_v (N Q) (len_N Q), hgin, hand] at h
                        simpa only [List.map_cons, List.map_nil, eval_and2] using h)
                      (by
                        obtain ⟨p, l, hpl, ht, hf⟩ := hSep_uv
                        rw [← agree_u (P p l) (len_P p l)] at ht
                        rw [eval_v (P p l) (len_P p l), hgin, hand] at hf
                        exact ⟨p, l, hpl, ht, by simpa only [List.map_cons, List.map_nil, eval_and2] using hf⟩)
                      (by
                        obtain ⟨p, l, hpl, ht, hf⟩ := hSep_vu
                        rw [← agree_u (P p l) (len_P p l)] at hf
                        rw [eval_v (P p l) (len_P p l), hgin, hand] at ht
                        exact ⟨p, l, hpl, by simpa only [List.map_cons, List.map_nil, eval_and2] using ht, hf⟩)
                    omega
                  · have h62 : 62 ≤ C''.size := topOr C'' u a b hC''mono hC''back hu_C'' ha hb hab
                      (fun p l hpl => by
                        have h := hCov_uv p l hpl
                        rw [← agree_u (P p l) (len_P p l), eval_v (P p l) (len_P p l), hgin, hor] at h
                        simpa only [List.map_cons, List.map_nil, eval_or2] using h)
                      (fun Q hQ => by
                        have h := hRej_uv Q hQ
                        rw [← agree_u (N Q) (len_N Q), eval_v (N Q) (len_N Q), hgin, hor] at h
                        simpa only [List.map_cons, List.map_nil, eval_or2] using h)
                      (by
                        obtain ⟨p, l, hpl, ht, hf⟩ := hSep_uv
                        rw [← agree_u (P p l) (len_P p l)] at ht
                        rw [eval_v (P p l) (len_P p l), hgin, hor] at hf
                        exact ⟨p, l, hpl, ht, by simpa only [List.map_cons, List.map_nil, eval_or2] using hf⟩)
                      (by
                        obtain ⟨p, l, hpl, ht, hf⟩ := hSep_vu
                        rw [← agree_u (P p l) (len_P p l)] at hf
                        rw [eval_v (P p l) (len_P p l), hgin, hor] at ht
                        exact ⟨p, l, hpl, by simpa only [List.map_cons, List.map_nil, eval_or2] using ht, hf⟩)
                    omega
              | cons _ _ =>
                rw [hgin] at hlen
                simp at hlen
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact peel_ordered w1 w2 hw1_26 hlt hw2 hCov hRej hSep1 hSep2
      · exact peel_ordered w2 w1 hw2_26 hgt hw1
          (fun p l hpl => (hCov p l hpl).symm)
          (fun Q hQ => ⟨(hRej Q hQ).2, (hRej Q hQ).1⟩)
          hSep2 hSep1
  intro C w1 w2 hMono hBack hw1 hw2 _ _
  dsimp only
  intro hCov hRej hSep1 hSep2
  exact main_ind C.size C w1 w2 rfl hMono hBack hw1 hw2 hCov hRej hSep1 hSep2
