import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the final combination and keep its two operand wires in the earlier list.
-- At minimum size each operand must be indispensable on a test input.
theorem PEqualNP.Outside.R_meta_1692_2 :
    (∀ (C : Circuit) (a b : ℕ), Monotone2 C → NestedCover.ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let Good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let V := fun (w : ℕ) (x : List Bool) => (C.wires x).getD w false
      (∀ p l : Fin 13, p - l ∈ D → V a (P p l) = true ∨ V b (P p l) = true) →
      (∀ Q : Finset (Fin 13), Good Q → V a (N Q) = false ∧ V b (N Q) = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ V a (P p l) = true ∧ V b (P p l) = false) →
      (∃ p l : Fin 13, p - l ∈ D ∧ V b (P p l) = true ∧ V a (P p l) = false) →
      63 ≤ C.size) →
    (∀ (C : Circuit) (a b : ℕ), Monotone2 C → NestedCover.ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size →
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let Good := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let V := fun (w : ℕ) (x : List Bool) => (C.wires x).getD w false
      (∀ p l : Fin 13, p - l ∈ D → V a (P p l) = true ∧ V b (P p l) = true) →
      (∀ Q : Finset (Fin 13), Good Q → V a (N Q) = false ∨ V b (N Q) = false) →
      (∃ Q : Finset (Fin 13), Good Q ∧ V a (N Q) = false ∧ V b (N Q) = true) →
      (∃ Q : Finset (Fin 13), Good Q ∧ V b (N Q) = false ∧ V a (N Q) = true) →
      63 ≤ C.size) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  classical
  intro orBound andBound
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let P (p l : Fin 13) := List.ofFn (fun u : Fin 13 => decide (u = p)) ++
    List.ofFn (fun v : Fin 13 => decide (v = l))
  let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
  let Good (Q : Finset (Fin 13)) := Q.card = 4 ∧
    ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
  let V (gs : List Gate) (w : ℕ) (x : List Bool) := (Circuit.wires ⟨gs, 0⟩ x).getD w false
  let W (n : ℕ) := ∃ (gs : List Gate) (out : ℕ), gs.length = n ∧
    Monotone2 ⟨gs, 0⟩ ∧ NestedCover.ReadsBack 26 ⟨gs, 0⟩ ∧
    (∀ p l : Fin 13, p - l ∈ D → V gs out (P p l) = true) ∧
    (∀ Q : Finset (Fin 13), Good Q → V gs out (N Q) = false)
  have goodOne : Good {0, 1, 2, 5} := by decide
  have p_len (p l : Fin 13) : (P p l).length = 26 := by simp [P]
  have n_len (Q : Finset (Fin 13)) : (N Q).length = 26 := by simp [N]
  have extend : ∀ (gs : List Gate) (x : List Bool),
      ∃ y, (Circuit.wires ⟨gs, 0⟩ x) = x ++ y ∧ y.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro x; exact ⟨[], (List.append_nil x).symm, rfl⟩
    | cons g gs ih =>
      intro x
      let z := g.op.eval (g.inputs.map fun i => x.getD i false)
      obtain ⟨y, hy, hyl⟩ := ih (x ++ [z])
      refine ⟨z :: y, ?_, by simp [hyl]⟩
      have hstep : Circuit.wires ⟨g :: gs, 0⟩ x =
          Circuit.wires ⟨gs, 0⟩ (x ++ [z]) := rfl
      rw [hstep, hy]
      simp [List.append_assoc]
  have wires_len (gs : List Gate) (x : List Bool) :
      (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
    obtain ⟨y, hy, hl⟩ := extend gs x
    rw [hy, List.length_append, hl]
  have preserves (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
      V gs w x = x.getD w false := by
    obtain ⟨y, hy, _⟩ := extend gs x
    dsimp [V]
    rw [hy, List.getD_append _ _ _ _ hw]
  have append (gs rest : List Gate) (x : List Bool) :
      Circuit.wires ⟨gs ++ rest, 0⟩ x =
        Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨gs, 0⟩ x) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    change (gs ++ rest).foldl step x = rest.foldl step (gs.foldl step x)
    rw [List.foldl_append]
  have finalValue (pre post : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 26) :
      V (pre ++ g :: post) (26 + pre.length) x =
        g.op.eval (g.inputs.map (fun w => V pre w x)) := by
    let y := Circuit.wires ⟨pre, 0⟩ x
    let z := g.op.eval (g.inputs.map (fun w => y.getD w false))
    have hy : y.length = 26 + pre.length := by rw [wires_len, hx]
    have eq : Circuit.wires ⟨pre ++ g :: post, 0⟩ x =
        Circuit.wires ⟨post, 0⟩ (y ++ [z]) := by
      rw [append]; rfl
    change (Circuit.wires ⟨pre ++ g :: post, 0⟩ x).getD (26 + pre.length) false = z
    rw [eq]
    change V post (26 + pre.length) (y ++ [z]) = z
    rw [preserves post _ _ (by simp [hy])]
    rw [← hy]
    simp
  have split : ∀ (gs : List Gate) (i : ℕ) (g : Gate), gs[i]? = some g →
      ∃ pre post, gs = pre ++ g :: post ∧ pre.length = i := by
    intro gs
    induction gs with
    | nil => intro i g h; simp at h
    | cons a gs ih =>
      intro i g h
      cases i with
      | zero =>
        simp at h
        subst g
        exact ⟨[], gs, rfl, rfl⟩
      | succ i =>
        have hg : gs[i]? = some g := by simpa using h
        obtain ⟨pre, post, rfl, hl⟩ := ih i g hg
        exact ⟨a :: pre, post, rfl, by simp [hl]⟩
  have raw : ∀ i : Fin 26, ((P 0 0).getD i false && (P 1 1).getD i false) = false := by decide
  intro gates out hmon hread hpos hneg
  by_contra hsize
  have ready : W gates.length := by
    refine ⟨gates, out, rfl, ?_, ?_, hpos, ?_⟩
    · intro g hg
      refine ⟨?_, (hmon g hg).2⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hmon g hg).1
    · intro i hi w hw
      change i < gates.length at hi
      change w ∈ (gates.getD i ⟨GateOp.or, []⟩).inputs at hw
      exact hread ⟨i, hi⟩ w (by simpa [List.getD_eq_getElem?_getD, hi] using hw)
    · intro Q hQ
      exact hneg Q hQ.1 hQ.2
  have existsW : ∃ n, W n := ⟨_, ready⟩
  let n := Nat.find existsW
  have hn : n ≤ gates.length := Nat.find_min' existsW ready
  have hnsmall : n < 64 := by omega
  obtain ⟨gs, u, hnlen, hm, hr, hp, hq⟩ := Nat.find_spec existsW
  change gs.length = n at hnlen
  have earlierBad : ∀ pre : List Gate, pre.length < n → ¬ W pre.length := by
    intro pre hpre hw
    have := Nat.find_min' existsW hw
    omega
  have h00 := hp 0 0 (by decide)
  have h11 := hp 1 1 (by decide)
  have huRaw : 26 ≤ u := by
    by_contra h
    have hi : u < 26 := by omega
    rw [preserves gs (P 0 0) u (p_len _ _ ▸ hi)] at h00
    rw [preserves gs (P 1 1) u (p_len _ _ ▸ hi)] at h11
    have e := raw ⟨u, hi⟩
    rw [h00, h11] at e
    simp at e
  have huBound : u < 26 + gs.length := by
    by_contra h
    have hw : (Circuit.wires ⟨gs, 0⟩ (P 0 0)).length ≤ u := by
      rw [wires_len, p_len]; omega
    have h0 : V gs u (P 0 0) = false := by
      simp [V, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hw]
    rw [h0] at h00
    simp at h00
  let i := u - 26
  have hi : i < gs.length := by omega
  let g := gs[i]
  have hgi : gs[i]? = some g := by simp [g, hi]
  obtain ⟨pre, post, hs, hlen⟩ := split gs i g hgi
  have hu : u = 26 + pre.length := by omega
  have hpre : pre.length < n := by
    have hh : n = pre.length + 1 + post.length := by
      rw [← hnlen, hs]; simp; omega
    omega
  have hpm : Monotone2 ⟨pre, 0⟩ := by
    intro j hj
    apply hm j
    rw [hs]
    exact List.mem_append_left _ hj
  have hpr : NestedCover.ReadsBack 26 ⟨pre, 0⟩ := by
    intro j hj w hw
    change j < pre.length at hj
    have hj' : j < gs.length := by rw [hs, List.length_append]; omega
    apply hr j hj' w
    change w ∈ (pre.getD j ⟨GateOp.or, []⟩).inputs at hw
    change w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs
    rw [hs, List.getD_append _ _ _ _ hj]
    exact hw
  have hgm := hm g (by rw [hs]; simp)
  have hOp : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hgm.1
  have hgr : ∀ w ∈ g.inputs, w < 26 + pre.length := by
    have hj : pre.length < gs.length := by rw [hs, List.length_append]; simp
    intro w hw
    apply hr pre.length hj w
    change w ∈ (gs.getD pre.length ⟨GateOp.or, []⟩).inputs
    simpa [hs, List.getD_append_right] using hw
  have valid (w : ℕ) (ha : ∀ p l : Fin 13, p - l ∈ D → V pre w (P p l) = true)
      (hb : ∀ Q : Finset (Fin 13), Good Q → V pre w (N Q) = false) : False :=
    earlierBad pre hpre ⟨pre, w, rfl, hpm, hpr, ha, hb⟩
  have gate (x : List Bool) (hx : x.length = 26) :
      V gs u x = g.op.eval (g.inputs.map (fun w => V pre w x)) := by
    rw [hs, hu]
    exact finalValue pre post g x hx
  have unary (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (b : Bool) :
      op.eval [b] = b := by
    rcases hop with rfl | rfl <;> cases b <;> rfl
  have evalAnd (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    cases a <;> cases b <;> rfl
  have evalOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    cases a <;> cases b <;> rfl
  cases he : g.inputs with
  | nil =>
    rcases hOp with ha | ho
    · have H := hq {0, 1, 2, 5} goodOne
      rw [gate _ (n_len _), he, ha] at H
      change true = false at H
      cases H
    · rw [gate _ (p_len _ _), he, ho] at h00
      change false = true at h00
      cases h00
  | cons a rest =>
    cases er : rest with
    | nil =>
      apply valid a
      · intro p l hpl
        have he' := hp p l hpl
        rw [gate _ (p_len _ _), he, er] at he'
        simpa only [List.map_cons, List.map_nil, unary g.op hOp] using he'
      · intro Q hQ
        have he' := hq Q hQ
        rw [gate _ (n_len _), he, er] at he'
        simpa only [List.map_cons, List.map_nil, unary g.op hOp] using he'
    | cons b rest' =>
      have er' : rest' = [] := by
        have h := hgm.2
        rw [he, er] at h
        cases rest' with
        | nil => rfl
        | cons c cs => simp at h
      subst rest'
      have ha := hgr a (by simp [he, er])
      have hb := hgr b (by simp [he, er])
      rcases hOp with hAnd | hOr
      · have A : ∀ p l : Fin 13, p - l ∈ D →
            V pre a (P p l) = true ∧ V pre b (P p l) = true := by
          intro p l h
          have z := hp p l h
          rw [gate _ (p_len _ _), he, er, hAnd] at z
          simp only [List.map_cons, List.map_nil, evalAnd] at z
          simpa using z
        have B : ∀ Q : Finset (Fin 13), Good Q →
            V pre a (N Q) = false ∨ V pre b (N Q) = false := by
          intro Q h
          have z := hq Q h
          rw [gate _ (n_len _), he, er, hAnd] at z
          simp only [List.map_cons, List.map_nil, evalAnd] at z
          cases hx : V pre a (N Q) with
          | false => exact Or.inl rfl
          | true => exact Or.inr (by simpa [hx] using z)
        have E1 : ∃ Q : Finset (Fin 13), Good Q ∧
            V pre a (N Q) = false ∧ V pre b (N Q) = true := by
          by_contra E
          apply valid b (fun p l h => (A p l h).2)
          intro Q h
          cases hx : V pre b (N Q) with
          | false => rfl
          | true => exact False.elim (E ⟨Q, h, (B Q h).resolve_right (by simp [hx]), hx⟩)
        have E2 : ∃ Q : Finset (Fin 13), Good Q ∧
            V pre b (N Q) = false ∧ V pre a (N Q) = true := by
          by_contra E
          apply valid a (fun p l h => (A p l h).1)
          intro Q h
          cases hx : V pre a (N Q) with
          | false => rfl
          | true => exact False.elim (E ⟨Q, h, (B Q h).resolve_left (by simp [hx]), hx⟩)
        have lower : 63 ≤ pre.length :=
          andBound ⟨pre, 0⟩ a b hpm hpr ha hb A B E1 E2
        omega
      · have A : ∀ p l : Fin 13, p - l ∈ D →
            V pre a (P p l) = true ∨ V pre b (P p l) = true := by
          intro p l h
          have z := hp p l h
          rw [gate _ (p_len _ _), he, er, hOr] at z
          simp only [List.map_cons, List.map_nil, evalOr] at z
          simpa using z
        have B : ∀ Q : Finset (Fin 13), Good Q →
            V pre a (N Q) = false ∧ V pre b (N Q) = false := by
          intro Q h
          have z := hq Q h
          rw [gate _ (n_len _), he, er, hOr] at z
          simp only [List.map_cons, List.map_nil, evalOr] at z
          simpa using z
        have E1 : ∃ p l : Fin 13, p - l ∈ D ∧
            V pre a (P p l) = true ∧ V pre b (P p l) = false := by
          by_contra E
          apply valid b _ (fun Q h => (B Q h).2)
          intro p l h
          cases hx : V pre b (P p l) with
          | false => exact False.elim (E ⟨p,l,h,(A p l h).resolve_right (by simp [hx]),hx⟩)
          | true => rfl
        have E2 : ∃ p l : Fin 13, p - l ∈ D ∧
            V pre b (P p l) = true ∧ V pre a (P p l) = false := by
          by_contra E
          apply valid a _ (fun Q h => (B Q h).1)
          intro p l h
          cases hx : V pre a (P p l) with
          | false => exact False.elim (E ⟨p,l,h,(A p l h).resolve_left (by simp [hx]),hx⟩)
          | true => rfl
        have lower : 63 ≤ pre.length :=
          orBound ⟨pre, 0⟩ a b hpm hpr ha hb A B E1 E2
        omega
