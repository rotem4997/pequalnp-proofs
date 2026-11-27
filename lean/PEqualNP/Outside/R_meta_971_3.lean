import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A minimum separator cannot discard either operand of its output gate.
-- The two operands share the earlier gate list.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_971_3 :
    (∀ (C : Circuit) (a b : ℕ), Monotone2 C → a < 14 + C.size → b < 14 + C.size →
      let E : List (ℕ × ℕ) := ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))
      let T := fun (x : Fin 14 → Bool) =>
        ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
      let V := fun (w : ℕ) (x : Fin 14 → Bool) => (C.wires (List.ofFn x)).getD w false
      (∀ x, T x → V a x = true ∨ V b x = true) →
      (∀ x, ¬ T x → V a x = false ∧ V b x = false) →
      (∃ x, T x ∧ V a x = true ∧ V b x = false) →
      (∃ x, T x ∧ V b x = true ∧ V a x = false) →
      26 ≤ C.size) →
    (∀ (C : Circuit) (a b : ℕ), Monotone2 C → a < 14 + C.size → b < 14 + C.size →
      let E : List (ℕ × ℕ) := ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))
      let T := fun (x : Fin 14 → Bool) =>
        ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
      let V := fun (w : ℕ) (x : Fin 14 → Bool) => (C.wires (List.ofFn x)).getD w false
      (∀ x, T x → V a x = true ∧ V b x = true) →
      (∀ x, ¬ T x → V a x = false ∨ V b x = false) →
      (∃ x, ¬ T x ∧ V a x = false ∧ V b x = true) →
      (∃ x, ¬ T x ∧ V b x = false ∧ V a x = true) →
      26 ≤ C.size) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  classical
  intro orBound andBound
  let E : List (ℕ × ℕ) := ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))
  let T := fun (x : Fin 14 → Bool) =>
    ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
  let P (u v k : Fin 14) := decide (k = u ∨ k = v)
  let V (gs : List Gate) (w : ℕ) (x : List Bool) := (Circuit.wires ⟨gs, 0⟩ x).getD w false
  let W (n : ℕ) := ∃ (gs : List Gate) (out : ℕ), gs.length = n ∧
    Monotone2 ⟨gs, 0⟩ ∧ ∀ x : Fin 14 → Bool, V gs out (List.ofFn x) = true ↔ T x
  have t01 : T (P 0 7) := ⟨0, 7, by decide, by decide, by decide⟩
  have t12 : T (P 1 9) := ⟨1, 9, by decide, by decide, by decide⟩
  have tEmpty : ¬ T (fun _ => false) := by
    rintro ⟨_, _, _, impossible, _⟩
    cases impossible
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
  have finalValue (pre post : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 14) :
      V (pre ++ g :: post) (14 + pre.length) x =
        g.op.eval (g.inputs.map (fun w => V pre w x)) := by
    let y := Circuit.wires ⟨pre, 0⟩ x
    let z := g.op.eval (g.inputs.map (fun w => y.getD w false))
    have hy : y.length = 14 + pre.length := by rw [wires_len, hx]
    have eq : Circuit.wires ⟨pre ++ g :: post, 0⟩ x =
        Circuit.wires ⟨post, 0⟩ (y ++ [z]) := by
      rw [append]; rfl
    change (Circuit.wires ⟨pre ++ g :: post, 0⟩ x).getD (14 + pre.length) false = z
    rw [eq]
    change V post (14 + pre.length) (y ++ [z]) = z
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
  have raw : ∀ i : Fin 14,
      ((List.ofFn (P 0 7)).getD i false && (List.ofFn (P 1 9)).getD i false) = false := by decide
  have inRange (gs : List Gate) (w : ℕ) (x : Fin 14 → Bool)
      (accepts : V gs w (List.ofFn x) = true) : w < 14 + gs.length := by
    by_contra bad
    have past : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length ≤ w := by
      rw [wires_len, List.length_ofFn]
      omega
    have rejects : V gs w (List.ofFn x) = false := by
      simp only [V, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr past, Option.getD_none]
    have impossible : false = true := rejects.symm.trans accepts
    cases impossible
  intro C hMon hEval
  by_contra hSize
  rcases C with ⟨gates, out⟩
  change ¬ 27 ≤ gates.length at hSize
  have ready : W gates.length := ⟨gates, out, rfl, hMon, hEval⟩
  have existsW : ∃ n, W n := ⟨_, ready⟩
  let n := Nat.find existsW
  have hn : n ≤ gates.length := Nat.find_min' existsW ready
  have hnsmall : n < 27 := by omega
  obtain ⟨gs, u, hnlen, hm, hp⟩ := Nat.find_spec existsW
  change gs.length = n at hnlen
  have earlier (pre : List Gate) (hpre : pre.length < n) (hw : W pre.length) : False := by
    have bound : n ≤ pre.length := Nat.find_min' existsW hw
    omega
  have positive (x : Fin 14 → Bool) (hx : T x) : V gs u (List.ofFn x) = true := (hp x).mpr hx
  have negative (x : Fin 14 → Bool) (hx : ¬ T x) : V gs u (List.ofFn x) = false := by
    cases h : V gs u (List.ofFn x)
    · rfl
    · exact False.elim (hx ((hp x).mp h))
  have first := positive (P 0 7) t01
  have second := positive (P 1 9) t12
  have huRaw : 14 ≤ u := by
    by_contra h
    have hi : u < 14 := by omega
    rw [preserves gs (List.ofFn (P 0 7)) u (by simpa using hi)] at first
    rw [preserves gs (List.ofFn (P 1 9)) u (by simpa using hi)] at second
    have e := raw ⟨u, hi⟩
    rw [first, second] at e
    cases e
  have huBound := inRange gs u (P 0 7) (positive (P 0 7) t01)
  let i := u - 14
  have hi : i < gs.length := by omega
  let g := gs[i]
  have hgi : gs[i]? = some g := by simp [g, hi]
  obtain ⟨pre, post, hs, hlen⟩ := split gs i g hgi
  have hu : u = 14 + pre.length := by omega
  have hpre : pre.length < n := by
    have h : n = pre.length + 1 + post.length := by
      rw [← hnlen, hs]
      simp
      omega
    omega
  have hpm : Monotone2 ⟨pre, 0⟩ := by
    intro j hj
    apply hm j
    rw [hs]
    exact List.mem_append_left _ hj
  have hgm := hm g (by rw [hs]; simp)
  have hOp : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hgm.1
  have valid (w : ℕ) (ha : ∀ x : Fin 14 → Bool, T x → V pre w (List.ofFn x) = true)
      (hb : ∀ x : Fin 14 → Bool, ¬ T x → V pre w (List.ofFn x) = false) : False := by
    apply earlier pre hpre
    refine ⟨pre, w, rfl, hpm, ?_⟩
    intro x
    refine ⟨?_, ha x⟩
    intro h
    by_contra hn
    have impossible : false = true := (hb x hn).symm.trans h
    cases impossible
  have gate (x : Fin 14 → Bool) :
      V gs u (List.ofFn x) = g.op.eval (g.inputs.map (fun w => V pre w (List.ofFn x))) := by
    rw [hs, hu]
    exact finalValue pre post g _ (List.length_ofFn)
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
    · have h := negative (fun _ => false) tEmpty
      rw [gate, he, ha] at h
      change true = false at h
      cases h
    · rw [gate, he, ho] at first
      change false = true at first
      cases first
  | cons a rest =>
    cases er : rest with
    | nil =>
      apply valid a
      · intro x hx
        have h := positive x hx
        rw [gate, he, er] at h
        simpa only [List.map_cons, List.map_nil, unary g.op hOp] using h
      · intro x hx
        have h := negative x hx
        rw [gate, he, er] at h
        simpa only [List.map_cons, List.map_nil, unary g.op hOp] using h
    | cons b rest' =>
      have empty : rest' = [] := by
        have h := hgm.2
        rw [he, er] at h
        cases rest' with
        | nil => rfl
        | cons c cs => simp at h
      subst rest'
      rcases hOp with hAnd | hOr
      · have A : ∀ x : Fin 14 → Bool, T x → V pre a (List.ofFn x) = true ∧
            V pre b (List.ofFn x) = true := by
          intro x hx
          have z := positive x hx
          rw [gate, he, er, hAnd] at z
          simp only [List.map_cons, List.map_nil, evalAnd] at z
          exact Bool.and_eq_true_iff.mp z
        have B : ∀ x : Fin 14 → Bool, ¬ T x → V pre a (List.ofFn x) = false ∨
            V pre b (List.ofFn x) = false := by
          intro x hx
          have z := negative x hx
          rw [gate, he, er, hAnd] at z
          simp only [List.map_cons, List.map_nil, evalAnd] at z
          exact Bool.and_eq_false_iff.mp z
        have E1 : ∃ x : Fin 14 → Bool, ¬ T x ∧ V pre a (List.ofFn x) = false ∧
            V pre b (List.ofFn x) = true := by
          by_contra E
          apply valid b (fun x h => (A x h).2)
          intro x h
          cases hx : V pre b (List.ofFn x) with
          | false => rfl
          | true => exact False.elim (E ⟨x, h,
              (B x h).resolve_right (fun hz => Bool.false_ne_true (hz.symm.trans hx)), hx⟩)
        have E2 : ∃ x : Fin 14 → Bool, ¬ T x ∧ V pre b (List.ofFn x) = false ∧
            V pre a (List.ofFn x) = true := by
          by_contra E
          apply valid a (fun x h => (A x h).1)
          intro x h
          cases hx : V pre a (List.ofFn x) with
          | false => rfl
          | true => exact False.elim (E ⟨x, h,
              (B x h).resolve_left (fun hz => Bool.false_ne_true (hz.symm.trans hx)), hx⟩)
        have aBound := inRange pre a (P 0 7) (A _ t01).1
        have bBound := inRange pre b (P 0 7) (A _ t01).2
        have lower : 26 ≤ pre.length := andBound ⟨pre, 0⟩ a b hpm aBound bBound A B E1 E2
        omega
      · have A : ∀ x : Fin 14 → Bool, T x → V pre a (List.ofFn x) = true ∨
            V pre b (List.ofFn x) = true := by
          intro x hx
          have z := positive x hx
          rw [gate, he, er, hOr] at z
          simp only [List.map_cons, List.map_nil, evalOr] at z
          exact Bool.or_eq_true_iff.mp z
        have B : ∀ x : Fin 14 → Bool, ¬ T x → V pre a (List.ofFn x) = false ∧
            V pre b (List.ofFn x) = false := by
          intro x hx
          have z := negative x hx
          rw [gate, he, er, hOr] at z
          simp only [List.map_cons, List.map_nil, evalOr] at z
          exact Bool.or_eq_false_iff.mp z
        have E1 : ∃ x : Fin 14 → Bool, T x ∧ V pre a (List.ofFn x) = true ∧
            V pre b (List.ofFn x) = false := by
          by_contra E
          apply valid b _ (fun x h => (B x h).2)
          intro x h
          cases hx : V pre b (List.ofFn x) with
          | false => exact False.elim (E ⟨x, h,
              (A x h).resolve_right (fun hz => Bool.false_ne_true (hx.symm.trans hz)), hx⟩)
          | true => rfl
        have E2 : ∃ x : Fin 14 → Bool, T x ∧ V pre b (List.ofFn x) = true ∧
            V pre a (List.ofFn x) = false := by
          by_contra E
          apply valid a _ (fun x h => (B x h).1)
          intro x h
          cases hx : V pre a (List.ofFn x) with
          | false => exact False.elim (E ⟨x, h,
              (A x h).resolve_left (fun hz => Bool.false_ne_true (hx.symm.trans hz)), hx⟩)
          | true => rfl
        have aBound : a < 14 + pre.length := by
          obtain ⟨x, _, hxa, _⟩ := E1
          exact inRange pre a x hxa
        have bBound : b < 14 + pre.length := by
          obtain ⟨y, _, hyb, _⟩ := E2
          exact inRange pre b y hyb
        have lower : 26 ≤ pre.length := orBound ⟨pre, 0⟩ a b hpm aBound bBound A B E1 E2
        omega
