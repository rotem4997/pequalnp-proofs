import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2498_301
    (h_mono : ∀ (D : Circuit), Monotone2 D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 1]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
          fun e => x e.1 && x e.2) →
      (∀ v ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < D.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → (D.wires (List.ofFn x ++ [x 0 || x 1])).getD (10 + j) false = b) ∨
           (∃ i < 10 + j, ∀ x : Fin 9 → Bool, x v = false → (D.wires (List.ofFn x ++ [x 0 || x 1])).getD (10 + j) false = (D.wires (List.ofFn x ++ [x 0 || x 1])).getD i false))) →
        S.card ≤ if v = 0 ∨ v = 1 then 2 else 3) →
      15 ≤ D.size)
    (h_signed : ∀ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 || x 1, false]) != p) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
          fun e => x e.1 && x e.2) →
      14 ≤ B.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro C hfan hfirst hfun hfew
  let step (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let push (v : List Bool) (g : BinaryGate) : List Bool := v ++ [g.op (v.getD g.left false) (v.getD g.right false)]
  let read (v : List Bool) (r : ℕ × Bool) : Bool := v.getD r.1 false != r.2
  let signed (g : BinaryGate) : Prop := ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)
  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 1]
  have hsz_eq : ∀ D : Circuit, D.size = D.gates.length := fun _ => rfl
  have hwires_eq : ∀ (D : Circuit) (x : List Bool), D.wires x = D.gates.foldl step x := fun _ _ => rfl
  have hev_eq : ∀ (D : Circuit) (x : List Bool), D.eval x = (D.gates.foldl step x).getD D.output false := fun _ _ => rfl
  have hcfun_eq : ∀ (D : Circuit) (x : Fin 9 → Bool), circuitFun 9 D x = D.eval (List.ofFn x) := fun _ _ => rfl
  have hBsz_eq : ∀ B : BinaryCircuit, B.size = B.gates.length := fun _ => rfl
  have hBev_eq : ∀ (B : BinaryCircuit) (v : List Bool), B.eval v = (B.gates.foldl push v).getD B.output false := fun _ _ => rfl
  have hand0 : GateOp.and.eval [] = true := rfl
  have hand1 : ∀ a : Bool, GateOp.and.eval [a] = a := fun a => by cases a <;> rfl
  have hand2 : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := fun a b => by cases a <;> cases b <;> rfl
  have hor0 : GateOp.or.eval [] = false := rfl
  have hor1 : ∀ a : Bool, GateOp.or.eval [a] = a := fun a => by cases a <;> rfl
  have hor2 : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := fun a b => by cases a <;> cases b <;> rfl
  have hnot0 : GateOp.not.eval [] = true := rfl
  have hnot1 : ∀ (a : Bool) (t : List Bool), GateOp.not.eval (a :: t) = !a := fun a _ => by cases a <;> rfl
  have hkeep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons a rest ih =>
      intro w i hi
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  rcases C with ⟨gates, out⟩
  cases gates with
  | nil =>
    have h := hfirst (fun _ => true)
    rw [hwires_eq] at h
    simp only [List.foldl_nil] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)] at h
    exact Bool.noConfusion h
  | cons g0 gs =>
    let D : Circuit := ⟨gs, out⟩
    have hDfan : FanInTwo D := fun a ha => hfan a (List.mem_cons_of_mem _ ha)
    have hfront : ∀ x : Fin 9 → Bool, step (List.ofFn x) g0 = row x := by
      intro x
      have h := hfirst x
      rw [hwires_eq] at h
      simp only [List.foldl_cons] at h
      rw [hkeep gs (step (List.ofFn x) g0) 9 (by simp [step])] at h
      have hread : (step (List.ofFn x) g0).getD 9 false =
          g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) := by
        dsimp only [step]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      rw [hread] at h
      dsimp only [step, row]
      rw [h]
    have hwires_D : ∀ x : Fin 9 → Bool, (⟨g0 :: gs, out⟩ : Circuit).wires (List.ofFn x) = D.wires (row x) := by
      intro x
      rw [hwires_eq, hwires_eq]
      simp only [List.foldl_cons, D]
      rw [hfront x]
    have hDcorrect : ∀ x : Fin 9 → Bool, D.eval (row x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
          fun e => x e.1 && x e.2 := by
      intro x
      have e := congrFun hfun x
      rw [hcfun_eq, hev_eq] at e
      rw [hev_eq]
      simp only [List.foldl_cons, D] at e ⊢
      rw [hfront x] at e
      exact e
    by_cases hhasNot : ∃ g ∈ gs, g.op = GateOp.not
    · -- Compile D to a signed BinaryCircuit B with B.size + 1 ≤ D.size
      letI := lineDegreeGateOpDecEq
      have hsign_rule : ∀ x y a b isOr : Bool,
          (((x == (a == isOr)) && (y == (b == isOr))) != isOr) =
            (if isOr then ((x != a) || (y != b)) else ((x != a) && (y != b))) := by
        intro x y a b isOr
        cases x <;> cases y <;> cases a <;> cases b <;> cases isOr <;> rfl
      have hread_push : ∀ (v : List Bool) (r : ℕ × Bool) (hr : r.1 < v.length) (q : BinaryGate),
          read (push v q) r = read v r := by
        intro v r hr q
        dsimp only [read, push]
        rw [List.getD_append _ _ _ _ hr]
      have hrunLen : ∀ (bs : List BinaryGate) (v : List Bool), (bs.foldl push v).length = v.length + bs.length := by
        intro bs
        induction bs with
        | nil => intro _; simp
        | cons q qs ih => intro v; rw [List.foldl_cons, ih]; simp [push]; omega
      have holdLen : ∀ (ts : List Gate) (u : List Bool), (ts.foldl step u).length = u.length + ts.length := by
        intro ts
        induction ts with
        | nil => intro _; simp
        | cons q qs ih => intro u; rw [List.foldl_cons, ih]; simp [step]; omega
      have hpres : ∀ (bs : List BinaryGate) (v : List Bool) (i : ℕ), i < v.length →
          (bs.foldl push v).getD i false = v.getD i false := by
        intro bs
        induction bs with
        | nil => intro _ _ _; rfl
        | cons q qs ih =>
          intro v i hi
          rw [List.foldl_cons, ih (push v q) i (by simp [push]; omega)]
          exact List.getD_append _ _ _ _ hi
      have hgadget : ∀ (g : Gate) (hbg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
          (rho : ℕ → ℕ × Bool) (m : ℕ) (hz : 10 < m) (hbd : ∀ i, (rho i).1 < m),
          ∃ (add : List BinaryGate) (r : ℕ × Bool), (∀ q ∈ add, signed q) ∧
            (add.length + (if g.op = .not then 1 else 0) ≤ 1) ∧ r.1 < m + add.length ∧
            ∀ (u v : List Bool), v.length = m → v.getD 10 false = false →
              (∀ i, read v (rho i) = u.getD i false) →
              (∀ p : ℕ × Bool, p.1 < m → read (add.foldl push v) p = read v p) ∧
                read (add.foldl push v) r = g.op.eval (g.inputs.map fun i => u.getD i false) := by
        intro g hbg rho m hz hbd
        rcases g with ⟨op, ins⟩
        rcases hbg with ⟨hops, hlen⟩
        have hemit : ∀ (a b : ℕ × Bool), a.1 < m → b.1 < m → ∀ (d : Bool), op ≠ .not →
            (∀ (u v : List Bool), v.getD 10 false = false →
              (∀ i, read v (rho i) = u.getD i false) →
              (if d then (read v a || read v b) else (read v a && read v b)) =
                op.eval (ins.map fun i => u.getD i false)) →
            ∃ (add : List BinaryGate) (r : ℕ × Bool), (∀ q ∈ add, signed q) ∧
              (add.length + (if op = .not then 1 else 0) ≤ 1) ∧ r.1 < m + add.length ∧
              ∀ (u v : List Bool), v.length = m → v.getD 10 false = false →
                (∀ i, read v (rho i) = u.getD i false) →
                (∀ p : ℕ × Bool, p.1 < m → read (add.foldl push v) p = read v p) ∧
                  read (add.foldl push v) r = op.eval (ins.map fun i => u.getD i false) := by
          intro a b ha hb d hne hsem
          let q : BinaryGate := ⟨fun x y => (x == (a.2 == d)) && (y == (b.2 == d)), a.1, b.1⟩
          refine ⟨[q], (m, d), ?_, by simp [hne], by simp, ?_⟩
          · intro q' hq'; rw [List.mem_singleton.mp hq']; exact ⟨a.2 == d, b.2 == d, rfl⟩
          · intro u v lv z h
            refine ⟨fun p hp => hread_push v p (lv ▸ hp) q, ?_⟩
            dsimp only [List.foldl_cons, List.foldl_nil, read, push]
            rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq lv), lv, Nat.sub_self]
            exact (hsign_rule _ _ _ _ d).trans (hsem u v z h)
        rcases hops with rfl | rfl | rfl
        · cases ins with
          | nil => exact hemit (10, true) (10, true) hz hz false (by intro e; cases e) (fun u v z _ => by simp only [Bool.false_eq_true, if_false, read, z, List.map_nil, hand0]; rfl)
          | cons i is =>
            cases is with
            | nil => exact hemit (rho i) (10, true) (hbd i) hz false (by intro e; cases e) (fun u v z h => by simp only [Bool.false_eq_true, if_false, h, List.map_cons, List.map_nil, hand1]; dsimp only [read]; rw [z]; simp)
            | cons j js =>
              cases js with
              | nil => exact hemit (rho i) (rho j) (hbd i) (hbd j) false (by intro e; cases e) (fun u v _ h => by simp only [Bool.false_eq_true, if_false, h, List.map_cons, List.map_nil, hand2])
              | cons k ks => simp at hlen
        · cases ins with
          | nil => exact hemit (10, false) (10, false) hz hz true (by intro e; cases e) (fun u v z _ => by simp only [if_true, read, z, List.map_nil, hor0]; rfl)
          | cons i is =>
            cases is with
            | nil => exact hemit (rho i) (10, false) (hbd i) hz true (by intro e; cases e) (fun u v z h => by simp only [if_true, h, List.map_cons, List.map_nil, hor1]; dsimp only [read]; rw [z]; simp)
            | cons j js =>
              cases js with
              | nil => exact hemit (rho i) (rho j) (hbd i) (hbd j) true (by intro e; cases e) (fun u v _ h => by simp only [if_true, h, List.map_cons, List.map_nil, hor2])
              | cons k ks => simp at hlen
        · cases ins with
          | nil =>
            exact ⟨[], (10, true), by simp, by simp, by simpa using hz,
              fun _ v _ z _ => ⟨fun _ _ => rfl, by simp only [read, List.foldl_nil, List.map_nil]; rw [z, hnot0]; rfl⟩⟩
          | cons i is =>
            refine ⟨[], ((rho i).1, !(rho i).2), by simp, by simp, by simpa using hbd i, ?_⟩
            intro u v _ _ h
            refine ⟨fun _ _ => rfl, ?_⟩
            simp only [List.foldl_nil, List.map_cons]
            rw [hnot1, ← h i]
            dsimp only [read]
            cases v.getD (rho i).1 false <;> cases (rho i).2 <;> rfl
      have htrans : ∀ (ts : List Gate), (∀ g ∈ ts, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
          ∃ (bs : List BinaryGate) (rho : ℕ → ℕ × Bool), (∀ q ∈ bs, signed q) ∧
            bs.length + (ts.map fun g => if g.op = .not then 1 else 0).sum ≤ ts.length ∧
            (∀ i, (rho i).1 < 11 + bs.length) ∧
            ∀ x : List Bool, x.length = 10 → ∀ i,
              read (bs.foldl push (x ++ [false])) (rho i) = (ts.foldl step x).getD i false := by
        intro ts
        induction ts using List.reverseRecOn with
        | nil =>
          intro _
          refine ⟨[], fun i => (min i 10, false), by simp, by simp, fun i => by simp, ?_⟩
          intro x len i
          dsimp only [read, List.foldl_nil]
          by_cases hi : i < 10
          · rw [Nat.min_eq_left (by omega), List.getD_append _ _ _ _ (by omega)]; simp
          · rw [Nat.min_eq_right (by omega), List.getD_append_right _ _ _ _ (by omega),
                List.getD_eq_default x false (by omega), len]; rfl
        | append_singleton ts g ih =>
          intro hts
          obtain ⟨bs, rho, hsig, hsz, hbd, hsim⟩ := ih (fun q hq => hts q (List.mem_append_left _ hq))
          obtain ⟨add, r, hsig', hcost', hbr, hsound⟩ := hgadget g (hts g (by simp)) rho (11 + bs.length) (by omega) hbd
          let k := 10 + ts.length
          refine ⟨bs ++ add, fun i => if i = k then r else rho i, ?_, ?_, ?_, ?_⟩
          · intro q hq
            rcases List.mem_append.mp hq with hl | hr
            · exact hsig q hl
            · exact hsig' q hr
          · simp only [List.length_append, List.length_singleton, List.map_append, List.sum_append,
              List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at *
            omega
          · intro i; dsimp only
            split_ifs
            · simpa [Nat.add_assoc] using hbr
            · have := hbd i; simp only [List.length_append]; omega
          · intro x len i
            let u := ts.foldl step x
            let v := bs.foldl push (x ++ [false])
            have lu : u.length = k := by simp [u, holdLen, len, k]
            have lv : v.length = 11 + bs.length := by simp [v, hrunLen, len]
            have hz : v.getD 10 false = false := by
              rw [show v.getD 10 false = (x ++ [false]).getD 10 false from hpres bs _ 10 (by simp [len])]
              rw [List.getD_append_right _ _ _ _ (by omega), len]; rfl
            obtain ⟨hstab, hval⟩ := hsound u v lv hz (hsim x len)
            rw [List.foldl_append, List.foldl_append]
            by_cases hik : i = k
            · subst hik
              simp only [if_pos rfl, List.foldl_cons, List.foldl_nil]
              change read (add.foldl push v) r = (u ++ [_]).getD k false
              rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq lu), lu, Nat.sub_self]
              exact hval
            · simp only [if_neg hik, List.foldl_cons, List.foldl_nil]
              rw [hstab (rho i) (hbd i), hsim x len]
              change u.getD i false = (u ++ [_]).getD i false
              by_cases hlo : i < u.length
              · exact (List.getD_append _ _ _ _ hlo).symm
              · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
      obtain ⟨bs, rho, hsig, hsz, _, hsim⟩ := htrans gs hDfan
      have hcnt_pos : 1 ≤ (gs.map fun g => if g.op = .not then 1 else 0).sum := by
        obtain ⟨gn, hgn_mem, hgn_op⟩ := hhasNot
        have h1 : 1 ∈ gs.map (fun g => if g.op = .not then 1 else 0) :=
          List.mem_map.mpr ⟨gn, hgn_mem, by simp [hgn_op]⟩
        exact List.le_sum_of_mem h1
      let B : BinaryCircuit := ⟨bs, (rho out).1⟩
      have hBbound := h_signed B (rho out).2 hsig (fun x => by
        rw [hBev_eq]
        have hrowlen : (row x).length = 10 := by simp [row]
        have h1 := hsim (row x) hrowlen out
        dsimp only [B]
        change read (bs.foldl push (row x ++ [false])) (rho out) = _
        rw [h1, ← hev_eq D (row x)]
        exact hDcorrect x)
      rw [hBsz_eq] at hBbound
      dsimp only [B] at hBbound
      rw [hsz_eq]
      simp only [List.length_cons]
      omega
    · -- No NOT gate in gs: D is Monotone2!
      have hDmono : Monotone2 D := by
        intro g hg
        have hgf := hDfan g hg
        rcases hgf.1 with h1 | h2 | h3
        · exact ⟨Or.inl h1, hgf.2⟩
        · exact ⟨Or.inr h2, hgf.2⟩
        · exact False.elim (hhasNot ⟨g, hg, h3⟩)
      have hDfew : ∀ v ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)), ∀ S : Finset ℕ,
          (∀ j ∈ S, j < D.size ∧
            ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → (D.wires (row x)).getD (10 + j) false = b) ∨
             (∃ i < 10 + j, ∀ x : Fin 9 → Bool, x v = false → (D.wires (row x)).getD (10 + j) false = (D.wires (row x)).getD i false))) →
          S.card ≤ if v = 0 ∨ v = 1 then 2 else 3 := by
        intro v hv S hS
        by_cases hv01 : v = 0 ∨ v = 1
        · rw [if_pos hv01]
          let S' : Finset ℕ := insert 0 (S.image (· + 1))
          have hnot0 : 0 ∉ S.image (· + 1) := by simp
          have hcard : S'.card = S.card + 1 := by
            rw [Finset.card_insert_of_notMem hnot0, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
          have hS' : ∀ k ∈ S', k < (⟨g0 :: gs, out⟩ : Circuit).size ∧
              ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → ((⟨g0 :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD (9 + k) false = b) ∨
               (∃ i < 9 + k, ∀ x : Fin 9 → Bool, x v = false → ((⟨g0 :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD (9 + k) false = ((⟨g0 :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD i false)) := by
            intro k hk
            rcases Finset.mem_insert.mp hk with rfl | hkimg
            · refine ⟨by rw [hsz_eq]; simp, Or.inr ?_⟩
              rcases hv01 with rfl | rfl
              · refine ⟨1, by omega, fun x hx0 => ?_⟩
                rw [Nat.add_zero, hfirst x, hx0, Bool.false_or, hwires_D x, hwires_eq]
                rw [hkeep gs (row x) 1 (by simp [row])]
                dsimp only [row]
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
                simp
              · refine ⟨0, by omega, fun x hx1 => ?_⟩
                rw [Nat.add_zero, hfirst x, hx1, Bool.or_false, hwires_D x, hwires_eq]
                rw [hkeep gs (row x) 0 (by simp [row])]
                dsimp only [row]
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
                simp
            · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hkimg
              obtain ⟨hjlt, hjcase⟩ := hS j hj
              refine ⟨by rw [hsz_eq] at hjlt ⊢; simp [D] at hjlt; simp; omega, ?_⟩
              have hidx : 9 + (j + 1) = 10 + j := by omega
              rw [hidx]
              rcases hjcase with ⟨b, hb⟩ | ⟨i, hilt, hi⟩
              · exact Or.inl ⟨b, fun x hxv => by rw [hwires_D x]; exact hb x hxv⟩
              · exact Or.inr ⟨i, hilt, fun x hxv => by rw [hwires_D x]; exact hi x hxv⟩
          have hle3 := hfew v hv S' hS'
          omega
        · rw [if_neg hv01]
          let S' : Finset ℕ := S.image (· + 1)
          have hcard : S'.card = S.card := Finset.card_image_of_injective _ (fun _ _ h => by omega)
          have hS' : ∀ k ∈ S', k < (⟨g0 :: gs, out⟩ : Circuit).size ∧
              ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → ((⟨g0 :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD (9 + k) false = b) ∨
               (∃ i < 9 + k, ∀ x : Fin 9 → Bool, x v = false → ((⟨g0 :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD (9 + k) false = ((⟨g0 :: gs, out⟩ : Circuit).wires (List.ofFn x)).getD i false)) := by
            intro k hk
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
            obtain ⟨hjlt, hjcase⟩ := hS j hj
            refine ⟨by rw [hsz_eq] at hjlt ⊢; simp [D] at hjlt; simp; omega, ?_⟩
            have hidx : 9 + (j + 1) = 10 + j := by omega
            rw [hidx]
            rcases hjcase with ⟨b, hb⟩ | ⟨i, hilt, hi⟩
            · exact Or.inl ⟨b, fun x hxv => by rw [hwires_D x]; exact hb x hxv⟩
            · exact Or.inr ⟨i, hilt, fun x hxv => by rw [hwires_D x]; exact hi x hxv⟩
          have hle3 := hfew v hv S' hS'
          omega
      have hDbound := h_mono D hDmono hDcorrect hDfew
      rw [hsz_eq] at hDbound ⊢
      simp only [D, List.length_cons] at hDbound ⊢
      omega
