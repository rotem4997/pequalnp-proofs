import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8297_37
    (h1 : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 10 → Bool, x 9 = false →
        C.eval (List.ofFn x) =
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
            (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) →
      15 + notCount C ≤ C.size)
    (h2 : ∀ (A B : Circuit), Monotone2 A → Monotone2 B →
      17 ≤ A.size + B.size → A.size + B.size ≤ 18 →
      ¬ ∀ x : Fin 10 → Bool,
        B.eval (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)]) =
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
            (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
    (h3 : ∀ (A B : Circuit), FanInTwo A → Monotone2 B →
      notCount A = 1 → A.size + B.size = 18 →
      ¬ ∀ x : Fin 10 → Bool,
        B.eval (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)]) =
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
            (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.Monotone2 x3 → x2.size + x3.size ≤ (18 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [!x2.eval (List.ofFn x7)]) = x1 x7 := by
  dsimp only
  intro A B hA hB hsz hcomp
  let fPet : (Fin 10 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  have hfPet_eq : ∀ x : Fin 10 → Bool,
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
       x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) = fPet x := by
    intro x
    dsimp only [fPet, List.any_cons, List.any_nil]
    simp only [Bool.or_false]
    change _ = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) ||
      ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) ||
      ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) ||
      ((x 9 && x 6) || ((x 6 && x 8) || (x 8 && x 5)))))))))))))))
    ac_rfl
  have hcompF : ∀ x : Fin 10 → Bool,
      B.eval (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)]) = fPet x :=
    fun x => (hcomp x).trans (hfPet_eq x)
  -- Basic circuit execution helpers
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have hrun_nil : ∀ w, run [] w = w := fun _ => rfl
  have hrun_cons : ∀ g gs w, run (g :: gs) w = run gs (step w g) := fun _ _ _ => rfl
  have hrun_append : ∀ gs hs w, run (gs ++ hs) w = run hs (run gs w) := by
    intro gs hs w; simp [run, List.foldl_append]
  have hrun_len : ∀ gs w, (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih => intro w; rw [hrun_cons, ih]; simp [step]; omega
  have hrun_getD_lt : ∀ gs w i, i < w.length → (run gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [hrun_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have hstep_last : ∀ w g,
      (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro w g; simp [step]
  have heval_and : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have heval_or : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have heval_not : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  -- Counting binary (AND/OR) gates vs NOT gates
  let isBin : Gate → Bool := fun g => !g.op.eval [false]
  let binCount : List Gate → ℕ := fun gs => gs.countP isBin
  have hisBin_and : ∀ ins, isBin ⟨GateOp.and, ins⟩ = true := fun _ => rfl
  have hisBin_or : ∀ ins, isBin ⟨GateOp.or, ins⟩ = true := fun _ => rfl
  have hisBin_not : ∀ ins, isBin ⟨GateOp.not, ins⟩ = false := fun _ => rfl
  have hbin_nil : binCount [] = 0 := rfl
  have hbin_cons : ∀ g gs, binCount (g :: gs) = binCount gs + if isBin g then 1 else 0 := by
    intro g gs; exact List.countP_cons
  have hbin_append : ∀ gs hs, binCount (gs ++ hs) = binCount gs + binCount hs := by
    intro gs hs; exact List.countP_append
  have hbin_add_not : ∀ (C : Circuit), FanInTwo C → binCount C.gates + notCount C = C.size := by
    intro C hC
    change C.gates.countP isBin +
      (C.gates.filter (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not))).length =
      C.gates.length
    have hgo : ∀ (gs : List Gate),
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
        gs.countP isBin +
          (gs.filter (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not))).length =
        gs.length := by
      intro gs
      induction gs with
      | nil => intro _; rfl
      | cons g gs ih =>
        intro hgs
        have hg := hgs g List.mem_cons_self
        have htl := ih (fun h hh => hgs h (List.mem_cons_of_mem _ hh))
        rcases g with ⟨op, ins⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · rw [List.countP_cons, hisBin_and, List.filter_cons, List.length_cons]
          have hne : @decide (GateOp.and = GateOp.not) (lineDegreeGateOpDecEq GateOp.and GateOp.not) = false := rfl
          rw [hne]; simp; omega
        · rw [List.countP_cons, hisBin_or, List.filter_cons, List.length_cons]
          have hne : @decide (GateOp.or = GateOp.not) (lineDegreeGateOpDecEq GateOp.or GateOp.not) = false := rfl
          rw [hne]; simp; omega
        · rw [List.countP_cons, hisBin_not, List.filter_cons, List.length_cons]
          have heq : @decide (GateOp.not = GateOp.not) (lineDegreeGateOpDecEq GateOp.not GateOp.not) = true := rfl
          rw [heq]; simp; omega
    exact hgo C.gates (fun g hg => (hC g hg).1)
  have h1_bin : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 10 → Bool, x 9 = false → C.eval (List.ofFn x) = fPet x) →
      15 ≤ binCount C.gates := by
    intro C hC hev
    have h1c := h1 C hC hev
    have hsum := hbin_add_not C hC
    omega
  -- Petersen vertex-transitive automorphisms sending v to 9
  let permRows : List (List (Fin 10)) :=
    [[9, 6, 8, 5, 7, 4, 1, 3, 0, 2],
     [6, 9, 7, 5, 8, 1, 4, 2, 0, 3],
     [5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
     [5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
     [6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
     [4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
     [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let perm : Fin 10 → Fin 10 → Fin 10 := fun v i => (permRows.getD v.val []).getD i.val 0
  have hperm_self : ∀ v : Fin 10, perm v v = 9 := by
    dsimp only [perm, permRows]; decide
  have hperm_aut : ∀ (v : Fin 10) (x : Fin 10 → Bool), fPet (fun i => x (perm v i)) = fPet x := by
    intro v x
    let edgeList : List (Fin 10 × Fin 10) :=
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
       (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
    have hf_edges : ∀ y : Fin 10 → Bool, fPet y = edgeList.any (fun e => y e.1 && y e.2) := by
      intro y
      dsimp only [fPet, edgeList, List.any_cons, List.any_nil]
      rfl
    have hdir1 : ∀ u : Fin 10,
        edgeList.all (fun e => edgeList.any (fun e' =>
          (perm u e.1 == e'.1 && perm u e.2 == e'.2) || (perm u e.1 == e'.2 && perm u e.2 == e'.1))) = true := by
      dsimp only [perm, permRows, edgeList]; decide
    have hdir2 : ∀ u : Fin 10,
        edgeList.all (fun e' => edgeList.any (fun e =>
          (perm u e.1 == e'.1 && perm u e.2 == e'.2) || (perm u e.1 == e'.2 && perm u e.2 == e'.1))) = true := by
      dsimp only [perm, permRows, edgeList]; decide
    rw [hf_edges (fun i => x (perm v i)), hf_edges x, Bool.eq_iff_iff]
    constructor
    · intro h
      rw [List.any_eq_true] at h ⊢
      obtain ⟨e, he, hev⟩ := h
      have hm := List.all_eq_true.mp (hdir1 v) e he
      rw [List.any_eq_true] at hm
      obtain ⟨e', he', heq⟩ := hm
      refine ⟨e', he', ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨h1' ▸ hev.1, h2' ▸ hev.2⟩
      · exact ⟨h2' ▸ hev.2, h1' ▸ hev.1⟩
    · intro h
      rw [List.any_eq_true] at h ⊢
      obtain ⟨e', he', hev⟩ := h
      have hm := List.all_eq_true.mp (hdir2 v) e' he'
      rw [List.any_eq_true] at hm
      obtain ⟨e, he, heq⟩ := hm
      refine ⟨e, he, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨by rw [h1']; exact hev.1, by rw [h2']; exact hev.2⟩
      · exact ⟨by rw [h1']; exact hev.2, by rw [h2']; exact hev.1⟩
  -- Petersen non-degeneracy: depends on every var, not a 1-var func, 4 cofactors distinct for any pair
  have hfPet_dep : ∀ v : Fin 10, ∃ a : Fin 10, a ≠ v ∧
      fPet (fun k => decide (k = a)) ≠ fPet (fun k => decide (k = v ∨ k = a)) := by
    dsimp only [fPet]; decide
  have hfPet_not_lit : ∀ (v : Fin 10) (neg : Bool),
      ∃ x : Fin 10 → Bool, (if neg then !(x v) else x v) ≠ fPet x := by
    intro v neg
    cases neg with
    | false =>
      refine ⟨fun k => decide (k = v), ?_⟩
      revert v; dsimp only [fPet]; decide
    | true =>
      refine ⟨fun _ => false, ?_⟩
      revert v; dsimp only [fPet]; decide
  have hfPet_four : ∀ (a b : Fin 10), a ≠ b →
      ∀ (p1 q1 p2 q2 : Bool), (p1, q1) ≠ (p2, q2) →
        ∃ (c : Option (Fin 10)),
          let z : Fin 10 → Bool := fun k =>
            @Option.casesOn (Fin 10) (fun _ => Bool) c false (fun u => decide (k = u))
          fPet (fun k => if k = a then p1 else if k = b then q1 else z k) ≠
          fPet (fun k => if k = a then p2 else if k = b then q2 else z k) := by
    dsimp only [fPet]; decide
  -- Symbolic compiler absorbing NOTs and eliminating constant/same-wire binary gates
  let evalVal : List Bool → Sum Bool (Bool × ℕ) → Bool := fun w v =>
    @Sum.casesOn Bool (Bool × ℕ) (fun _ => Bool) v
      (fun b => b)
      (fun p => if p.1 then !(w.getD p.2 false) else w.getD p.2 false)
  let negVal : Sum Bool (Bool × ℕ) → Sum Bool (Bool × ℕ) := fun v =>
    @Sum.casesOn Bool (Bool × ℕ) (fun _ => Sum Bool (Bool × ℕ)) v
      (fun b => Sum.inl (!b))
      (fun p => Sum.inr (!p.1, p.2))
  have hevalVal_neg : ∀ w v, evalVal w (negVal v) = !(evalVal w v) := by
    intro w v
    cases v with
    | inl b => rfl
    | inr p => rcases p with ⟨neg, i⟩; cases neg <;> simp [evalVal, negVal]
  let getV : List (Sum Bool (Bool × ℕ)) → ℕ → Sum Bool (Bool × ℕ) := fun env i =>
    env.getD i (Sum.inl false)
  let emitNot : Bool → ℕ → List Gate → ℕ × List Gate := fun neg i gs' =>
    if neg then (10 + gs'.length, gs' ++ [⟨GateOp.not, [i]⟩]) else (i, gs')
  let evalBin : Bool → Sum Bool (Bool × ℕ) → Sum Bool (Bool × ℕ) → List Gate →
      Sum Bool (Bool × ℕ) × List Gate := fun isOr va vb gs' =>
    @Sum.casesOn Bool (Bool × ℕ) (fun _ => Sum Bool (Bool × ℕ) × List Gate) va
      (fun b =>
        if isOr then (if b then (Sum.inl true, gs') else (vb, gs'))
        else (if b then (vb, gs') else (Sum.inl false, gs')))
      (fun pa =>
        @Sum.casesOn Bool (Bool × ℕ) (fun _ => Sum Bool (Bool × ℕ) × List Gate) vb
          (fun b =>
            if isOr then (if b then (Sum.inl true, gs') else (Sum.inr pa, gs'))
            else (if b then (Sum.inr pa, gs') else (Sum.inl false, gs')))
          (fun pb =>
            if pa.2 = pb.2 then
              if pa.1 = pb.1 then (Sum.inr pa, gs') else (Sum.inl isOr, gs')
            else
              let r1 := emitNot pa.1 pa.2 gs'
              let r2 := emitNot pb.1 pb.2 r1.2
              let op := if isOr then GateOp.or else GateOp.and
              (Sum.inr (false, 10 + r2.2.length), r2.2 ++ [⟨op, [r1.1, r2.1]⟩])))
  let compStep : (List (Sum Bool (Bool × ℕ)) × List Gate) → Gate →
      (List (Sum Bool (Bool × ℕ)) × List Gate) := fun st g =>
    let env := st.1
    let gs' := st.2
    @GateOp.casesOn (fun _ => List (Sum Bool (Bool × ℕ)) × List Gate) g.op
      (@List.casesOn ℕ (fun _ => List (Sum Bool (Bool × ℕ)) × List Gate) g.inputs
        (env ++ [Sum.inl true], gs')
        (fun a t =>
          @List.casesOn ℕ (fun _ => List (Sum Bool (Bool × ℕ)) × List Gate) t
            (env ++ [getV env a], gs')
            (fun b _ =>
              let r := evalBin false (getV env a) (getV env b) gs'
              (env ++ [r.1], r.2))))
      (@List.casesOn ℕ (fun _ => List (Sum Bool (Bool × ℕ)) × List Gate) g.inputs
        (env ++ [Sum.inl false], gs')
        (fun a t =>
          @List.casesOn ℕ (fun _ => List (Sum Bool (Bool × ℕ)) × List Gate) t
            (env ++ [getV env a], gs')
            (fun b _ =>
              let r := evalBin true (getV env a) (getV env b) gs'
              (env ++ [r.1], r.2))))
      (let v := @List.casesOn ℕ (fun _ => Sum Bool (Bool × ℕ)) g.inputs
         (Sum.inl true) (fun a _ => negVal (getV env a))
       (env ++ [v], gs'))
      (fun _ => (env ++ [Sum.inl false], gs'))
      (env ++ [Sum.inl false], gs')
  let compLoop : List Gate → List (Sum Bool (Bool × ℕ)) × List Gate →
      List (Sum Bool (Bool × ℕ)) × List Gate := fun gs st => gs.foldl compStep st
  let finish : ℕ → List (Sum Bool (Bool × ℕ)) × List Gate → Circuit := fun out st =>
    @Sum.casesOn Bool (Bool × ℕ) (fun _ => Circuit) (getV st.1 out)
      (fun b =>
        @Bool.casesOn (fun _ => Circuit) b
          ⟨st.2, 10 + st.2.length⟩
          ⟨st.2 ++ [⟨GateOp.not, [10 + st.2.length]⟩], 10 + st.2.length⟩)
      (fun p =>
        let r := emitNot p.1 p.2 st.2
        ⟨r.2, r.1⟩)
  let fanG : Gate → Prop := fun g =>
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  let wfEnv : List (Sum Bool (Bool × ℕ)) → ℕ → Prop := fun env m =>
    ∀ v ∈ env, ∀ neg i, v = Sum.inr (neg, i) → i < m
  have hgetV_wf : ∀ env m a neg i, wfEnv env m → getV env a = Sum.inr (neg, i) → i < m := by
    intro env m a neg i hwf hget
    by_cases ha : a < env.length
    · rw [show getV env a = env[a] from List.getD_eq_getElem env (Sum.inl false) ha] at hget
      exact hwf _ (List.getElem_mem ha) neg i hget
    · rw [show getV env a = Sum.inl false from List.getD_eq_default env (Sum.inl false) (by omega)] at hget
      cases hget
  have hemitNot_props : ∀ (neg : Bool) (i : ℕ) (gs' : List Gate),
      i < 10 + gs'.length →
      (∀ g ∈ gs', fanG g) →
      let r := emitNot neg i gs'
      (∃ ext, r.2 = gs' ++ ext) ∧
      r.1 < 10 + r.2.length ∧
      binCount r.2 = binCount gs' ∧
      (∀ g ∈ r.2, fanG g) ∧
      ∀ (y : List Bool), y.length = 10 →
        (run r.2 y).getD r.1 false = (if neg then !((run gs' y).getD i false) else (run gs' y).getD i false) := by
    intro neg i gs' hi hfg
    cases neg with
    | false =>
      refine ⟨⟨[], by simp [emitNot]⟩, hi, rfl, hfg, fun y _ => rfl⟩
    | true =>
      dsimp only [emitNot]; rw [if_pos rfl]
      refine ⟨⟨[⟨GateOp.not, [i]⟩], rfl⟩, by simp, ?_, ?_, ?_⟩
      · rw [hbin_append, hbin_cons, hbin_nil, hisBin_not]; simp
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hfg g hg
        · exact ⟨by simp, by simp⟩
      · intro y hy
        rw [hrun_append, hrun_cons, hrun_nil]
        have hlen : (run gs' y).length = 10 + gs'.length := by rw [hrun_len, hy]
        rw [← hlen, hstep_last, heval_not]
        simp
  have hevalBin_props : ∀ (isOr : Bool) (va vb : Sum Bool (Bool × ℕ)) (gs' : List Gate),
      (∀ neg i, va = Sum.inr (neg, i) → i < 10 + gs'.length) →
      (∀ neg i, vb = Sum.inr (neg, i) → i < 10 + gs'.length) →
      (∀ g ∈ gs', fanG g) →
      let r := evalBin isOr va vb gs'
      (∃ ext, r.2 = gs' ++ ext) ∧
      (∀ neg i, r.1 = Sum.inr (neg, i) → i < 10 + r.2.length) ∧
      binCount r.2 ≤ binCount gs' + 1 ∧
      ((∃ b, va = Sum.inl b) ∨ (∃ b, vb = Sum.inl b) → binCount r.2 = binCount gs') ∧
      (∀ g ∈ r.2, fanG g) ∧
      ∀ (y : List Bool), y.length = 10 →
        evalVal (run r.2 y) r.1 =
          (if isOr then evalVal (run gs' y) va || evalVal (run gs' y) vb
           else evalVal (run gs' y) va && evalVal (run gs' y) vb) := by
    intro isOr va vb gs' hva hvb hfg
    cases va with
    | inl ba =>
      cases isOr <;> cases ba <;>
        refine ⟨⟨[], by simp [evalBin]⟩, ?_, by simp [evalBin], fun _ => rfl, hfg, fun y _ => by simp [evalBin, evalVal]⟩
      · intro neg i h; cases h
      · exact hvb
      · exact hvb
      · intro neg i h; cases h
    | inr pa =>
      rcases pa with ⟨na, wa⟩
      cases vb with
      | inl bb =>
        cases isOr <;> cases bb <;>
          refine ⟨⟨[], by simp [evalBin]⟩, ?_, by simp [evalBin], fun _ => rfl, hfg, fun y _ => by simp [evalBin, evalVal]⟩
        · intro neg i h; cases h
        · exact hva
        · exact hva
        · intro neg i h; cases h
      | inr pb =>
        rcases pb with ⟨nb, wb⟩
        by_cases hw : wa = wb
        · subst hw
          by_cases hn : na = nb
          · subst hn
            dsimp only [evalBin]; rw [if_pos rfl, if_pos rfl]; dsimp only
            refine ⟨⟨[], by simp⟩, hva, Nat.le_succ _, ?_, hfg, ?_⟩
            · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> cases h
            · intro y _; cases isOr <;> simp [evalVal]
          · dsimp only [evalBin]; rw [if_pos rfl, if_neg hn]; dsimp only
            refine ⟨⟨[], by simp⟩, ?_, Nat.le_succ _, ?_, hfg, ?_⟩
            · intro neg i h; cases h
            · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> cases h
            · intro y _; cases isOr <;> cases na <;> cases nb <;> simp_all [evalVal]
        · have hwa : wa < 10 + gs'.length := hva na wa rfl
          have hwb : wb < 10 + gs'.length := hvb nb wb rfl
          obtain ⟨⟨e1, he1⟩, hw1, hb1, hf1, hev1⟩ := hemitNot_props na wa gs' hwa hfg
          have hwb1 : wb < 10 + (emitNot na wa gs').2.length := by rw [he1, List.length_append]; omega
          obtain ⟨⟨e2, he2⟩, hw2, hb2, hf2, hev2⟩ := hemitNot_props nb wb (emitNot na wa gs').2 hwb1 hf1
          let r1 := emitNot na wa gs'
          let r2 := emitNot nb wb r1.2
          let op := if isOr then GateOp.or else GateOp.and
          have hbn_op : isBin ⟨op, [r1.1, r2.1]⟩ = true := by cases isOr <;> rfl
          dsimp only [evalBin]; rw [if_neg hw]; dsimp only
          refine ⟨⟨e1 ++ e2 ++ [⟨op, [r1.1, r2.1]⟩], ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
          · change r2.2 ++ [⟨op, [r1.1, r2.1]⟩] = _
            rw [he2, he1]; simp [List.append_assoc]
          · intro neg i h; cases h; simp
          · change binCount (r2.2 ++ [⟨op, [r1.1, r2.1]⟩]) ≤ binCount gs' + 1
            rw [hbin_append, hbin_cons, hbin_nil, hbn_op, if_pos rfl]
            rw [hb2, hb1]
          · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> cases h
          · intro g hg
            simp only [List.mem_append, List.mem_singleton] at hg
            rcases hg with hg | rfl
            · exact hf2 g hg
            · exact ⟨by cases isOr <;> simp, by simp⟩
          · intro y hy
            change (run (r2.2 ++ [⟨op, [r1.1, r2.1]⟩]) y).getD (10 + r2.2.length) false = _
            have hlen2 : (run r2.2 y).length = 10 + r2.2.length := by rw [hrun_len, hy]
            rw [hrun_append, hrun_cons, hrun_nil, ← hlen2, hstep_last]
            have h1get : (run r2.2 y).getD r1.1 false = (run r1.2 y).getD r1.1 false := by
              rw [he2, hrun_append, hrun_getD_lt _ _ _ (by rw [hrun_len, hy]; exact hw1)]
            have hev1' : (run r1.2 y).getD r1.1 false =
                (if na then !((run gs' y).getD wa false) else (run gs' y).getD wa false) := hev1 y hy
            have h2get : (run r2.2 y).getD r2.1 false =
                (if nb then !((run r1.2 y).getD wb false) else (run r1.2 y).getD wb false) := hev2 y hy
            have hwbget : (run r1.2 y).getD wb false = (run gs' y).getD wb false := by
              rw [he1, hrun_append, hrun_getD_lt _ _ _ (by rw [hrun_len, hy]; exact hwb)]
            simp only [List.map_cons, List.map_nil, h1get, hev1', h2get, hwbget]
            cases isOr with
            | false => simp [op, heval_and, evalVal]
            | true => simp [op, heval_or, evalVal]
  have hcompStep_props : ∀ (g : Gate) (st : List (Sum Bool (Bool × ℕ)) × List Gate),
      fanG g → wfEnv st.1 (10 + st.2.length) → (∀ h ∈ st.2, fanG h) →
      let st1 := compStep st g
      (∃ ext, st1.2 = st.2 ++ ext) ∧
      wfEnv st1.1 (10 + st1.2.length) ∧
      st1.1.length = st.1.length + 1 ∧
      (∀ i < st.1.length, getV st1.1 i = getV st.1 i) ∧
      (∀ h ∈ st1.2, fanG h) ∧
      binCount st1.2 ≤ binCount st.2 + (if isBin g then 1 else 0) ∧
      ((isBin g = true ∧ (∃ a ∈ g.inputs, ∃ b, getV st.1 a = Sum.inl b)) → binCount st1.2 = binCount st.2) ∧
      ∀ (y w : List Bool), y.length = 10 → w.length = st.1.length →
        (∀ i < st.1.length, evalVal (run st.2 y) (getV st.1 i) = w.getD i false) →
        ∀ i < st1.1.length, evalVal (run st1.2 y) (getV st1.1 i) = (step w g).getD i false := by
    intro g st hg hwf hfg
    rcases st with ⟨env, gs'⟩
    dsimp only at hwf hfg ⊢
    have hwf_ext : ∀ (v : Sum Bool (Bool × ℕ)) (gs1 : List Gate),
        (∃ ext, gs1 = gs' ++ ext) →
        (∀ neg i, v = Sum.inr (neg, i) → i < 10 + gs1.length) →
        wfEnv (env ++ [v]) (10 + gs1.length) := by
      intro v gs1 hex hv u hu neg i heq
      rcases hex with ⟨ext, hext⟩
      rw [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · have := hwf u hu neg i heq; rw [hext, List.length_append]; omega
      · exact hv neg i heq
    have hpres : ∀ (v : Sum Bool (Bool × ℕ)) (gs1 : List Gate) (ext : List Gate),
        gs1 = gs' ++ ext →
        ∀ (y w : List Bool), y.length = 10 → w.length = env.length →
          (∀ i < env.length, evalVal (run gs' y) (getV env i) = w.getD i false) →
          evalVal (run gs1 y) v = g.op.eval (g.inputs.map fun i => w.getD i false) →
          ∀ i < (env ++ [v]).length, evalVal (run gs1 y) (getV (env ++ [v]) i) = (step w g).getD i false := by
      intro v gs1 ext hext y w hy hw hinv hlast i hi
      by_cases hilt : i < env.length
      · have hget : getV (env ++ [v]) i = getV env i := List.getD_append _ _ _ _ hilt
        rw [hget]
        have hstep_lt : (step w g).getD i false = w.getD i false :=
          List.getD_append _ _ _ _ (by omega)
        rw [hstep_lt, ← hinv i hilt]
        cases hgi : getV env i with
        | inl b => rfl
        | inr p =>
          rcases p with ⟨neg, idx⟩
          have hidx : idx < 10 + gs'.length := hgetV_wf env _ i neg idx hwf hgi
          simp only [evalVal]
          rw [hext, hrun_append, hrun_getD_lt _ _ _ (by rw [hrun_len, hy]; exact hidx)]
      · have hieq : i = env.length := by simp at hi; omega
        subst hieq
        have hget : getV (env ++ [v]) env.length = v := by simp [getV]
        rw [hget, ← hw, hstep_last, hlast]
    have hget_agree : ∀ (y w : List Bool), w.length = env.length →
        (∀ i < env.length, evalVal (run gs' y) (getV env i) = w.getD i false) →
        ∀ a, evalVal (run gs' y) (getV env a) = w.getD a false := by
      intro y w hw hinv a
      by_cases ha : a < env.length
      · exact hinv a ha
      · rw [show getV env a = Sum.inl false from List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
    rcases g with ⟨op, ins⟩
    rcases hg with ⟨hop, hilen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · -- GateOp.and
      cases ins with
      | nil =>
        dsimp only [compStep]
        refine ⟨⟨[], by simp⟩, hwf_ext _ _ ⟨[], by simp⟩ (fun _ _ h => by cases h),
          by simp, fun i hi => List.getD_append _ _ _ _ hi, hfg, by omega,
          fun _ => rfl, fun y w hy hw hinv => hpres _ _ [] (by simp) y w hy hw hinv rfl⟩
      | cons a t =>
        cases t with
        | nil =>
          dsimp only [compStep]
          refine ⟨⟨[], by simp⟩,
            hwf_ext _ _ ⟨[], by simp⟩ (fun neg i h => hgetV_wf env _ a neg i hwf h),
            by simp, fun i hi => List.getD_append _ _ _ _ hi, hfg, by omega,
            fun _ => rfl, fun y w hy hw hinv => hpres _ _ [] (by simp) y w hy hw hinv
              (by rw [hget_agree y w hw hinv a, heval_and]; simp)⟩
        | cons b rest =>
          have hrest : rest = [] := by cases rest with | nil => rfl | cons _ _ => simp at hilen
          subst hrest
          dsimp only [compStep]
          obtain ⟨⟨ext, hext⟩, hwf1, hb1, helim1, hfg1, hev1⟩ :=
            hevalBin_props false (getV env a) (getV env b) gs'
              (fun neg i h => hgetV_wf env _ a neg i hwf h)
              (fun neg i h => hgetV_wf env _ b neg i hwf h) hfg
          refine ⟨⟨ext, hext⟩, hwf_ext _ _ ⟨ext, hext⟩ hwf1, by simp,
            fun i hi => List.getD_append _ _ _ _ hi, hfg1, by simpa [hisBin_and] using hb1,
            ?_, fun y w hy hw hinv => hpres _ _ ext hext y w hy hw hinv (by
              rw [hev1 y hy, hget_agree y w hw hinv a, hget_agree y w hw hinv b, heval_and]; simp)⟩
          rintro ⟨_, x, hx, bx, hbx⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact helim1 (Or.inl ⟨bx, hbx⟩)
          · exact helim1 (Or.inr ⟨bx, hbx⟩)
    · -- GateOp.or
      cases ins with
      | nil =>
        dsimp only [compStep]
        refine ⟨⟨[], by simp⟩, hwf_ext _ _ ⟨[], by simp⟩ (fun _ _ h => by cases h),
          by simp, fun i hi => List.getD_append _ _ _ _ hi, hfg, by omega,
          fun _ => rfl, fun y w hy hw hinv => hpres _ _ [] (by simp) y w hy hw hinv rfl⟩
      | cons a t =>
        cases t with
        | nil =>
          dsimp only [compStep]
          refine ⟨⟨[], by simp⟩,
            hwf_ext _ _ ⟨[], by simp⟩ (fun neg i h => hgetV_wf env _ a neg i hwf h),
            by simp, fun i hi => List.getD_append _ _ _ _ hi, hfg, by omega,
            fun _ => rfl, fun y w hy hw hinv => hpres _ _ [] (by simp) y w hy hw hinv
              (by rw [hget_agree y w hw hinv a, heval_or]; simp)⟩
        | cons b rest =>
          have hrest : rest = [] := by cases rest with | nil => rfl | cons _ _ => simp at hilen
          subst hrest
          dsimp only [compStep]
          obtain ⟨⟨ext, hext⟩, hwf1, hb1, helim1, hfg1, hev1⟩ :=
            hevalBin_props true (getV env a) (getV env b) gs'
              (fun neg i h => hgetV_wf env _ a neg i hwf h)
              (fun neg i h => hgetV_wf env _ b neg i hwf h) hfg
          refine ⟨⟨ext, hext⟩, hwf_ext _ _ ⟨ext, hext⟩ hwf1, by simp,
            fun i hi => List.getD_append _ _ _ _ hi, hfg1, by simpa [hisBin_or] using hb1,
            ?_, fun y w hy hw hinv => hpres _ _ ext hext y w hy hw hinv (by
              rw [hev1 y hy, hget_agree y w hw hinv a, hget_agree y w hw hinv b, heval_or]; simp)⟩
          rintro ⟨_, x, hx, bx, hbx⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact helim1 (Or.inl ⟨bx, hbx⟩)
          · exact helim1 (Or.inr ⟨bx, hbx⟩)
    · -- GateOp.not
      cases ins with
      | nil =>
        dsimp only [compStep]
        refine ⟨⟨[], by simp⟩, hwf_ext _ _ ⟨[], by simp⟩ (fun _ _ h => by cases h),
          by simp, fun i hi => List.getD_append _ _ _ _ hi, hfg, by omega,
          fun _ => rfl, fun y w hy hw hinv => hpres _ _ [] (by simp) y w hy hw hinv rfl⟩
      | cons a t =>
        dsimp only [compStep]
        refine ⟨⟨[], by simp⟩,
          hwf_ext _ _ ⟨[], by simp⟩ (fun neg i h => by
            cases hga : getV env a with
            | inl b => rw [hga] at h; cases h
            | inr p =>
              rcases p with ⟨n0, i0⟩
              have hi0 := hgetV_wf env _ a n0 i0 hwf hga
              rw [hga] at h; cases h; exact hi0),
          by simp, fun i hi => List.getD_append _ _ _ _ hi, hfg, by omega,
          fun _ => rfl, fun y w hy hw hinv => hpres _ _ [] (by simp) y w hy hw hinv (by
            rw [hevalVal_neg, hget_agree y w hw hinv a, heval_not]; simp)⟩
  have hcompLoop_props : ∀ (gs : List Gate) (st : List (Sum Bool (Bool × ℕ)) × List Gate),
      (∀ g ∈ gs, fanG g) → wfEnv st.1 (10 + st.2.length) → (∀ h ∈ st.2, fanG h) →
      let res := compLoop gs st
      wfEnv res.1 (10 + res.2.length) ∧
      res.1.length = st.1.length + gs.length ∧
      (∀ i < st.1.length, getV res.1 i = getV st.1 i) ∧
      (∀ h ∈ res.2, fanG h) ∧
      binCount res.2 ≤ binCount st.2 + binCount gs ∧
      ∀ (y w : List Bool), y.length = 10 → w.length = st.1.length →
        (∀ i < st.1.length, evalVal (run st.2 y) (getV st.1 i) = w.getD i false) →
        ∀ i < res.1.length, evalVal (run res.2 y) (getV res.1 i) = (run gs w).getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro st _ hwf hfg
      exact ⟨hwf, by simp [compLoop], fun _ _ => rfl, hfg,
        by dsimp only [compLoop, List.foldl_nil]; rw [hbin_nil]; omega,
        fun _ _ _ _ hinv => hinv⟩
    | cons g gs ih =>
      intro st hgs hwf hfg
      have hg : fanG g := hgs g List.mem_cons_self
      have htl : ∀ h ∈ gs, fanG h := fun h hh => hgs h (List.mem_cons_of_mem _ hh)
      obtain ⟨_, hwf1, hlen1, hpres1, hfg1, hb1, _, hev1⟩ := hcompStep_props g st hg hwf hfg
      obtain ⟨hwf2, hlen2, hpres2, hfg2, hb2, hev2⟩ := ih (compStep st g) htl hwf1 hfg1
      refine ⟨hwf2, ?_, ?_, hfg2, ?_, ?_⟩
      · change (compLoop gs (compStep st g)).1.length = st.1.length + (g :: gs).length
        rw [hlen2, hlen1]; simp; omega
      · intro i hi
        change getV (compLoop gs (compStep st g)).1 i = getV st.1 i
        rw [hpres2 i (by omega), hpres1 i hi]
      · change binCount (compLoop gs (compStep st g)).2 ≤ binCount st.2 + binCount (g :: gs)
        rw [hbin_cons]
        cases hbg : isBin g with
        | true => rw [hbg] at hb1; simp only [↓reduceIte] at hb1 ⊢; omega
        | false => rw [hbg] at hb1; simp only [Bool.false_eq_true, ↓reduceIte] at hb1 ⊢; omega
      · intro y w hy hw hinv
        exact hev2 y (step w g) hy (by simp [step, hw, hlen1]) (hev1 y w hy hw hinv)
  have hfinish_props : ∀ (out : ℕ) (st : List (Sum Bool (Bool × ℕ)) × List Gate),
      wfEnv st.1 (10 + st.2.length) → (∀ h ∈ st.2, fanG h) →
      let D := finish out st
      FanInTwo D ∧
      binCount D.gates = binCount st.2 ∧
      ∀ (y : List Bool), y.length = 10 → D.eval y = evalVal (run st.2 y) (getV st.1 out) := by
    intro out st hwf hfg
    cases hv : getV st.1 out with
    | inl b =>
      cases b with
      | false =>
        dsimp only [finish]; rw [hv]
        refine ⟨hfg, rfl, fun y hy => ?_⟩
        change (run st.2 y).getD (10 + st.2.length) false = false
        exact List.getD_eq_default _ _ (by rw [hrun_len, hy])
      | true =>
        dsimp only [finish]; rw [hv]
        refine ⟨?_, ?_, fun y hy => ?_⟩
        · intro g hg
          simp only [List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · exact hfg g hg
          · exact ⟨by simp, by simp⟩
        · rw [hbin_append, hbin_cons, hbin_nil, hisBin_not]; simp
        · change (run (st.2 ++ [⟨GateOp.not, [10 + st.2.length]⟩]) y).getD (10 + st.2.length) false = true
          have hlen : (run st.2 y).length = 10 + st.2.length := by rw [hrun_len, hy]
          rw [hrun_append, hrun_cons, hrun_nil, ← hlen, hstep_last, heval_not]
          simp
    | inr p =>
      rcases p with ⟨neg, w⟩
      have hw : w < 10 + st.2.length := hgetV_wf st.1 _ out neg w hwf hv
      obtain ⟨_, _, hb, hfg1, hev1⟩ := hemitNot_props neg w st.2 hw hfg
      dsimp only [finish]; rw [hv]
      refine ⟨hfg1, hb, fun y hy => ?_⟩
      change (run (emitNot neg w st.2).2 y).getD (emitNot neg w st.2).1 false = _
      exact hev1 y hy
  -- Helper: count how many binary gates get eliminated by compStep along gs
  have hcompLoop_elim : ∀ (gs : List Gate) (env : List (Sum Bool (Bool × ℕ))) (gs' : List Gate)
      (P : List (Sum Bool (Bool × ℕ)) → Gate → Prop),
      (∀ g ∈ gs, fanG g) → wfEnv env (10 + gs'.length) → (∀ h ∈ gs', fanG h) →
      (∀ e g, P e g → isBin g = true ∧ ∃ a ∈ g.inputs, ∃ b, getV e a = Sum.inl b) →
      (∃ pre g post, gs = pre ++ g :: post ∧
        P (compLoop pre (env, gs')).1 g) →
      binCount (compLoop gs (env, gs')).2 + 1 ≤ binCount gs' + binCount gs := by
    intro gs env gs' P hgs hwf hfg hP hex
    rcases hex with ⟨pre, g, post, hsplit, hPg⟩
    subst hsplit
    have hpre_fan : ∀ h ∈ pre, fanG h := fun h hh => hgs h (List.mem_append_left _ hh)
    have hg_fan : fanG g := hgs g (List.mem_append_right _ List.mem_cons_self)
    have hpost_fan : ∀ h ∈ post, fanG h := fun h hh => hgs h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
    have hfold : compLoop (pre ++ g :: post) (env, gs') =
        compLoop post (compStep (compLoop pre (env, gs')) g) := by
      simp [compLoop, List.foldl_append]
    rw [hfold]
    obtain ⟨hwf1, _, _, hfg1, hb1, _⟩ := hcompLoop_props pre (env, gs') hpre_fan hwf hfg
    dsimp only at hb1
    obtain ⟨_, hwf2, _, _, hfg2, _, helim, _⟩ := hcompStep_props g (compLoop pre (env, gs')) hg_fan hwf1 hfg1
    obtain ⟨_, _, _, _, hb3, _⟩ := hcompLoop_props post (compStep (compLoop pre (env, gs')) g) hpost_fan hwf2 hfg2
    have hcond := hP _ _ hPg
    have heq2 : binCount (compStep (compLoop pre (env, gs')) g).2 = binCount (compLoop pre (env, gs')).2 := helim hcond
    have hsplit_bin : binCount (pre ++ g :: post) = binCount pre + 1 + binCount post := by
      rw [hbin_append, hbin_cons, hcond.1, if_pos rfl]; omega
    omega
  have hcompLoop_elim2 : ∀ (gs : List Gate) (env : List (Sum Bool (Bool × ℕ))) (gs' : List Gate)
      (pre : List Gate) (g0 : Gate) (mid : List Gate) (g1 : Gate) (post : List Gate),
      gs = pre ++ g0 :: (mid ++ g1 :: post) →
      (∀ g ∈ gs, fanG g) → wfEnv env (10 + gs'.length) → (∀ h ∈ gs', fanG h) →
      (isBin g0 = true ∧ ∃ a ∈ g0.inputs, ∃ b, getV (compLoop pre (env, gs')).1 a = Sum.inl b) →
      (isBin g1 = true ∧ ∃ a ∈ g1.inputs, ∃ b, getV (compLoop (pre ++ g0 :: mid) (env, gs')).1 a = Sum.inl b) →
      binCount (compLoop gs (env, gs')).2 + 2 ≤ binCount gs' + binCount gs := by
    intro gs env gs' pre g0 mid g1 post hsplit hgs hwf hfg hc0 hc1
    subst hsplit
    have hpre_f : ∀ h ∈ pre, fanG h := fun h hh => hgs h (List.mem_append_left _ hh)
    have hg0_f : fanG g0 := hgs g0 (List.mem_append_right _ List.mem_cons_self)
    have hmid_f : ∀ h ∈ mid, fanG h := fun h hh => hgs h (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hh)))
    have hg1_f : fanG g1 := hgs g1 (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))
    have hpost_f : ∀ h ∈ post, fanG h := fun h hh => hgs h (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hh))))
    let st1 := compLoop pre (env, gs')
    let st2 := compStep st1 g0
    let st3 := compLoop mid st2
    let st4 := compStep st3 g1
    let st5 := compLoop post st4
    have hfold : compLoop (pre ++ g0 :: (mid ++ g1 :: post)) (env, gs') = st5 := by
      simp [st1, st2, st3, st4, st5, compLoop, List.foldl_append]
    have hst3_eq : st3 = compLoop (pre ++ g0 :: mid) (env, gs') := by
      simp [st1, st2, st3, compLoop, List.foldl_append]
    rw [hfold]
    obtain ⟨hwf1, _, _, hfg1, hb1, _⟩ := hcompLoop_props pre (env, gs') hpre_f hwf hfg
    change binCount st1.2 ≤ binCount gs' + binCount pre at hb1
    obtain ⟨_, hwf2, _, _, hfg2, _, helim0, _⟩ := hcompStep_props g0 st1 hg0_f hwf1 hfg1
    have heq2 : binCount st2.2 = binCount st1.2 := helim0 hc0
    obtain ⟨hwf3, _, _, hfg3, hb3, _⟩ := hcompLoop_props mid st2 hmid_f hwf2 hfg2
    change binCount st3.2 ≤ binCount st2.2 + binCount mid at hb3
    obtain ⟨_, hwf4, _, _, hfg4, _, helim1, _⟩ := hcompStep_props g1 st3 hg1_f hwf3 hfg3
    have heq4 : binCount st4.2 = binCount st3.2 := helim1 (hst3_eq ▸ hc1)
    obtain ⟨_, _, _, _, hb5, _⟩ := hcompLoop_props post st4 hpost_f hwf4 hfg4
    change binCount st5.2 ≤ binCount st4.2 + binCount post at hb5
    have htot : binCount (pre ++ g0 :: (mid ++ g1 :: post)) =
        binCount pre + 1 + binCount mid + 1 + binCount post := by
      rw [hbin_append, hbin_cons, hc0.1, if_pos rfl, hbin_append, hbin_cons, hc1.1, if_pos rfl]; omega
    omega
  -- Main theorem: 17 <= binCount C.gates for any FanInTwo C computing fPet
  have h17 : ∀ (k : ℕ), k ≤ 16 →
      ∀ (C : Circuit), FanInTwo C → binCount C.gates = k →
        ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = fPet x := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk16 C hC hbk hCev
      -- First: identity compilation must not reduce binCount
      let initId : List (Sum Bool (Bool × ℕ)) :=
        (List.finRange 10).map (fun i => Sum.inr (false, i.val))
      have hinitId_len : initId.length = 10 := by simp [initId]
      have hinitId_wf : wfEnv initId 10 := by
        intro v hv neg i heq
        simp only [initId, List.mem_map, List.mem_finRange, true_and] at hv
        obtain ⟨j, hj⟩ := hv
        rw [← hj] at heq; cases heq; exact j.isLt
      have hinitId_get : ∀ i : Fin 10, getV initId i.val = Sum.inr (false, i.val) := by
        intro i
        have hi : i.val < initId.length := by rw [hinitId_len]; exact i.isLt
        rw [show getV initId i.val = initId[i.val] from List.getD_eq_getElem _ _ hi]
        simp [initId]
      have hinitId_eval : ∀ (x : Fin 10 → Bool) (i : ℕ), i < initId.length →
          evalVal (List.ofFn x) (getV initId i) = (List.ofFn x).getD i false := by
        intro x i hi
        rw [hinitId_len] at hi
        rw [hinitId_get ⟨i, hi⟩]
        simp [evalVal]
      let stId := compLoop C.gates (initId, [])
      let DId := finish C.output stId
      obtain ⟨hwfId, hlenId, _, hfgId, hbId, hevId⟩ := hcompLoop_props C.gates (initId, []) hC hinitId_wf (fun _ h => by cases h)
      rw [hinitId_len] at hlenId
      obtain ⟨hDId_fan, hDId_bin, hDId_ev⟩ := hfinish_props C.output stId hwfId hfgId
      have hDId_comp : ∀ x : Fin 10 → Bool, DId.eval (List.ofFn x) = fPet x := by
        intro x
        rw [hDId_ev (List.ofFn x) (by simp)]
        by_cases ho : C.output < stId.1.length
        · rw [hevId (List.ofFn x) (List.ofFn x) (by simp) (by simp [hinitId_len]) (hinitId_eval x) C.output ho]
          exact hCev x
        · rw [show getV stId.1 C.output = Sum.inl false from List.getD_eq_default _ _ (by omega)]
          have hco : C.eval (List.ofFn x) = false := by
            change (run C.gates (List.ofFn x)).getD C.output false = false
            dsimp only [stId] at ho
            exact List.getD_eq_default _ _ (by rw [hrun_len, List.length_ofFn]; omega)
          rw [← hCev x, hco]
      have hnoDrop : binCount stId.2 = k := by
        by_contra hne
        have hlt : binCount DId.gates < k := by
          rw [hDId_bin]
          dsimp only [stId] at hne ⊢
          rw [hbin_nil] at hbId
          omega
        exact ih (binCount DId.gates) hlt (by omega) DId hDId_fan rfl hDId_comp
      -- Restriction compiler fixing vertex v to false via perm v
      let initZero (v : Fin 10) : List (Sum Bool (Bool × ℕ)) :=
        (List.finRange 10).map (fun i => if i = v then Sum.inl false else Sum.inr (false, (perm v i).val))
      have hiz_len : ∀ v, (initZero v).length = 10 := fun v => by simp [initZero]
      have hiz_wf : ∀ v, wfEnv (initZero v) 10 := by
        intro v u hu neg idx heq
        simp only [initZero, List.mem_map, List.mem_finRange, true_and] at hu
        obtain ⟨j, hj⟩ := hu
        by_cases hjv : j = v
        · rw [if_pos hjv] at hj; rw [← hj] at heq; cases heq
        · rw [if_neg hjv] at hj; rw [← hj] at heq; cases heq; exact (perm v j).isLt
      have hiz_get : ∀ v (i : Fin 10),
          getV (initZero v) i.val = if i = v then Sum.inl false else Sum.inr (false, (perm v i).val) := by
        intro v i
        have hi : i.val < (initZero v).length := by rw [hiz_len]; exact i.isLt
        rw [show getV (initZero v) i.val = (initZero v)[i.val] from List.getD_eq_getElem _ _ hi]
        simp [initZero]
      have hiz_comp : ∀ (v : Fin 10),
          let Dv := finish C.output (compLoop C.gates (initZero v, []))
          FanInTwo Dv ∧
          binCount Dv.gates = binCount (compLoop C.gates (initZero v, [])).2 ∧
          15 ≤ binCount (compLoop C.gates (initZero v, [])).2 := by
        intro v
        obtain ⟨hwfv, hlenv, _, hfgv, _, hevv⟩ :=
          hcompLoop_props C.gates (initZero v, []) hC (hiz_wf v) (fun _ h => by cases h)
        rw [hiz_len] at hlenv
        obtain ⟨hDv_fan, hDv_bin, hDv_ev⟩ := hfinish_props C.output _ hwfv hfgv
        refine ⟨hDv_fan, hDv_bin, ?_⟩
        rw [← hDv_bin]
        apply h1_bin _ hDv_fan
        intro x hx9
        rw [hDv_ev (List.ofFn x) (by simp)]
        let xp : Fin 10 → Bool := fun i => x (perm v i)
        have hinit_ev : ∀ i < (initZero v).length,
            evalVal (List.ofFn x) (getV (initZero v) i) = (List.ofFn xp).getD i false := by
          intro i hi
          rw [hiz_len] at hi
          rw [hiz_get v ⟨i, hi⟩]
          have hgetp : (List.ofFn xp).getD i false = xp ⟨i, hi⟩ := by
            rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]
          rw [hgetp]
          by_cases hiv : (⟨i, hi⟩ : Fin 10) = v
          · rw [if_pos hiv, hiv]; dsimp only [evalVal, xp]; rw [hperm_self, hx9]
          · rw [if_neg hiv]; dsimp only [evalVal, xp]
            rw [if_neg Bool.false_ne_true, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        by_cases ho : C.output < (compLoop C.gates (initZero v, [])).1.length
        · rw [hevv (List.ofFn x) (List.ofFn xp) (by simp) (by simp [hiz_len]) hinit_ev C.output ho]
          exact (hCev xp).trans (hperm_aut v x)
        · rw [show getV (compLoop C.gates (initZero v, [])).1 C.output = Sum.inl false from
            List.getD_eq_default _ _ (by omega)]
          have hco : C.eval (List.ofFn xp) = false := by
            change (run C.gates (List.ofFn xp)).getD C.output false = false
            exact List.getD_eq_default _ _ (by rw [hrun_len, List.length_ofFn]; omega)
          rw [← hperm_aut v x, ← hCev xp, hco]
      -- Key invariant: because no binary gate drops in stId, every binary gate in C emits a wire >= 10
      -- in stId, so any wire with stId value inr (_, v) (v < 10) becomes inl _ in initZero v.
      have hstep_full : ∀ (pre : List Gate) (g : Gate) (post : List Gate),
          C.gates = pre ++ g :: post → isBin g = true →
          let stP := compLoop pre (initId, [])
          ∃ a b na nb wa wb,
            g.inputs = [a, b] ∧
            getV stP.1 a = Sum.inr (na, wa) ∧
            getV stP.1 b = Sum.inr (nb, wb) ∧
            wa ≠ wb ∧
            ∃ wNew ≥ 10, (compStep stP g).1 = stP.1 ++ [Sum.inr (false, wNew)] := by
        intro pre g post hsp hbin
        have hpre_f : ∀ h ∈ pre, fanG h := fun h hh => hC h (hsp ▸ List.mem_append_left _ hh)
        have hg_f : fanG g := hC g (hsp ▸ List.mem_append_right _ List.mem_cons_self)
        have hpost_f : ∀ h ∈ post, fanG h := fun h hh => hC h (hsp ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
        have hfold : stId = compLoop post (compStep (compLoop pre (initId, [])) g) := by
          simp [stId, hsp, compLoop, List.foldl_append]
        obtain ⟨hwf1, _, _, hfg1, hb1, _⟩ := hcompLoop_props pre (initId, []) hpre_f hinitId_wf (fun _ h => by cases h)
        obtain ⟨_, hwf2, _, _, hfg2, hstep_le0, _, _⟩ := hcompStep_props g (compLoop pre (initId, [])) hg_f hwf1 hfg1
        obtain ⟨_, _, _, _, hb3, _⟩ := hcompLoop_props post (compStep (compLoop pre (initId, [])) g) hpost_f hwf2 hfg2
        have hinc : binCount (compStep (compLoop pre (initId, [])) g).2 =
            binCount (compLoop pre (initId, [])).2 + 1 := by
          have hsplit_b : k = binCount pre + 1 + binCount post := by
            rw [← hbk, hsp, hbin_append, hbin_cons, hbin, if_pos rfl]; omega
          have hno : binCount (compLoop post (compStep (compLoop pre (initId, [])) g)).2 = k := by
            rw [← hfold]; exact hnoDrop
          have hstep_le : binCount (compStep (compLoop pre (initId, [])) g).2 ≤
              binCount (compLoop pre (initId, [])).2 + 1 := by
            rw [hbin, if_pos rfl] at hstep_le0; exact hstep_le0
          rw [hbin_nil] at hb1
          omega
        rcases g with ⟨op, ins⟩
        rcases hg_f with ⟨hop, hilen⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hnot_not : op ≠ GateOp.not := by intro h; subst h; simp [hisBin_not] at hbin
        rcases hop with rfl | rfl | rfl
        · -- and
          cases ins with
          | nil => simp [compStep] at hinc
          | cons a t =>
            cases t with
            | nil => simp [compStep] at hinc
            | cons b rest =>
              have hr : rest = [] := by cases rest with | nil => rfl | cons _ _ => simp at hilen
              subst hr
              dsimp only [compStep] at hinc ⊢
              cases hva : getV (compLoop pre (initId, [])).1 a with
              | inl ba =>
                cases ba <;> simp [evalBin, hva] at hinc
              | inr pa =>
                rcases pa with ⟨na, wa⟩
                cases hvb : getV (compLoop pre (initId, [])).1 b with
                | inl bb =>
                  cases bb <;> simp [evalBin, hva, hvb] at hinc
                | inr pb =>
                  rcases pb with ⟨nb, wb⟩
                  by_cases hw : wa = wb
                  · subst hw; by_cases hn : na = nb <;> simp [evalBin, hva, hvb, hn] at hinc
                  · refine ⟨a, b, na, nb, wa, wb, rfl, hva, hvb, hw,
                      10 + (emitNot nb wb (emitNot na wa (compLoop pre (initId, [])).2).2).2.length,
                      by omega, ?_⟩
                    simp [evalBin, hw]
        · -- or
          cases ins with
          | nil => simp [compStep] at hinc
          | cons a t =>
            cases t with
            | nil => simp [compStep] at hinc
            | cons b rest =>
              have hr : rest = [] := by cases rest with | nil => rfl | cons _ _ => simp at hilen
              subst hr
              dsimp only [compStep] at hinc ⊢
              cases hva : getV (compLoop pre (initId, [])).1 a with
              | inl ba =>
                cases ba <;> simp [evalBin, hva] at hinc
              | inr pa =>
                rcases pa with ⟨na, wa⟩
                cases hvb : getV (compLoop pre (initId, [])).1 b with
                | inl bb =>
                  cases bb <;> simp [evalBin, hva, hvb] at hinc
                | inr pb =>
                  rcases pb with ⟨nb, wb⟩
                  by_cases hw : wa = wb
                  · subst hw; by_cases hn : na = nb <;> simp [evalBin, hva, hvb, hn] at hinc
                  · refine ⟨a, b, na, nb, wa, wb, rfl, hva, hvb, hw,
                      10 + (emitNot nb wb (emitNot na wa (compLoop pre (initId, [])).2).2).2.length,
                      by omega, ?_⟩
                    simp [evalBin, hw]
        · exact absurd rfl hnot_not
      -- Track that any wire with id-value inr (_, v) (v < 10) has zero-value inl _
      have hconst_track : ∀ (v : Fin 10) (pre post : List Gate),
          C.gates = pre ++ post →
          ∀ i neg, getV (compLoop pre (initId, [])).1 i = Sum.inr (neg, v.val) →
            ∃ b, getV (compLoop pre (initZero v, [])).1 i = Sum.inl b := by
        intro v pre
        induction pre using List.reverseRecOn with
        | nil =>
          intro post _ i neg hi
          change getV initId i = Sum.inr (neg, v.val) at hi
          by_cases hilt : i < 10
          · rw [hinitId_get ⟨i, hilt⟩] at hi
            cases hi
            exact ⟨false, by dsimp only [compLoop, List.foldl_nil]; rw [hiz_get v v]; simp only [↓reduceIte]⟩
          · rw [show getV initId i = Sum.inl false from List.getD_eq_default _ _ (by rw [hinitId_len]; omega)] at hi
            cases hi
        | append_singleton pre g ih =>
          intro post hsp i neg hi
          have hsp' : C.gates = pre ++ g :: post := by simpa [List.append_assoc] using hsp
          have hpre_f : ∀ h ∈ pre, fanG h := fun h hh => hC h (hsp' ▸ List.mem_append_left _ hh)
          have hg_f : fanG g := hC g (hsp' ▸ List.mem_append_right _ List.mem_cons_self)
          obtain ⟨hwf_id, hlen_id0, _, hfg_id, _, _⟩ :=
            hcompLoop_props pre (initId, []) hpre_f hinitId_wf (fun _ h => by cases h)
          have hlen_id : (compLoop pre (initId, [])).1.length = 10 + pre.length := by
            rw [hinitId_len] at hlen_id0; exact hlen_id0
          obtain ⟨hwf_iz, hlen_iz0, _, hfg_iz, _, _⟩ :=
            hcompLoop_props pre (initZero v, []) hpre_f (hiz_wf v) (fun _ h => by cases h)
          have hlen_iz : (compLoop pre (initZero v, [])).1.length = 10 + pre.length := by
            rw [hiz_len] at hlen_iz0; exact hlen_iz0
          have hstep_id : compLoop (pre ++ [g]) (initId, []) = compStep (compLoop pre (initId, [])) g := by
            simp [compLoop, List.foldl_append]
          have hstep_iz : compLoop (pre ++ [g]) (initZero v, []) = compStep (compLoop pre (initZero v, [])) g := by
            simp [compLoop, List.foldl_append]
          rw [hstep_id] at hi
          rw [hstep_iz]
          obtain ⟨_, _, hlen_id1, hpres_id, _, _, _, _⟩ :=
            hcompStep_props g (compLoop pre (initId, [])) hg_f hwf_id hfg_id
          obtain ⟨_, _, _, hpres_iz, _, _, _, _⟩ :=
            hcompStep_props g (compLoop pre (initZero v, [])) hg_f hwf_iz hfg_iz
          by_cases hilt : i < 10 + pre.length
          · have h1' : getV (compStep (compLoop pre (initId, [])) g).1 i =
                getV (compLoop pre (initId, [])).1 i := hpres_id i (by omega)
            have h2' : getV (compStep (compLoop pre (initZero v, [])) g).1 i =
                getV (compLoop pre (initZero v, [])).1 i := hpres_iz i (by omega)
            rw [h1'] at hi; rw [h2']
            exact ih (g :: post) hsp' i neg hi
          · by_cases hieq : i = 10 + pre.length
            · subst hieq
              by_cases hbin : isBin g = true
              · obtain ⟨_, _, _, _, _, _, _, _, _, _, wNew, hw10, happ⟩ := hstep_full pre g post hsp' hbin
                rw [happ] at hi
                have hl : getV ((compLoop pre (initId, [])).1 ++ [Sum.inr (false, wNew)]) (10 + pre.length) =
                    Sum.inr (false, wNew) := by
                  dsimp only [getV]; rw [← hlen_id, List.getD_append_right _ _ _ _ le_rfl]; simp
                rw [hl] at hi
                cases hi
                have := v.isLt; omega
              · rcases g with ⟨op, ins⟩
                have hop := hg_f.1
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
                rcases hop with rfl | rfl | rfl
                · exact absurd (hisBin_and ins) hbin
                · exact absurd (hisBin_or ins) hbin
                · cases ins with
                  | nil =>
                    have hl : getV (compStep (compLoop pre (initId, [])) ⟨GateOp.not, []⟩).1 (10 + pre.length) =
                        Sum.inl true := by
                      dsimp only [compStep, getV]; rw [← hlen_id, List.getD_append_right _ _ _ _ le_rfl]; simp
                    rw [hl] at hi; cases hi
                  | cons a rest =>
                    have hl1 : getV (compStep (compLoop pre (initId, [])) ⟨GateOp.not, a :: rest⟩).1 (10 + pre.length) =
                        negVal (getV (compLoop pre (initId, [])).1 a) := by
                      dsimp only [compStep, getV]; rw [← hlen_id, List.getD_append_right _ _ _ _ le_rfl]; simp
                    have hl2 : getV (compStep (compLoop pre (initZero v, [])) ⟨GateOp.not, a :: rest⟩).1 (10 + pre.length) =
                        negVal (getV (compLoop pre (initZero v, [])).1 a) := by
                      dsimp only [compStep, getV]; rw [← hlen_iz, List.getD_append_right _ _ _ _ le_rfl]; simp
                    rw [hl1] at hi; rw [hl2]
                    cases hga : getV (compLoop pre (initId, [])).1 a with
                    | inl b => rw [hga] at hi; cases hi
                    | inr p =>
                      rcases p with ⟨n0, i0⟩
                      rw [hga] at hi; cases hi
                      obtain ⟨b, hb⟩ := ih (⟨GateOp.not, a :: rest⟩ :: post) hsp' a n0 hga
                      rw [hb]; exact ⟨!b, rfl⟩
            · rw [show getV (compStep (compLoop pre (initId, [])) g).1 i = Sum.inl false from
                List.getD_eq_default _ _ (by omega)] at hi
              cases hi
      -- First: C must have at least one binary gate (actually k = 16!)
      -- Prove k >= 16: if k <= 15, then some binary gate must read x_9 (else C doesn't depend on x_9),
      -- eliminating it gives binCount <= 14 < 15, contradicting h1.
      -- Even simpler: prove directly that for ANY v : Fin 10, if no binary gate reads v in stId, contradiction.
      -- And if k <= 15, taking v = 9 gives a binary gate reading 9, hence binCount <= k - 1 <= 14 < 15!
      have hno_var_eval : ∀ (v : Fin 10),
          (∀ pre g post, C.gates = pre ++ g :: post → isBin g = true →
            ∀ a ∈ g.inputs, ∀ neg, getV (compLoop pre (initId, [])).1 a ≠ Sum.inr (neg, v.val)) →
          (∀ neg, getV stId.1 C.output ≠ Sum.inr (neg, v.val)) →
          ∀ x y : Fin 10 → Bool, (∀ j : Fin 10, j ≠ v → x j = y j) →
            C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
        intro v hnoG hnoOut x y hxy
        have hind : ∀ (pre post : List Gate), C.gates = pre ++ post →
            ∀ i, (∀ neg, getV (compLoop pre (initId, [])).1 i ≠ Sum.inr (neg, v.val)) →
              (run pre (List.ofFn x)).getD i false = (run pre (List.ofFn y)).getD i false := by
          intro pre
          induction pre using List.reverseRecOn with
          | nil =>
            intro post _ i hi
            dsimp only [compLoop, List.foldl_nil] at hi
            dsimp only [run, List.foldl_nil]
            by_cases hilt : i < 10
            · have hne : (⟨i, hilt⟩ : Fin 10) ≠ v := by
                intro heq; apply hi false; rw [hinitId_get ⟨i, hilt⟩, heq]
              rw [List.getD_eq_getElem _ _ (by simp; exact hilt), List.getElem_ofFn,
                List.getD_eq_getElem _ _ (by simp; exact hilt), List.getElem_ofFn]
              exact hxy ⟨i, hilt⟩ hne
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          | append_singleton pre g ih =>
            intro post hsp i hi
            have hsp' : C.gates = pre ++ g :: post := by simpa [List.append_assoc] using hsp
            have hpre_f : ∀ h ∈ pre, fanG h := fun h hh => hC h (hsp' ▸ List.mem_append_left _ hh)
            have hg_f : fanG g := hC g (hsp' ▸ List.mem_append_right _ List.mem_cons_self)
            obtain ⟨hwf_p, hlen_p, _, hfg_p, _, _⟩ :=
              hcompLoop_props pre (initId, []) hpre_f hinitId_wf (fun _ h => by cases h)
            have hlen_id : (compLoop pre (initId, [])).1.length = 10 + pre.length := by
              rw [hinitId_len] at hlen_p; exact hlen_p
            have hstep_id : compLoop (pre ++ [g]) (initId, []) = compStep (compLoop pre (initId, [])) g := by
              simp [compLoop, List.foldl_append]
            rw [hstep_id] at hi
            rw [hrun_append, hrun_cons, hrun_nil, hrun_append, hrun_cons, hrun_nil]
            have hrx : (run pre (List.ofFn x)).length = 10 + pre.length := by rw [hrun_len]; simp
            have hry : (run pre (List.ofFn y)).length = 10 + pre.length := by rw [hrun_len]; simp
            by_cases hilt : i < 10 + pre.length
            · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              apply ih (g :: post) hsp' i
              intro neg
              have hpres := (hcompStep_props g (compLoop pre (initId, [])) hg_f hwf_p hfg_p).2.2.2.1 i (by omega)
              rw [← hpres]; exact hi neg
            · by_cases hieq : i = 10 + pre.length
              · subst hieq
                rw [← hrx, hstep_last, hrx, ← hry, hstep_last]
                by_cases hbin : isBin g = true
                · have hmap : g.inputs.map (fun j => (run pre (List.ofFn x)).getD j false) =
                      g.inputs.map (fun j => (run pre (List.ofFn y)).getD j false) := by
                    apply List.map_congr_left
                    intro j hj
                    exact ih (g :: post) hsp' j (hnoG pre g post hsp' hbin j hj)
                  rw [hmap]
                · rcases g with ⟨op, ins⟩
                  have hop := hg_f.1
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
                  rcases hop with rfl | rfl | rfl
                  · exact absurd (hisBin_and ins) hbin
                  · exact absurd (hisBin_or ins) hbin
                  · cases ins with
                    | nil => rfl
                    | cons a rest =>
                      rw [heval_not, heval_not]
                      simp only [List.map_cons, List.headD_cons]
                      congr 1
                      apply ih (⟨GateOp.not, a :: rest⟩ :: post) hsp' a
                      intro neg hga
                      apply hi (!neg)
                      have hl : getV (compStep (compLoop pre (initId, [])) ⟨GateOp.not, a :: rest⟩).1 (10 + pre.length) =
                          negVal (getV (compLoop pre (initId, [])).1 a) := by
                        dsimp only [compStep, getV]; rw [← hlen_id, List.getD_append_right _ _ _ _ le_rfl]; simp
                      rw [hl, hga]
              · rw [List.getD_eq_default _ _ (by dsimp only [step]; rw [List.length_append, List.length_singleton, hrx]; omega),
                  List.getD_eq_default _ _ (by dsimp only [step]; rw [List.length_append, List.length_singleton, hry]; omega)]
        exact hind C.gates [] (by simp) C.output hnoOut
      have hOut_not_var : ∀ (v : Fin 10) (neg : Bool), getV stId.1 C.output ≠ Sum.inr (neg, v.val) := by
        intro v neg heq
        obtain ⟨x, hx⟩ := hfPet_not_lit v neg
        apply hx
        have hevC := hDId_ev (List.ofFn x) (by simp)
        rw [hDId_comp x, heq] at hevC
        have hget : (run stId.2 (List.ofFn x)).getD v.val false = x v := by
          rw [hrun_getD_lt _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        dsimp only [evalVal] at hevC
        rw [hget] at hevC
        exact hevC.symm
      have hvar_read : ∀ (v : Fin 10),
          ∃ pre g post, C.gates = pre ++ g :: post ∧ isBin g = true ∧
            ∃ a ∈ g.inputs, ∃ neg, getV (compLoop pre (initId, [])).1 a = Sum.inr (neg, v.val) := by
        intro v
        by_contra hno
        have hno' : ∀ pre g post, C.gates = pre ++ g :: post → isBin g = true →
            ∀ a ∈ g.inputs, ∀ neg, getV (compLoop pre (initId, [])).1 a ≠ Sum.inr (neg, v.val) := by
          intro pre g post hsp hbin a ha neg heq
          exact hno ⟨pre, g, post, hsp, hbin, a, ha, neg, heq⟩
        obtain ⟨a, hav, hdiff⟩ := hfPet_dep v
        let x0 : Fin 10 → Bool := fun j => decide (j = a)
        let x1 : Fin 10 → Bool := fun j => decide (j = v ∨ j = a)
        have hsame := hno_var_eval v hno' (hOut_not_var v) x0 x1 (by
          intro j hjv; simp [x0, x1, hjv])
        rw [hCev x0, hCev x1] at hsame
        exact hdiff hsame
      -- Rule out k <= 15 immediately using v = 9
      have hk16_eq : k = 16 := by
        by_contra hne
        have hle15 : k ≤ 15 := by omega
        obtain ⟨pre, g, post, hsp, hbin, a, ha, neg, hga⟩ := hvar_read 9
        obtain ⟨b, hb⟩ := hconst_track 9 pre (g :: post) hsp a neg hga
        have hel := hcompLoop_elim C.gates (initZero 9) []
          (fun e g' => isBin g' = true ∧ ∃ u ∈ g'.inputs, ∃ b', getV e u = Sum.inl b')
          hC (hiz_wf 9) (fun _ h => by cases h) (fun _ _ h => h)
          ⟨pre, g, post, hsp, hbin, a, ha, b, hb⟩
        have h15 := (hiz_comp 9).2.2
        rw [hbin_nil] at hel
        omega
      -- Now k = 16: split C.gates at the FIRST binary gate g0!
      have hfirst_bin : ∃ pre g0 post, C.gates = pre ++ g0 :: post ∧
          (∀ h ∈ pre, isBin h = false) ∧ isBin g0 = true := by
        have hpos : 0 < binCount C.gates := by omega
        have hex : ∀ gs : List Gate, 0 < binCount gs →
            ∃ pre g0 post, gs = pre ++ g0 :: post ∧ (∀ h ∈ pre, isBin h = false) ∧ isBin g0 = true := by
          intro gs
          induction gs with
          | nil => intro h; rw [hbin_nil] at h; omega
          | cons g gs ih =>
            intro h
            cases hgb : isBin g with
            | true => exact ⟨[], g, gs, rfl, (fun _ h' => by cases h'), hgb⟩
            | false =>
              rw [hbin_cons, hgb, if_neg Bool.false_ne_true, Nat.add_zero] at h
              obtain ⟨pre, g0, post, rfl, hpre, hg0⟩ := ih h
              refine ⟨g :: pre, g0, post, rfl, ?_, hg0⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hgb
              · exact hpre x hx
        exact hex C.gates hpos
      obtain ⟨pre, g0, post, hsp0, hpre_not, hg0_bin⟩ := hfirst_bin
      obtain ⟨ia, ib, na, nb, wa, wb, hg0_ins, hwa_eq, hwb_eq, hwa_ne, _, _, _⟩ :=
        hstep_full pre g0 post hsp0 hg0_bin
      -- Before g0, all gates are NOT, so stP.2 = [] and every wire in stP.1 has index < 10
      have hpre_empty : (compLoop pre (initId, [])).2 = [] := by
        have hgo : ∀ gs env, (∀ h ∈ gs, fanG h) → (∀ h ∈ gs, isBin h = false) →
            (compLoop gs (env, [])).2 = [] := by
          intro gs
          induction gs with
          | nil => intro _ _ _; rfl
          | cons g gs ih =>
            intro env hgf hgn
            have hg := hgf g List.mem_cons_self
            have hgb := hgn g List.mem_cons_self
            have hst : (compStep (env, []) g).2 = [] := by
              rcases g with ⟨op, ins⟩
              have hop := hg.1
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
              rcases hop with rfl | rfl | rfl
              · cases hgb
              · cases hgb
              · rfl
            change (compLoop gs (compStep (env, []) g)).2 = []
            rw [show compStep (env, []) g = ((compStep (env, []) g).1, []) from Prod.ext rfl hst]
            exact ih _ (fun h hh => hgf h (List.mem_cons_of_mem _ hh))
              (fun h hh => hgn h (List.mem_cons_of_mem _ hh))
        exact hgo pre initId (fun h hh => hC h (hsp0 ▸ List.mem_append_left _ hh)) hpre_not
      have hwf_pre : wfEnv (compLoop pre (initId, [])).1 10 := by
        have h := (hcompLoop_props pre (initId, [])
          (fun h hh => hC h (hsp0 ▸ List.mem_append_left _ hh)) hinitId_wf (fun _ h => by cases h)).1
        simpa [hpre_empty] using h
      have hwa_lt : wa < 10 := hgetV_wf _ 10 ia na wa hwf_pre hwa_eq
      have hwb_lt : wb < 10 := hgetV_wf _ 10 ib nb wb hwf_pre hwb_eq
      let fa : Fin 10 := ⟨wa, hwa_lt⟩
      let fb : Fin 10 := ⟨wb, hwb_lt⟩
      have hfab_ne : fa ≠ fb := fun h => hwa_ne (congrArg Fin.val h)
      -- Neither fa nor fb can be read by ANY binary gate in post (else 2 binary gates drop -> 14 < 15)!
      have hpost_no_read : ∀ (v : Fin 10), (v = fa ∨ v = fb) →
          ∀ mid g1 post', post = mid ++ g1 :: post' → isBin g1 = true →
            ∀ u ∈ g1.inputs, ∀ neg,
              getV (compLoop (pre ++ g0 :: mid) (initId, [])).1 u ≠ Sum.inr (neg, v.val) := by
        intro v hv mid g1 post' hpost_sp hg1_bin u hu neg hu_eq
        have hsp2 : C.gates = pre ++ g0 :: (mid ++ g1 :: post') := by rw [hsp0, hpost_sp]
        have hc0 : isBin g0 = true ∧ ∃ w ∈ g0.inputs, ∃ b, getV (compLoop pre (initZero v, [])).1 w = Sum.inl b := by
          rcases hv with rfl | rfl
          · obtain ⟨b, hb⟩ := hconst_track fa pre (g0 :: post) hsp0 ia na hwa_eq
            exact ⟨hg0_bin, ia, by simp [hg0_ins], b, hb⟩
          · obtain ⟨b, hb⟩ := hconst_track fb pre (g0 :: post) hsp0 ib nb hwb_eq
            exact ⟨hg0_bin, ib, by simp [hg0_ins], b, hb⟩
        have hc1 : isBin g1 = true ∧ ∃ w ∈ g1.inputs, ∃ b,
            getV (compLoop (pre ++ g0 :: mid) (initZero v, [])).1 w = Sum.inl b := by
          have hsp3 : C.gates = (pre ++ g0 :: mid) ++ g1 :: post' := by simp [hsp2, List.append_assoc]
          obtain ⟨b, hb⟩ := hconst_track v (pre ++ g0 :: mid) (g1 :: post') hsp3 u neg hu_eq
          exact ⟨hg1_bin, u, hu, b, hb⟩
        have hel2 := hcompLoop_elim2 C.gates (initZero v) [] pre g0 mid g1 post' hsp2
          hC (hiz_wf v) (fun _ h => by cases h) hc0 hc1
        have h15 := (hiz_comp v).2.2
        rw [hbin_nil] at hel2
        omega
      -- Value of g0 depends ONLY on (x fa, x fb)
      have hpre_val : ∀ (x : Fin 10 → Bool) (i : ℕ), i < (compLoop pre (initId, [])).1.length →
          (run pre (List.ofFn x)).getD i false = evalVal (List.ofFn x) (getV (compLoop pre (initId, [])).1 i) := by
        intro x i hi
        have h := (hcompLoop_props pre (initId, [])
          (fun h hh => hC h (hsp0 ▸ List.mem_append_left _ hh)) hinitId_wf (fun _ h => by cases h)).2.2.2.2.2
          (List.ofFn x) (List.ofFn x) (by simp) (by simp [hinitId_len]) (hinitId_eval x) i hi
        simpa [hpre_empty, run] using h.symm
      have hg0_val : ∀ (x : Fin 10 → Bool),
          (run (pre ++ [g0]) (List.ofFn x)).getD (10 + pre.length) false =
          g0.op.eval [if na then !(x fa) else x fa, if nb then !(x fb) else x fb] := by
        intro x
        rw [hrun_append, hrun_cons, hrun_nil]
        have hlen : (run pre (List.ofFn x)).length = 10 + pre.length := by rw [hrun_len]; simp
        rw [← hlen, hstep_last, hg0_ins]
        simp only [List.map_cons, List.map_nil]
        have hplen : (compLoop pre (initId, [])).1.length = 10 + pre.length := by
          have h := (hcompLoop_props pre (initId, [])
            (fun h hh => hC h (hsp0 ▸ List.mem_append_left _ hh)) hinitId_wf (fun _ h => by cases h)).2.1
          rw [hinitId_len] at h; exact h
        have hia_lt : ia < 10 + pre.length := by
          by_contra hge
          rw [show getV (compLoop pre (initId, [])).1 ia = Sum.inl false from
            List.getD_eq_default _ _ (by omega)] at hwa_eq
          cases hwa_eq
        have hib_lt : ib < 10 + pre.length := by
          by_contra hge
          rw [show getV (compLoop pre (initId, [])).1 ib = Sum.inl false from
            List.getD_eq_default _ _ (by omega)] at hwb_eq
          cases hwb_eq
        rw [hpre_val x ia (by omega), hwa_eq, hpre_val x ib (by omega), hwb_eq]
        have hfa : (List.ofFn x).getD wa false = x fa := by
          rw [List.getD_eq_getElem _ _ (by simp; exact hwa_lt), List.getElem_ofFn]
        have hfb : (List.ofFn x).getD wb false = x fb := by
          rw [List.getD_eq_getElem _ _ (by simp; exact hwb_lt), List.getElem_ofFn]
        dsimp only [evalVal]
        rw [hfa, hfb]
      let g0Fn : Bool → Bool → Bool := fun p q =>
        g0.op.eval [if na then !p else p, if nb then !q else q]
      -- If x and y agree outside {fa, fb} and give the same g0Fn value, then C.eval x = C.eval y!
      have hfactor : ∀ (x y : Fin 10 → Bool),
          (∀ j : Fin 10, j ≠ fa → j ≠ fb → x j = y j) →
          g0Fn (x fa) (x fb) = g0Fn (y fa) (y fb) →
          C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
        intro x y hxy hg0eq
        have hind : ∀ (mid post' : List Gate), post = mid ++ post' →
            ∀ i, (∀ neg, getV (compLoop (pre ++ g0 :: mid) (initId, [])).1 i ≠ Sum.inr (neg, fa.val)) →
                 (∀ neg, getV (compLoop (pre ++ g0 :: mid) (initId, [])).1 i ≠ Sum.inr (neg, fb.val)) →
              (run (pre ++ g0 :: mid) (List.ofFn x)).getD i false =
              (run (pre ++ g0 :: mid) (List.ofFn y)).getD i false := by
          intro mid
          induction mid using List.reverseRecOn with
          | nil =>
            intro post' _ i hna hnb
            have hst_eq : compLoop (pre ++ [g0]) (initId, []) = compStep (compLoop pre (initId, [])) g0 := by
              simp [compLoop, List.foldl_append]
            have hpre_f : ∀ h ∈ pre, fanG h := fun h hh => hC h (hsp0 ▸ List.mem_append_left _ hh)
            have hg0_f : fanG g0 := hC g0 (hsp0 ▸ List.mem_append_right _ List.mem_cons_self)
            obtain ⟨hwf_p, hlen_p, _, hfg_p, _, _⟩ :=
              hcompLoop_props pre (initId, []) hpre_f hinitId_wf (fun _ h => by cases h)
            have hplen : (compLoop pre (initId, [])).1.length = 10 + pre.length := by
              rw [hinitId_len] at hlen_p; exact hlen_p
            by_cases hilt : i < 10 + pre.length
            · have hpres_id := (hcompStep_props g0 (compLoop pre (initId, [])) hg0_f hwf_p hfg_p).2.2.2.1 i (by omega)
              rw [hst_eq] at hna hnb
              rw [hpres_id] at hna hnb
              rw [hrun_append, hrun_cons, hrun_nil, hrun_append, hrun_cons, hrun_nil]
              have hrx : (run pre (List.ofFn x)).length = 10 + pre.length := by rw [hrun_len]; simp
              have hry : (run pre (List.ofFn y)).length = 10 + pre.length := by rw [hrun_len]; simp
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              rw [hpre_val x i (by omega), hpre_val y i (by omega)]
              cases hvi : getV (compLoop pre (initId, [])).1 i with
              | inl b => rfl
              | inr p =>
                rcases p with ⟨neg, idx⟩
                have hlt10 : idx < 10 := hgetV_wf _ 10 i neg idx hwf_pre hvi
                have hne1 : (⟨idx, hlt10⟩ : Fin 10) ≠ fa := fun h => hna neg (by rw [hvi, ← h])
                have hne2 : (⟨idx, hlt10⟩ : Fin 10) ≠ fb := fun h => hnb neg (by rw [hvi, ← h])
                have hgx : (List.ofFn x).getD idx false = x ⟨idx, hlt10⟩ := by
                  rw [List.getD_eq_getElem _ _ (by simp; exact hlt10), List.getElem_ofFn]
                have hgy : (List.ofFn y).getD idx false = y ⟨idx, hlt10⟩ := by
                  rw [List.getD_eq_getElem _ _ (by simp; exact hlt10), List.getElem_ofFn]
                dsimp only [evalVal]
                rw [hgx, hgy, hxy ⟨idx, hlt10⟩ hne1 hne2]
            · by_cases hieq : i = 10 + pre.length
              · subst hieq
                rw [hg0_val x, hg0_val y]
                exact hg0eq
              · rw [List.getD_eq_default _ _ (by rw [hrun_len]; simp; omega),
                  List.getD_eq_default _ _ (by rw [hrun_len]; simp; omega)]
          | append_singleton mid g1 ih =>
            intro post' hpm i hna hnb
            have hpm' : post = mid ++ g1 :: post' := by simpa [List.append_assoc] using hpm
            have hbase_sp : pre ++ g0 :: (mid ++ [g1]) = (pre ++ g0 :: mid) ++ [g1] := by simp [List.append_assoc]
            have hsp_all : C.gates = (pre ++ g0 :: mid) ++ g1 :: post' := by
              rw [hsp0, hpm']; simp [List.append_assoc]
            have hprev_f : ∀ h ∈ pre ++ g0 :: mid, fanG h :=
              fun h hh => hC h (hsp_all ▸ List.mem_append_left _ hh)
            have hg1_f : fanG g1 := hC g1 (hsp_all ▸ List.mem_append_right _ List.mem_cons_self)
            obtain ⟨hwf_p, hlen_p, _, hfg_p, _, _⟩ :=
              hcompLoop_props (pre ++ g0 :: mid) (initId, []) hprev_f hinitId_wf (fun _ h => by cases h)
            have hplen : (compLoop (pre ++ g0 :: mid) (initId, [])).1.length = 10 + (pre ++ g0 :: mid).length := by
              rw [hinitId_len] at hlen_p; exact hlen_p
            rw [hbase_sp] at hna hnb ⊢
            have hstep_id : compLoop ((pre ++ g0 :: mid) ++ [g1]) (initId, []) =
                compStep (compLoop (pre ++ g0 :: mid) (initId, [])) g1 := by
              simp [compLoop, List.foldl_append]
            rw [hstep_id] at hna hnb
            rw [hrun_append (pre ++ g0 :: mid) [g1], hrun_cons, hrun_nil,
              hrun_append (pre ++ g0 :: mid) [g1], hrun_cons, hrun_nil]
            have hrx : (run (pre ++ g0 :: mid) (List.ofFn x)).length = 10 + (pre ++ g0 :: mid).length := by
              rw [hrun_len]; simp
            have hry : (run (pre ++ g0 :: mid) (List.ofFn y)).length = 10 + (pre ++ g0 :: mid).length := by
              rw [hrun_len]; simp
            by_cases hilt : i < 10 + (pre ++ g0 :: mid).length
            · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              have hpres := (hcompStep_props g1 (compLoop (pre ++ g0 :: mid) (initId, [])) hg1_f hwf_p hfg_p).2.2.2.1 i (by omega)
              rw [hpres] at hna hnb
              exact ih (g1 :: post') hpm' i hna hnb
            · by_cases hieq : i = 10 + (pre ++ g0 :: mid).length
              · subst hieq
                rw [← hrx, hstep_last, hrx, ← hry, hstep_last]
                by_cases hbin : isBin g1 = true
                · have hmap : g1.inputs.map (fun j => (run (pre ++ g0 :: mid) (List.ofFn x)).getD j false) =
                      g1.inputs.map (fun j => (run (pre ++ g0 :: mid) (List.ofFn y)).getD j false) := by
                    apply List.map_congr_left
                    intro j hj
                    exact ih (g1 :: post') hpm' j
                      (hpost_no_read fa (Or.inl rfl) mid g1 post' hpm' hbin j hj)
                      (hpost_no_read fb (Or.inr rfl) mid g1 post' hpm' hbin j hj)
                  rw [hmap]
                · rcases g1 with ⟨op, ins⟩
                  have hop := hg1_f.1
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
                  rcases hop with rfl | rfl | rfl
                  · exact absurd (hisBin_and ins) hbin
                  · exact absurd (hisBin_or ins) hbin
                  · cases ins with
                    | nil => rfl
                    | cons u rest =>
                      rw [heval_not, heval_not]
                      simp only [List.map_cons, List.headD_cons]
                      congr 1
                      apply ih (⟨GateOp.not, u :: rest⟩ :: post') hpm' u
                      · intro neg hu
                        apply hna (!neg)
                        have hl : getV (compStep (compLoop (pre ++ g0 :: mid) (initId, [])) ⟨GateOp.not, u :: rest⟩).1
                            (10 + (pre ++ g0 :: mid).length) =
                            negVal (getV (compLoop (pre ++ g0 :: mid) (initId, [])).1 u) := by
                          dsimp only [compStep, getV]; rw [← hplen, List.getD_append_right _ _ _ _ le_rfl]; simp
                        rw [hl, hu]
                      · intro neg hu
                        apply hnb (!neg)
                        have hl : getV (compStep (compLoop (pre ++ g0 :: mid) (initId, [])) ⟨GateOp.not, u :: rest⟩).1
                            (10 + (pre ++ g0 :: mid).length) =
                            negVal (getV (compLoop (pre ++ g0 :: mid) (initId, [])).1 u) := by
                          dsimp only [compStep, getV]; rw [← hplen, List.getD_append_right _ _ _ _ le_rfl]; simp
                        rw [hl, hu]
              · rw [List.getD_eq_default _ _ (by dsimp only [step]; rw [List.length_append, List.length_singleton, hrx]; omega),
                  List.getD_eq_default _ _ (by dsimp only [step]; rw [List.length_append, List.length_singleton, hry]; omega)]
        have hfull := hind post [] (by simp) C.output
        have hst_eq : compLoop (pre ++ g0 :: post) (initId, []) = stId := by rw [← hsp0]
        rw [hst_eq] at hfull
        change (run C.gates (List.ofFn x)).getD C.output false = (run C.gates (List.ofFn y)).getD C.output false
        rw [hsp0]
        exact hfull (hOut_not_var fa) (hOut_not_var fb)
      -- Pigeonhole on the 4 Boolean pairs (p, q) mapped to Bool by g0Fn!
      have hpigeon : ∃ p1 q1 p2 q2 : Bool, (p1, q1) ≠ (p2, q2) ∧ g0Fn p1 q1 = g0Fn p2 q2 := by
        cases h00 : g0Fn false false <;> cases h01 : g0Fn false true <;> cases h10 : g0Fn true false
        · exact ⟨false, false, false, true, by decide, by rw [h00, h01]⟩
        · exact ⟨false, false, false, true, by decide, by rw [h00, h01]⟩
        · exact ⟨false, false, true, false, by decide, by rw [h00, h10]⟩
        · exact ⟨false, true, true, false, by decide, by rw [h01, h10]⟩
        · exact ⟨false, true, true, false, by decide, by rw [h01, h10]⟩
        · exact ⟨false, false, true, false, by decide, by rw [h00, h10]⟩
        · exact ⟨false, false, false, true, by decide, by rw [h00, h01]⟩
        · exact ⟨false, false, false, true, by decide, by rw [h00, h01]⟩
      obtain ⟨p1, q1, p2, q2, hpq_ne, hg0_eq⟩ := hpigeon
      obtain ⟨c, hc⟩ := hfPet_four fa fb hfab_ne p1 q1 p2 q2 hpq_ne
      cases c with
      | none =>
        let x1 : Fin 10 → Bool := fun j => if j = fa then p1 else if j = fb then q1 else false
        let x2 : Fin 10 → Bool := fun j => if j = fa then p2 else if j = fb then q2 else false
        have hsame := hfactor x1 x2
          (fun j hja hjb => by simp [x1, x2, hja, hjb])
          (by simp [x1, x2, hfab_ne.symm, hg0_eq])
        rw [hCev x1, hCev x2] at hsame
        exact hc hsame
      | some u =>
        let x1 : Fin 10 → Bool := fun j => if j = fa then p1 else if j = fb then q1 else decide (j = u)
        let x2 : Fin 10 → Bool := fun j => if j = fa then p2 else if j = fb then q2 else decide (j = u)
        have hsame := hfactor x1 x2
          (fun j hja hjb => by simp [x1, x2, hja, hjb])
          (by simp [x1, x2, hfab_ne.symm, hg0_eq])
        rw [hCev x1, hCev x2] at hsame
        exact hc hsame
  -- Combine A, [NOT(A.output)], B into a single FanInTwo circuit C
  let gNot : Gate := ⟨GateOp.not, [A.output]⟩
  let C : Circuit := ⟨A.gates ++ gNot :: B.gates, B.output⟩
  have hC_fan : FanInTwo C := by
    intro g hg
    change g ∈ A.gates ++ gNot :: B.gates at hg
    rw [List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact hA g hg
    · exact ⟨by simp [gNot], by simp [gNot]⟩
    · obtain ⟨ho, hl⟩ := hB g hg
      refine ⟨?_, hl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
      rcases ho with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hC_size : C.size = A.size + B.size + 1 := by
    change (A.gates ++ gNot :: B.gates).length = A.gates.length + B.gates.length + 1
    simp; omega
  have hB_not0 : notCount B = 0 := by
    change (B.gates.filter _).length = 0
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg
    have ho := (hB g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with h | h <;> rw [h] <;> decide
  have hC_not : notCount C = notCount A + 1 := by
    change ((A.gates ++ gNot :: B.gates).filter _).length = (A.gates.filter _).length + 1
    rw [List.filter_append, List.length_append, List.filter_cons]
    have hgN : @decide (gNot.op = GateOp.not) (lineDegreeGateOpDecEq gNot.op GateOp.not) = true := rfl
    rw [hgN]
    simp only [ite_true, List.length_cons]
    have hB0 : (B.gates.filter (fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not))).length = 0 := hB_not0
    omega
  have hC_eval : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = fPet x := by
    intro x
    have hw : C.wires (List.ofFn x) = B.wires (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)]) := by
      change run (A.gates ++ gNot :: B.gates) (List.ofFn x) = run B.gates (run A.gates (List.ofFn x) ++ [!A.eval (List.ofFn x)])
      rw [hrun_append, hrun_cons]
      rfl
    change (C.wires (List.ofFn x)).getD B.output false = fPet x
    rw [hw]
    exact hcompF x
  have hC_bin17 : 17 ≤ binCount C.gates := by
    by_contra hlt
    exact h17 (binCount C.gates) (by omega) C hC_fan rfl hC_eval
  have hC_sum := hbin_add_not C hC_fan
  -- Now 17 + (notCount A + 1) <= A.size + B.size + 1 <= 19, so notCount A <= 1 and 17 <= A.size + B.size!
  have hnotA_le : notCount A ≤ 1 := by omega
  have hsz_ge : 17 ≤ A.size + B.size := by omega
  by_cases hnotA0 : notCount A = 0
  · have hA_mono : Monotone2 A := by
      intro g hg
      obtain ⟨ho, hl⟩ := hA g hg
      refine ⟨?_, hl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
      rcases ho with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have hmem : g ∈ A.gates.filter (fun g' => @decide (g'.op = GateOp.not) (lineDegreeGateOpDecEq g'.op GateOp.not)) := by
          rw [List.mem_filter]; exact ⟨hg, by rw [h]; rfl⟩
        have hnil : A.gates.filter (fun g' => @decide (g'.op = GateOp.not) (lineDegreeGateOpDecEq g'.op GateOp.not)) = [] :=
          List.length_eq_zero_iff.mp hnotA0
        rw [hnil] at hmem; cases hmem
    exact h2 A B hA_mono hB hsz_ge hsz hcompF
  · have hnotA1 : notCount A = 1 := by omega
    have hsz18 : A.size + B.size = 18 := by omega
    exact h3 A B hA hB hnotA1 hsz18 hcompF
