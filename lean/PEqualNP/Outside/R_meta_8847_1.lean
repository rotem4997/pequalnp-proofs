import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open PEqualNP.GenericRejection PEqualNP.HeptadCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8847_1
    (fewAnd : let S := singerLines3
      let T (b : Bool) (x : List Bool) : Prop := if b then
        ∃ p l, p ∈ S l ∧ x = incidenceInput {p} {l}
      else ∃ P, let W := missLines S P
                (∀ p ∉ P, ∃ l ∈ W, p ∈ S l) ∧
                (¬InNoLine S P ∨ ¬InNoPencil S W) ∧ x = incidenceInput P W
      ∀ C : Circuit, Monotone2 C →
      C.gates.countP (fun g => (g.op.eval [])) ≤ 13 →
      1 < min (C.lineDeg 26 (Finset.Ico 13 26)) (C.lineDeg 26 (Finset.range 13)) →
      (∀ b x, T b x → C.eval x = b) →
      (∀ m p g, C.gates[m]? = some g → p ∈ g.inputs → p < 26+m →
        let b := (!g.op.eval [])
        ∃ x, T b x ∧
          let a := (⟨C.gates.take m,0⟩ : Circuit).wires x
          let d := (⟨C.gates.drop (m+1),C.output⟩ : Circuit)
          a.getD p false = !b ∧ d.eval (a ++ [!b]) ≠ b) →
      64 ≤ C.size)
    (fewOr : let S := singerLines3
      let T (b : Bool) (x : List Bool) : Prop := if b then
        ∃ p l, p ∈ S l ∧ x = incidenceInput {p} {l}
      else ∃ P, let W := missLines S P
                (∀ p ∉ P, ∃ l ∈ W, p ∈ S l) ∧
                (¬InNoLine S P ∨ ¬InNoPencil S W) ∧ x = incidenceInput P W
      ∀ C : Circuit, Monotone2 C →
      C.gates.countP (fun g => (!g.op.eval [])) ≤ 49 →
      1 < min (C.lineDeg 26 (Finset.Ico 13 26)) (C.lineDeg 26 (Finset.range 13)) →
      (∀ b x, T b x → C.eval x = b) →
      (∀ m p g, C.gates[m]? = some g → p ∈ g.inputs → p < 26+m →
        let b := (!g.op.eval [])
        ∃ x, T b x ∧
          let a := (⟨C.gates.take m,0⟩ : Circuit).wires x
          let d := (⟨C.gates.drop (m+1),C.output⟩ : Circuit)
          a.getD p false = !b ∧ d.eval (a ++ [!b]) ≠ b) →
      64 ≤ C.size)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x6 : Finset (Fin (13 : ℕ))), (∀ x7 ∉ x6, ∃ (x9 : Fin (13 : ℕ)), x3 x6 x9 ∧ x2 x7 x9) → ((∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x6, x2 x9 x8) ∨ ∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), x3 x6 x9 → x2 x8 x9) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 fun (x9 : Fin (26 : ℕ)) => Decidable.decide ((∃ x10 ∈ x6, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x9 = Fin.natAdd (13 : ℕ) x10 ∧ x3 x6 x10)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x6 →     x6.size ≤ (63 : ℕ) →       x4 x6 →         x5 x6 →           (1 : ℕ) < Min.min (x6.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))) (x6.lineDeg (26 : ℕ) (Finset.range (13 : ℕ))) →             ∃ (x12 : ℕ) (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate),               x6.gates[x12]? = Option.some x14 ∧                 x13 ∈ x14.inputs ∧                   x13 < (26 : ℕ) + x12 ∧                     have x15 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x6 x12 x13;                     x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x5 x15 ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x4 x15 := by
  let run (gs : List Gate) (xs : List Bool) := gs.foldl (fun vs g =>
    vs ++ [g.op.eval (g.inputs.map fun i => vs.getD i false)]) xs

  have len (gs : List Gate) (xs : List Bool) : (run gs xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp [run]
    | cons g gs ih => change (run gs _).length = _; rw [ih]; simp; omega

  have renEq (n m p i : Nat) : eraseRedirect n m p i =
      (if i = n+m then p else if n+m < i then i-1 else i) := rfl
  have align (n m p : Nat) (a b : List Bool) (hp : p < a.length) (hl : a.length = n + m) (i : Nat) :
      (a ++ b).getD (eraseRedirect n m p i) false =
        (a ++ (a.getD p false :: b)).getD i false := by
    simp only [List.getD_eq_getElem?_getD]
    rcases lt_trichotomy i a.length with hi | hi | hi
    · simp [renEq, ← hl, ne_of_lt hi, not_lt_of_ge hi.le, List.getElem?_append_left hi]
    · subst i
      simp [renEq, ← hl, List.getElem?_append_left hp]
    · have h : a.length ≤ i-1 := by omega
      have he : i-a.length = (i-1-a.length)+1 := by omega
      simp [renEq, ← hl, ne_of_gt hi, hi, List.getElem?_append_right h, List.getElem?_append_right hi.le, he]

  have suffix (n m p : Nat) (a : List Bool) (hp : p < a.length) (hl : a.length = n+m)
      (gs : List Gate) (b : List Bool) (i : Nat) :
      (run (gs.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) (a++b)).getD (eraseRedirect n m p i) false =
        (run gs (a++(a.getD p false :: b))).getD i false := by
    induction gs generalizing b with
    | nil => exact align n m p a b hp hl i
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun t => (a ++ (a.getD p false :: b)).getD t false)
      have hv : g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun t => (a ++ b).getD t false) = v := by
        unfold v
        congr 1
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro t _
        exact align n m p a b hp hl t
      change (run _ ((a++b)++[_])).getD _ false = (run gs ((a++_)++[v])).getD i false
      rw [hv]
      simpa only [List.append_assoc, List.cons_append] using ih (b++[v])

  intro D I misses pos neg C hm hs hpos hneg hd
  classical
  let S := singerLines3
  let T (b : Bool) (x : List Bool) : Prop := if b then
        ∃ p l, p ∈ S l ∧ x = incidenceInput {p} {l}
      else ∃ P, let W := missLines S P
                (∀ p ∉ P, ∃ l ∈ W, p ∈ S l) ∧
                (¬InNoLine S P ∨ ¬InNoPencil S W) ∧ x = incidenceInput P W
  have inc : ∀ p l, p ∈ S l ↔ I p l := by decide
  have avoid (P : Finset (Fin 13)) (l : Fin 13) : l ∈ missLines S P ↔ misses P l := by
    change l ∈ Finset.univ.filter (fun k => Disjoint (S k) P) ↔ ∀ p ∈ P, ¬I p l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right,inc]
  have inputEq (P W : Finset (Fin 13)) : incidenceInput P W =
      List.ofFn (fun p : Fin 13 => decide (p ∈ P)) ++ List.ofFn (fun l : Fin 13 => decide (l ∈ W)) := rfl
  have funEq (A : Circuit) (x : Fin 26 → Bool) : circuitFun 26 A x = A.eval (List.ofFn x) := rfl
  have andEq (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEq (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have img (P W : Finset (Fin 13)) : incidenceInput P W = List.ofFn (fun i : Fin (13+13) =>
      decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ W, i = Fin.natAdd 13 l)) := by
    rw [List.ofFn_add]
    rw [inputEq]
    have lr : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide
    have rl : ∀ l p : Fin 13, Fin.natAdd 13 l ≠ Fin.castAdd 13 p := fun l p => (lr p l).symm
    have inj : ∀ k l : Fin 13, Fin.natAdd 13 k = Fin.natAdd 13 l ↔ k=l := by decide
    congr 1 <;> apply congrArg List.ofFn <;> funext i <;> apply decide_eq_decide.mpr
    · change i ∈ P ↔ (∃ p ∈ P, Fin.castAdd 13 i = Fin.castAdd 13 p) ∨ ∃ l ∈ W, Fin.castAdd 13 i = Fin.natAdd 13 l
      simp only [lr,Fin.castAdd_inj]; simp
    · change i ∈ W ↔ (∃ p ∈ P, Fin.natAdd 13 i = Fin.castAdd 13 p) ∨ ∃ l ∈ W, Fin.natAdd 13 i = Fin.natAdd 13 l
      simp only [rl,inj]; simp
  have pconv (A : Circuit) : pos A ↔ ∀ x, T true x → A.eval x = true := by
    constructor
    · intro h x hx
      obtain ⟨p,l,hi,hx⟩ := hx
      subst x
      rw [img]
      simpa only [funEq,Finset.mem_singleton,exists_eq_left] using h p l ((inc p l).mp hi)
    · intro h p l hi
      have he := h _ ⟨p,l,(inc p l).mpr hi,rfl⟩
      rw [img] at he
      simpa only [funEq,Finset.mem_singleton,exists_eq_left] using he
  have side (P : Finset (Fin 13)) (i : Fin 26) :
      (∃ l ∈ missLines S P, i = Fin.natAdd 13 l) ↔ ∃ l, i = Fin.natAdd 13 l ∧ misses P l := by
    simp only [avoid]
    exact exists_congr fun l => and_comm
  have nconv (A : Circuit) : neg A ↔ ∀ x, T false x → A.eval x = false := by
    have nc (P : Finset (Fin 13)) : (¬InNoLine S P ∨ ¬InNoPencil S (missLines S P)) ↔
        (∃ l, ∀ p ∈ P, I p l) ∨ ∃ p, ∀ l, misses P l → I p l := by
      unfold InNoLine InNoPencil
      push Not
      change ((∃ l, ∀ p ∈ P, p ∈ S l) ∨ ∃ p, ∀ l ∈ missLines S P, p ∈ S l) ↔ _
      simp only [inc, avoid]
    constructor
    · intro h x hx
      obtain ⟨P,hclosed,hdeg,hx⟩ := hx
      subst x
      have c := h P (by simpa only [← inc, ← avoid] using hclosed) ((nc P).mp hdeg)
      rw [img]
      change A.eval (List.ofFn _) = false at c
      simpa only [side] using c
    · intro h P hclosed hdeg
      have he := h _ ⟨P,(by simpa only [inc,avoid] using hclosed),(nc P).mpr hdeg,rfl⟩
      rw [img] at he
      change A.eval (List.ofFn _) = false
      simpa only [side] using he
  have correct : ∀ b x, T b x → C.eval x = b := by
    intro b; cases b
    · exact (nconv C).mp hneg
    · exact (pconv C).mp hpos
  have tlen (b : Bool) (x : List Bool) (h : T b x) : x.length = 26 := by
    cases b
    · obtain ⟨P,_,_,rfl⟩ := h; simp [inputEq]
    · obtain ⟨p,l,_,rfl⟩ := h; simp [inputEq]
  by_contra noErase
  have blockers : ∀ m p g, C.gates[m]? = some g → p ∈ g.inputs → p < 26+m →
        let b := (!g.op.eval [])
        ∃ x, T b x ∧
          let a := (⟨C.gates.take m,0⟩ : Circuit).wires x
          let d := (⟨C.gates.drop (m+1),C.output⟩ : Circuit)
          a.getD p false = !b ∧ d.eval (a ++ [!b]) ≠ b := by
    intro m p g hg hpin hp b
    let E := eraseGate 26 C m p
    have hm' := (List.getElem?_eq_some_iff.mp hg).1
    have hgval := (List.getElem?_eq_some_iff.mp hg).2
    have hop := (hm g (List.mem_of_getElem? hg)).1
    change g.op = .and ∨ g.op = .or at hop
    have fail : ¬∀ x, T b x → E.eval x = b := by
      intro hall
      apply noErase
      refine ⟨m,p,g,hg,hpin,hp,?_⟩
      rcases hop with h|h
      · exact Or.inl ⟨h,(nconv E).mpr (by simpa [b,h,andEq,orEq] using hall)⟩
      · exact Or.inr ⟨h,(pconv E).mpr (by simpa [b,h,andEq,orEq] using hall)⟩
    push Not at fail
    obtain ⟨x,hx,hbad⟩ := fail
    refine ⟨x,hx,?_⟩
    let a := run (C.gates.take m) x
    let d : Circuit := ⟨C.gates.drop (m+1),C.output⟩
    have ha : a.length = 26+m := by simp [a,len,tlen b x hx,Nat.min_eq_left hm'.le]
    have eh : E.eval x = d.eval (a++[a.getD p false]) := by
      have H := suffix 26 m p a (by omega) ha (C.gates.drop (m+1)) [] C.output
      simp only [List.append_nil] at H
      have repl : E = ⟨C.gates.take m ++ (C.gates.drop (m+1)).map (fun g => ⟨g.op,g.inputs.map (eraseRedirect 26 m p)⟩), eraseRedirect 26 m p C.output⟩ := by
        change (if m < C.gates.length then _ else _) = _
        rw [if_pos hm']
      rw [repl]
      change (run (C.gates.take m ++ _) x).getD _ false = (run _ (a++[a.getD p false])).getD _ false
      simpa [run,List.foldl_append,a] using H
    have orig : C.eval x = d.eval (a++[g.op.eval (g.inputs.map fun t => a.getD t false)]) := by
      have decomp : C.gates = C.gates.take m ++ g :: C.gates.drop (m+1) := by
        rw [←hgval,← List.drop_eq_getElem_cons hm', List.take_append_drop]
      change (run C.gates x).getD C.output false = _
      conv_lhs => rw [decomp]
      simp only [run, List.foldl_append, List.foldl_cons]
      rfl
    have neq : a.getD p false ≠ b := by
      intro heq
      have heval : g.op.eval (g.inputs.map fun t => a.getD t false) = b := by
        rcases hop with h|h
        · have hb : b = false := by simp [b,h,andEq,orEq]
          rw [h,hb]; simp only [andEq,List.all_eq_false]; exact ⟨false,List.mem_map.mpr ⟨p,hpin,heq.trans hb⟩,by decide⟩
        · have hb : b = true := by simp [b,h,andEq,orEq]
          rw [h,hb]; simp only [orEq,List.any_eq_true]; exact ⟨true,List.mem_map.mpr ⟨p,hpin,heq.trans hb⟩,rfl⟩
      apply hbad
      simpa only [orig,heval,eh,heq] using correct b x hx
    have hpinv : a.getD p false = !b := by revert neq; cases b <;> cases a.getD p false <;> decide
    change a.getD p false = !b ∧ d.eval (a++[!b]) ≠ b
    rw [eh,hpinv] at hbad
    exact ⟨hpinv,hbad⟩
  by_cases small : C.gates.countP (fun g => (g.op.eval [])) ≤ 13
  · have h := fewAnd C hm small hd correct blockers
    omega
  · have count (gs : List Gate) : gs.countP (fun g => (!g.op.eval [])) +
          gs.countP (fun g => (g.op.eval [])) ≤ gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih => cases h : g.op.eval [] <;> simp [List.countP_cons,h] <;> omega
    have bound := count C.gates
    change C.gates.length ≤ 63 at hs
    have h := fewOr C hm (by omega) hd correct blockers
    change 64 ≤ C.gates.length at h
    omega
