import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5792_517
    (hSigned : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 10 → Bool, (if b = true then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) →
      17 ≤ C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op))
    (hMono : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) = 0 →
      C.size ≤ 18 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hOneNotEarly : ∀ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (a out : ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨pre, 0⟩ →
      PEqualNP.MetaComplexity.FanInTwo ⟨post, 0⟩ →
      pre.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) = 0 →
      post.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) = 0 →
      pre.length ≤ 3 →
      pre.length + post.length = 17 →
      a < 10 + pre.length →
      out < 28 →
      ∃ x : Fin 10 → Bool,
        (⟨pre ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩ :: post, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
           x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hOneNotLate : ∀ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (a out : ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨pre, 0⟩ →
      PEqualNP.MetaComplexity.FanInTwo ⟨post, 0⟩ →
      pre.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) = 0 →
      post.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) = 0 →
      4 ≤ pre.length →
      pre.length + post.length = 17 →
      a < 10 + pre.length →
      out < 28 →
      ∃ x : Fin 10 → Bool,
        (⟨pre ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩ :: post, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
           x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         x2.size = (17 : ℕ) →           have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));           have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;           ∃ (x11 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x10 x11 x3 else x10 x11 x3) ≠ x9 x11 := by
  intro x1 x2 x3 x4 h1 h2 _hsz hsz17
  dsimp only
  let P : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let isNot : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op
  let isBin : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨x1 :: x2.gates, x3⟩
  have hC : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h1 _ (List.mem_cons_self ..)
    · exact h2 _ hg
  have hClen : C.gates.length = 18 := by
    change x2.gates.length = 17 at hsz17
    change (x1 :: x2.gates).length = 18
    simp only [List.length_cons]
    omega
  by_contra hNo
  have hCeval : ∀ x : Fin 10 → Bool, (if x4 = true then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) = P x := by
    intro x
    by_contra hne
    exact hNo ⟨x, hne⟩
  have hCountSum : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      gs.countP isBin + gs.countP isNot = gs.length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      rcases g with ⟨op, ins⟩
      cases op <;> (simp only [List.countP_cons, List.length_cons]; dsimp only [isBin, isNot] at ih ⊢; simp only [ite_true, Bool.false_eq_true, ite_false]; omega)
  have hBin17 : 17 ≤ C.gates.countP isBin := hSigned C x4 hC hCeval
  have hNotLe1 : C.gates.countP isNot ≤ 1 := by
    have hs := hCountSum C.gates
    omega
  have andEval (xs : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := rfl
  have notEval (xs : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.not.eval xs = !(xs.headD false) := rfl
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hWiresDef (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) :
      (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l = gs.foldl step l := rfl
  have hWiresAppend (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) :
      (⟨gs1 ++ gs2, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l =
      (⟨gs2, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
        ((⟨gs1, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l) := by
    change (gs1 ++ gs2).foldl step l = gs2.foldl step (gs1.foldl step l)
    exact List.foldl_append
  have hWiresCons (g : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) :
      (⟨g :: gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l =
      (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (step l g) := rfl
  have hWiresLen (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      ∀ l : List Bool, ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l).length = l.length + gs.length := by
    induction gs with
    | nil => intro l; simp [hWiresDef]
    | cons g gs ih =>
      intro l
      rw [hWiresCons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  let wle : List Bool → List Bool → Prop := fun l1 l2 =>
    l1.length = l2.length ∧ ∀ i, l1.getD i false = true → l2.getD i false = true
  have hWleApp (l1 l2 : List Bool) (b1 b2 : Bool) (hle : wle l1 l2) (hb : b1 = true → b2 = true) :
      wle (l1 ++ [b1]) (l2 ++ [b2]) := by
    refine ⟨by simp [hle.1], ?_⟩
    intro i hi
    by_cases hlt : i < l1.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (hle.1 ▸ hlt)]
      exact hle.2 i hi
    · by_cases heq : i = l1.length
      · subst heq
        rw [List.getD_append_right _ _ _ _ le_rfl] at hi
        rw [List.getD_append_right _ _ _ _ (by omega : l2.length ≤ l1.length)]
        have hsub1 : l1.length - l1.length = 0 := Nat.sub_self _
        have hsub2 : l1.length - l2.length = 0 := by omega
        rw [hsub1] at hi
        rw [hsub2]
        exact hb hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        contradiction
  have hMonoStep (g : PEqualNP.CircuitLowerBounds.Gate)
      (hg : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (l1 l2 : List Bool) (hle : wle l1 l2) :
      wle (step l1 g) (step l2 g) := by
    apply hWleApp l1 l2 _ _ hle
    intro hv
    rcases hg with hop | hop
    · rw [hop, andEval] at hv ⊢
      rw [List.all_eq_true] at hv ⊢
      intro b hb
      rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
      exact hle.2 i (hv _ (List.mem_map_of_mem hi))
    · rw [hop, orEval] at hv ⊢
      rw [List.any_eq_true] at hv ⊢
      rcases hv with ⟨b, hb, hbT⟩
      rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
      exact ⟨l2.getD i false, List.mem_map_of_mem hi, hle.2 i hbT⟩
  have hMonoRun (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
      gs.countP isNot = 0 →
      ∀ l1 l2 : List Bool, wle l1 l2 →
      wle ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l1)
          ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l2) := by
    induction gs with
    | nil => intro _ _ l1 l2 hle; exact hle
    | cons g gs ih =>
      intro hF h0 l1 l2 hle
      have hgF := hF g (List.mem_cons_self ..)
      have hgsF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ := fun q hq => hF q (List.mem_cons_of_mem _ hq)
      have hnotg : isNot g = false := by
        cases hgn : isNot g
        · rfl
        · rw [List.countP_cons, hgn] at h0
          simp at h0
      have h0gs : gs.countP isNot = 0 := by
        rw [List.countP_cons, hnotg] at h0
        simpa using h0
      have hgop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        have hmem := hgF.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with ha | ho | hn
        · exact Or.inl ha
        · exact Or.inr ho
        · simp only [isNot, hn] at hnotg
          contradiction
      rw [hWiresCons, hWiresCons]
      exact ih hgsF h0gs _ _ (hMonoStep g hgop l1 l2 hle)
  have hOfFnLe (x y : Fin 10 → Bool) (hxy : ∀ i : Fin 10, x i = true → y i = true) :
      wle (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hlt : i < 10
    · rw [List.getD_eq_getElem _ _ (by simp; exact hlt), List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem _ _ (by simp; exact hlt), List.getElem_ofFn]
      exact hxy ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction
  have hP0 : P (fun _ => false) = false := rfl
  have hP1 : P (fun _ => true) = true := rfl
  have hNoAntiMono (f : (Fin 10 → Bool) → Bool)
      (hmon : ∀ x y : Fin 10 → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true)
      (heq : ∀ x : Fin 10 → Bool, (!f x) = P x) : False := by
    have hf0 : f (fun _ => false) = true := by
      have h := heq (fun _ => false)
      rw [hP0] at h
      cases hval : f (fun _ => false)
      · rw [hval] at h; cases h
      · rfl
    have hf1 : f (fun _ => true) = false := by
      have h := heq (fun _ => true)
      rw [hP1] at h
      cases hval : f (fun _ => true)
      · rfl
      · rw [hval] at h; cases h
    have hle := hmon (fun _ => false) (fun _ => true) (fun _ h => by contradiction) hf0
    rw [hf1] at hle
    contradiction
  have hSplitOneNot : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      gs.countP isNot = 1 →
      ∃ (pre : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate)
        (post : List PEqualNP.CircuitLowerBounds.Gate),
        gs = pre ++ g :: post ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        pre.countP isNot = 0 ∧ post.countP isNot = 0 := by
    intro gs
    induction gs with
    | nil => intro h; simp at h
    | cons g gs ih =>
      intro h
      cases hgn : g.op with
      | not =>
        have h0 : gs.countP isNot = 0 := by
          rw [List.countP_cons] at h
          have : isNot g = true := by simp [isNot, hgn]
          rw [this] at h
          simpa using h
        exact ⟨[], g, gs, rfl, hgn, rfl, h0⟩
      | and =>
        have h1' : gs.countP isNot = 1 := by
          rw [List.countP_cons] at h
          have : isNot g = false := by simp [isNot, hgn]
          rw [this] at h
          simpa using h
        obtain ⟨pre, gn, post, rfl, hgop, hp0, hq0⟩ := ih h1'
        refine ⟨g :: pre, gn, post, rfl, hgop, ?_, hq0⟩
        rw [List.countP_cons]
        have : isNot g = false := by simp [isNot, hgn]
        rw [this, hp0]
        rfl
      | or =>
        have h1' : gs.countP isNot = 1 := by
          rw [List.countP_cons] at h
          have : isNot g = false := by simp [isNot, hgn]
          rw [this] at h
          simpa using h
        obtain ⟨pre, gn, post, rfl, hgop, hp0, hq0⟩ := ih h1'
        refine ⟨g :: pre, gn, post, rfl, hgop, ?_, hq0⟩
        rw [List.countP_cons]
        have : isNot g = false := by simp [isNot, hgn]
        rw [this, hp0]
        rfl
      | mod m =>
        have h1' : gs.countP isNot = 1 := by
          rw [List.countP_cons] at h
          have : isNot g = false := by simp [isNot, hgn]
          rw [this] at h
          simpa using h
        obtain ⟨pre, gn, post, rfl, hgop, hp0, hq0⟩ := ih h1'
        refine ⟨g :: pre, gn, post, rfl, hgop, ?_, hq0⟩
        rw [List.countP_cons]
        have : isNot g = false := by simp [isNot, hgn]
        rw [this, hp0]
        rfl
      | maj =>
        have h1' : gs.countP isNot = 1 := by
          rw [List.countP_cons] at h
          have : isNot g = false := by simp [isNot, hgn]
          rw [this] at h
          simpa using h
        obtain ⟨pre, gn, post, rfl, hgop, hp0, hq0⟩ := ih h1'
        refine ⟨g :: pre, gn, post, rfl, hgop, ?_, hq0⟩
        rw [List.countP_cons]
        have : isNot g = false := by simp [isNot, hgn]
        rw [this, hp0]
        rfl
  by_cases hNot0 : C.gates.countP isNot = 0
  · cases hx4 : x4
    · obtain ⟨x, hx⟩ := hMono C hC hNot0 (by change C.gates.length ≤ 18; omega)
      have he := hCeval x
      rw [hx4] at he
      exact hx he
    · apply hNoAntiMono (fun x => C.eval (List.ofFn x))
      · intro x y hxy hx
        have hrun := hMonoRun C.gates hC hNot0 (List.ofFn x) (List.ofFn y) (hOfFnLe x y hxy)
        exact hrun.2 x3 hx
      · intro x
        have he := hCeval x
        rw [hx4] at he
        exact he
  · have hNot1 : C.gates.countP isNot = 1 := by omega
    obtain ⟨pre, gnot, post, hsplit, hgnop, hpre0, hpost0⟩ := hSplitOneNot C.gates hNot1
    have hFanPre : PEqualNP.MetaComplexity.FanInTwo ⟨pre, 0⟩ := by
      intro q hq
      apply hC q
      rw [hsplit]
      exact List.mem_append_left _ hq
    have hFanPost : PEqualNP.MetaComplexity.FanInTwo ⟨post, 0⟩ := by
      intro q hq
      apply hC q
      rw [hsplit]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
    have hLenSum : pre.length + post.length = 17 := by
      rw [hsplit, List.length_append, List.length_cons] at hClen
      omega
    have hCsplit (x : Fin 10 → Bool) :
        C.eval (List.ofFn x) =
        ((⟨post, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
          (step ((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)) gnot)).getD x3 false := by
      change (C.wires (List.ofFn x)).getD x3 false = _
      have hw : C.wires (List.ofFn x) = (⟨pre ++ gnot :: post, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) := by
        change C.gates.foldl step (List.ofFn x) = (pre ++ gnot :: post).foldl step (List.ofFn x)
        rw [hsplit]
      rw [hw, hWiresAppend, hWiresCons]
    have hConstNot (hconst : ∀ x : Fin 10 → Bool,
        gnot.op.eval (gnot.inputs.map fun i => ((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD i false) = true) :
        False := by
      let gtrue : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre ++ gtrue :: post, x3⟩
      have hFanC' : PEqualNP.MetaComplexity.FanInTwo C' := by
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hFanPre q hq
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨Set.mem_insert _ _, by simp [gtrue]⟩
          · exact hFanPost q hq
      have hNotC' : C'.gates.countP isNot = 0 := by
        change (pre ++ gtrue :: post).countP isNot = 0
        rw [List.countP_append, List.countP_cons, hpre0, hpost0]
        rfl
      have hSizeC' : C'.size ≤ 18 := by
        change (pre ++ gtrue :: post).length ≤ 18
        rw [List.length_append, List.length_cons]
        omega
      have hSameC' (x : Fin 10 → Bool) : C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
        rw [hCsplit x]
        change ((⟨pre ++ gtrue :: post, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD x3 false = _
        rw [hWiresAppend, hWiresCons]
        have hst : step ((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)) gtrue =
            step ((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)) gnot := by
          simp only [step, hconst x]
          rfl
        rw [hst]
      cases hx4 : x4
      · obtain ⟨x, hx⟩ := hMono C' hFanC' hNotC' hSizeC'
        have he := hCeval x
        rw [hx4, ← hSameC' x] at he
        exact hx he
      · apply hNoAntiMono (fun x => C'.eval (List.ofFn x))
        · intro x y hxy hx
          have hrun := hMonoRun C'.gates hFanC' hNotC' (List.ofFn x) (List.ofFn y) (hOfFnLe x y hxy)
          exact hrun.2 x3 hx
        · intro x
          have he := hCeval x
          rw [hx4, ← hSameC' x] at he
          exact he
    cases hgi : gnot.inputs with
    | nil =>
      apply hConstNot
      intro x
      rw [hgnop, hgi, notEval]
      rfl
    | cons a rest =>
      by_cases haLt : a < 10 + pre.length
      · have hStepEq (x : Fin 10 → Bool) :
            step ((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)) gnot =
            ((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)) ++
              [!(((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD a false)] := by
          simp only [step, hgnop, hgi, List.map_cons, notEval, List.headD_cons]
        cases hx4 : x4
        · have hx3Lt : x3 < 28 := by
            by_contra hge
            have hlenC : (C.wires (List.ofFn (fun _ : Fin 10 => true))).length = 28 := by
              have hl := hWiresLen C.gates (List.ofFn (fun _ : Fin 10 => true))
              change (C.wires (List.ofFn (fun _ : Fin 10 => true))).length = _ at hl
              rw [List.length_ofFn, hClen] at hl
              exact hl
            have hdef : C.eval (List.ofFn (fun _ : Fin 10 => true)) = false := by
              change (C.wires (List.ofFn (fun _ : Fin 10 => true))).getD x3 false = false
              exact List.getD_eq_default _ _ (by omega)
            have he := hCeval (fun _ => true)
            rw [hx4, hdef, hP1] at he
            contradiction
          have hNormEq (x : Fin 10 → Bool) :
              (⟨pre ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩ :: post, x3⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) =
              C.eval (List.ofFn x) := by
            rw [hCsplit x, hStepEq x]
            change ((⟨pre ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [a]⟩ :: post, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD x3 false = _
            rw [hWiresAppend, hWiresCons]
            simp only [step, List.map_cons, List.map_nil, notEval, List.headD_cons]
          by_cases hle3 : pre.length ≤ 3
          · obtain ⟨x, hx⟩ := hOneNotEarly pre post a x3 hFanPre hFanPost hpre0 hpost0 hle3 hLenSum haLt hx3Lt
            have he := hCeval x
            rw [hx4, ← hNormEq x] at he
            exact hx he
          · obtain ⟨x, hx⟩ := hOneNotLate pre post a x3 hFanPre hFanPost hpre0 hpost0 (by omega) hLenSum haLt hx3Lt
            have he := hCeval x
            rw [hx4, ← hNormEq x] at he
            exact hx he
        · let U : PEqualNP.CircuitLowerBounds.Circuit := ⟨pre, a⟩
          let u : (Fin 10 → Bool) → Bool := fun x => U.eval (List.ofFn x)
          have hUmono : ∀ x y : Fin 10 → Bool, (∀ i, x i = true → y i = true) → u x = true → u y = true := by
            intro x y hxy hx
            exact (hMonoRun pre hFanPre hpre0 (List.ofFn x) (List.ofFn y) (hOfFnLe x y hxy)).2 a hx
          have hCmonoOf (x y : Fin 10 → Bool) (hxy : ∀ i, x i = true → y i = true)
              (huxy : (!u x) = true → (!u y) = true) (hcx : C.eval (List.ofFn x) = true) :
              C.eval (List.ofFn y) = true := by
            rw [hCsplit x, hStepEq x] at hcx
            rw [hCsplit y, hStepEq y]
            have hp := hMonoRun pre hFanPre hpre0 (List.ofFn x) (List.ofFn y) (hOfFnLe x y hxy)
            have ha := hWleApp _ _ (!u x) (!u y) hp huxy
            exact (hMonoRun post hFanPost hpost0 _ _ ha).2 x3 hcx
          cases hu0 : u (fun _ => false) with
          | true =>
            apply hNoAntiMono (fun x => C.eval (List.ofFn x))
            · intro x y hxy hcx
              have hux : u x = true := hUmono (fun _ => false) x (fun _ h => by contradiction) hu0
              have huy : u y = true := hUmono (fun _ => false) y (fun _ h => by contradiction) hu0
              exact hCmonoOf x y hxy (by rw [hux, huy]; intro h; exact h) hcx
            · intro x
              have he := hCeval x
              rw [hx4] at he
              exact he
          | false =>
            cases hu1 : u (fun _ => true) with
            | false =>
              apply hNoAntiMono (fun x => C.eval (List.ofFn x))
              · intro x y hxy hcx
                have hux : u x = false := by
                  cases hv : u x
                  · rfl
                  · have := hUmono x (fun _ => true) (fun _ _ => rfl) hv
                    rw [hu1] at this
                    contradiction
                have huy : u y = false := by
                  cases hv : u y
                  · rfl
                  · have := hUmono y (fun _ => true) (fun _ _ => rfl) hv
                    rw [hu1] at this
                    contradiction
                exact hCmonoOf x y hxy (by rw [hux, huy]; intro h; exact h) hcx
              · intro x
                have he := hCeval x
                rw [hx4] at he
                exact he
            | true =>
              have hUeq : ∀ x : Fin 10 → Bool, u x = P x := by
                intro x
                cases hux : u x with
                | false =>
                  have hcz0 : C.eval (List.ofFn (fun _ : Fin 10 => false)) = true := by
                    have he := hCeval (fun _ => false)
                    rw [hx4, hP0] at he
                    simp only [ite_true] at he
                    cases hv : C.eval (List.ofFn (fun _ : Fin 10 => false))
                    · rw [hv] at he; cases he
                    · rfl
                  have hcx : C.eval (List.ofFn x) = true :=
                    hCmonoOf (fun _ => false) x (fun _ h => by contradiction) (by rw [hu0, hux]; intro h; exact h) hcz0
                  have he := hCeval x
                  rw [hx4, hcx] at he
                  exact he
                | true =>
                  have hcz1 : C.eval (List.ofFn (fun _ : Fin 10 => true)) = false := by
                    have he := hCeval (fun _ => true)
                    rw [hx4, hP1] at he
                    simp only [ite_true] at he
                    cases hv : C.eval (List.ofFn (fun _ : Fin 10 => true))
                    · rfl
                    · rw [hv] at he; cases he
                  have hcx : C.eval (List.ofFn x) = false := by
                    cases hv : C.eval (List.ofFn x)
                    · rfl
                    · have := hCmonoOf x (fun _ => true) (fun _ _ => rfl) (by rw [hux, hu1]; intro h; exact h) hv
                      rw [hcz1] at this
                      contradiction
                  have he := hCeval x
                  rw [hx4, hcx] at he
                  exact he
              obtain ⟨x, hx⟩ := hMono U hFanPre hpre0 (by change pre.length ≤ 18; omega)
              exact hx (hUeq x)
      · apply hConstNot
        intro x
        rw [hgnop, hgi, List.map_cons, notEval, List.headD_cons]
        have hl : ((⟨pre, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).length = 10 + pre.length := by
          have := hWiresLen pre (List.ofFn x)
          rw [List.length_ofFn] at this
          exact this
        rw [List.getD_eq_default _ _ (by omega)]
        rfl
