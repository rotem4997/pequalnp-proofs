import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_5877_426 :
    (∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧
          (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∧
          x a = true ∧ x b = true) →
      ¬∃ (k : Nat) (g : Gate), C.gates[k]? = some g ∧ g.op = .and ∧
        (C.wires (List.ofFn (fun i : Fin 42 => decide (i = 0 ∨ i = 1)))).getD (42 + k) false = true) →
    (∀ C : Circuit, Monotone2 C → C.size ≤ 124 →
      (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ a b : Fin 42, (a.val < 21 ∧ 21 ≤ b.val ∧
          (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∧
          x a = true ∧ x b = true) →
      ¬∃ (k : Nat) (g : Gate), C.gates[k]? = some g ∧ g.op = .and ∧
        (C.wires (List.ofFn (fun i : Fin 42 => decide (i = 0 ∨ i = 22)))).getD (42 + k) false = true) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (124 : ℕ) →       (∀ (x4 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) →         have x5 : List ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (3436108316976 : ℕ), (154640061441 : ℕ), (1168315262978 : ℕ)];         have x6 : ℕ → Fin (42 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (42 : ℕ)) => x6.testBit ↑x7;         have x7 : (Fin (42 : ℕ) → Bool) → Prop := fun (x7 : Fin (42 : ℕ) → Bool) => ∃ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x8]? = Option.some x9 ∧ x9.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn x7)).getD ((42 : ℕ) + x8) Bool.false = Bool.true;         have x8 : ℕ → Finset ℕ := fun (x8 : ℕ) => {x9 ∈ Finset.range x1.size | ((Option.map (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x11 : ℕ) => Bool.false) Bool.false x10.op) x1.gates[x9]?).getD Bool.false && !(x1.wires (List.ofFn (x6 x8))).getD ((42 : ℕ) + x9) Bool.false) = Bool.true};         (x7 fun (x9 : Fin (42 : ℕ)) => Decidable.decide (↑x9 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)])) → ((∃ x10 ∈ x5, x7 (x6 x10)) ∧ ∀ x10 ∈ x5, (33 : ℕ) ≤ (x8 x10).card) → False := by
  intro hSame hCross
  let run (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

  have run_append (gs hs : List Gate) (w : List Bool) :
      run (gs ++ hs) w = run hs (run gs w) := by
    simp [run, List.foldl_append]

  have run_ext (gs : List Gate) (w : List Bool) :
      ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
      refine ⟨v :: t, ?_, by simp [hl]⟩
      change run gs (w ++ [v]) = w ++ v :: t
      simp [ht]

  have run_length (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := run_ext gs w
    rw [ht, List.length_append, hl]

  have run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := run_ext gs w
    rw [ht, List.getD_append _ _ _ _ hi]

  have prefix_read (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
      (run (gs.take k) w).getD i false =
        if i < w.length + k then (run gs w).getD i false else false := by
    have hlen : (run (gs.take k) w).length = w.length + k := by
      rw [run_length, List.length_take, min_eq_left hk]
    split_ifs with hi
    · conv_rhs => rw [← List.take_append_drop k gs, run_append]
      exact (run_input _ _ _ (by omega)).symm
    · exact List.getD_eq_default _ _ (by omega)

  have run_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
      (run gs w).getD (w.length + k) false =
        gs[k].op.eval (gs[k].inputs.map fun i =>
          if i < w.length + k then (run gs w).getD i false else false) := by
    have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      have h := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h
      exact h
    have hlen : (run (gs.take k) w).length = w.length + k := by
      rw [run_length, List.length_take, min_eq_left (Nat.le_of_lt hk)]
    have heq : run gs w =
        run (gs.drop (k + 1)) (run (gs.take k) w ++
          [gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit, run_append]
      rfl
    calc
      (run gs w).getD (w.length + k) false =
          gs[k].op.eval (gs[k].inputs.map fun i => (run (gs.take k) w).getD i false) := by
        rw [heq, run_input]
        · simp [← hlen]
        · simp [hlen]
      _ = _ := by
        congr 1
        apply List.map_congr_left
        intro i _
        exact prefix_read gs w k i (Nat.le_of_lt hk)


  let wire (C : Circuit) (y : (Fin 42 → Bool)) (i : ℕ) : Bool :=
    (C.wires (List.ofFn y)).getD i false

  let read (C : Circuit) (y : (Fin 42 → Bool)) (k i : ℕ) : Bool :=
    if i < 42 + k then wire C y i else false

  have wire_input (C : Circuit) (y : (Fin 42 → Bool)) (i : Fin 42) : wire C y i.val = y i := by
    change (run C.gates (List.ofFn y)).getD i.val false = y i
    rw [run_input, List.getD_eq_getElem, List.getElem_ofFn]
    all_goals simp

  have wire_outside (C : Circuit) (y : (Fin 42 → Bool)) {i : ℕ} (hi : 42 + C.gates.length ≤ i) :
      wire C y i = false := by
    change (run C.gates (List.ofFn y)).getD i false = false
    exact List.getD_eq_default _ _ (by simpa [run_length] using hi)

  have gate_sem (C : Circuit) (y : (Fin 42 → Bool)) {k : ℕ} {g : Gate}
      (hg : C.gates[k]? = some g) :
      wire C y (42 + k) = g.op.eval (g.inputs.map (read C y k)) := by
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hg
    change (run C.gates (List.ofFn y)).getD (42 + k) false = _
    have h := run_gate C.gates (List.ofFn y) k hk
    rw [List.length_ofFn] at h
    exact h

  have and_sem (C : Circuit) (y : (Fin 42 → Bool)) {k : ℕ} {g : Gate}
      (hg : C.gates[k]? = some g) (ho : g.op = .and) :
      wire C y (42 + k) = true ↔ ∀ i ∈ g.inputs, read C y k i = true := by
    rw [gate_sem C y hg, ho]
    change (g.inputs.map (read C y k)).all id = true ↔ _
    simp [List.all_eq_true]

  have or_sem (C : Circuit) (y : (Fin 42 → Bool)) {k : ℕ} {g : Gate}
      (hg : C.gates[k]? = some g) (ho : g.op = .or) :
      wire C y (42 + k) = true ↔ ∃ i ∈ g.inputs, read C y k i = true := by
    rw [gate_sem C y hg, ho]
    change (g.inputs.map (read C y k)).any id = true ↔ _
    simp [List.any_eq_true]

  have gate_mono {C : Circuit} (hc : Monotone2 C) {k : ℕ} {g : Gate}
      (hg : C.gates[k]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      hc _ (List.getElem_mem hk)

  have inputs_cases (l : List ℕ) (hl : l.length ≤ 2) :
      l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
    cases l with
    | nil => exact Or.inl rfl
    | cons a l =>
      cases l with
      | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
      | cons b l =>
        cases l with
        | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
        | cons c l => simp at hl

  let base : List (Fin 42) := [0, 1, 2, 6, 8, 18, 24, 31, 33, 37]

  let baseInput : (Fin 42 → Bool) := fun i => decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ))

  have base_spec (i : Fin 42) : baseInput i = true ↔ i ∈ base := by
    change decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)) = true ↔ i ∈ base
    rw [decide_eq_true_eq]
    have h : base.map Fin.val = [0, 1, 2, 6, 8, 18, 24, 31, 33, 37] := rfl
    rw [← h, List.mem_map]
    constructor
    · rintro ⟨a, ha, he⟩
      exact Fin.ext he ▸ ha
    · intro hi
      exact ⟨i, hi, rfl⟩

  let hit (C : Circuit) (y : (Fin 42 → Bool)) : Prop :=
    ∃ k g, C.gates[k]? = some g ∧ g.op = .and ∧ wire C y (42 + k) = true

  have before_first_and {C : Circuit} (hc : Monotone2 C) {k : ℕ} (hk : k < C.gates.length)
      (hfirst : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = .and →
        wire C baseInput (42 + j) ≠ true) :
      ∀ w < 42 + k, wire C baseInput w = true →
        ∃ i ∈ base, ∀ y : (Fin 42 → Bool), y i = true → wire C y w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw htrue
      by_cases hin : w < 42
      · let i : Fin 42 := ⟨w, hin⟩
        have hi := (base_spec i).mp ((wire_input C baseInput i).symm.trans htrue)
        exact ⟨i, hi, fun y hy => (wire_input C y i).trans hy⟩
      · let j := w - 42
        have he : w = 42 + j := by dsimp [j]; omega
        have hj : j < k := by omega
        have hj' : j < C.gates.length := by omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj'
        have ht : wire C baseInput (42 + j) = true := he ▸ htrue
        have ho : g.op = .or := (gate_mono hc hg).1.resolve_left
          (fun ha => hfirst j hj g hg ha ht)
        obtain ⟨a, ha, hra⟩ := (or_sem C baseInput hg ho).mp ht
        by_cases hlt : a < 42 + j
        · have hwa : wire C baseInput a = true := by simpa [read, hlt] using hra
          obtain ⟨i, hi, hiw⟩ := ih a (by omega) (by omega) hwa
          refine ⟨i, hi, fun y hy => ?_⟩
          rw [he, or_sem C y hg ho]
          exact ⟨a, ha, by simpa [read, hlt] using hiw y hy⟩
        · simp [read, hlt] at hra

  have getPair {C : Circuit} (hc : Monotone2 C) (hh : hit C baseInput) :
      ∃ i ∈ base, ∃ j ∈ base, ∀ y : (Fin 42 → Bool), y i = true → y j = true → hit C y := by
    classical
    let P := fun k => ∃ g, C.gates[k]? = some g ∧ g.op = .and ∧ wire C baseInput (42 + k) = true
    have hex : ∃ k, P k := hh
    let k := Nat.find hex
    obtain ⟨g, hg, ho, ht⟩ := Nat.find_spec hex
    have hg' : C.gates[k]? = some g := hg
    have hk : k < C.gates.length := (List.getElem?_eq_some_iff.mp hg').choose
    have hfirst : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = .and →
        wire C baseInput (42 + j) ≠ true := by
      intro j hj gate hgate hop hwire
      exact Nat.find_min hex hj ⟨gate, hgate, hop, hwire⟩
    have hread : ∀ a ∈ g.inputs, ∃ i ∈ base, ∀ y : (Fin 42 → Bool), y i = true → read C y k a = true := by
      intro a ha
      have hr := (and_sem C baseInput hg' ho).mp ht a ha
      by_cases hlt : a < 42 + k
      · simpa [read, hlt] using before_first_and hc hk hfirst a hlt (by simpa [read, hlt] using hr)
      · simp [read, hlt] at hr
    have hpair : ∃ i ∈ base, ∃ j ∈ base, ∀ y : (Fin 42 → Bool), y i = true → y j = true →
        ∀ a ∈ g.inputs, read C y k a = true := by
      have hzero : (0 : Fin 42) ∈ base := by decide
      rcases inputs_cases _ (gate_mono hc hg').2 with he | ⟨a, he⟩ | ⟨a, b, he⟩
      · exact ⟨0, hzero, 0, hzero, by simp [he]⟩
      · obtain ⟨i, hi, hp⟩ := hread a (by simp [he])
        refine ⟨i, hi, i, hi, fun y hy _ c hmem => ?_⟩
        have heq : c = a := by simpa [he] using hmem
        exact heq.symm ▸ hp y hy
      · obtain ⟨i, hi, hp⟩ := hread a (by simp [he])
        obtain ⟨j, hj, hq⟩ := hread b (by simp [he])
        refine ⟨i, hi, j, hj, fun y hy hz c hmem => ?_⟩
        simp only [he, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact hp y hy
        · exact hq y hz
    obtain ⟨i, hi, j, hj, hp⟩ := hpair
    exact ⟨i, hi, j, hj, fun y hy hz => ⟨k, g, hg', ho, (and_sem C _ hg' ho).mpr (hp y hy hz)⟩⟩
  let edge (a b : Fin 42) : Prop :=
    a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)
  let hasEdge (x : Fin 42 → Bool) : Prop :=
    ∃ a b : Fin 42, edge a b ∧ x a = true ∧ x b = true
  let correct (C : Circuit) : Prop := ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ hasEdge x
  let good (y : Fin 42 → Bool) : Prop :=
    ∀ C : Circuit, Monotone2 C → C.size ≤ 124 → correct C → ¬hit C y
  let seed (b : Bool) (i : Fin 42) : Bool :=
    if b then decide (i = 0 ∨ i = 22) else decide (i = 0 ∨ i = 1)
  have goodSeed (b : Bool) : good (seed b) := by
    cases b
    · exact hSame
    · exact hCross
  let generators : List (List (Fin 42)) := [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 0, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 21], [21, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 0, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], [0, 3, 8, 10, 20, 9, 19, 7, 11, 5, 4, 2, 14, 18, 13, 12, 15, 1, 16, 6, 17, 41, 29, 36, 27, 37, 26, 24, 28, 31, 25, 30, 40, 35, 39, 33, 32, 22, 21, 23, 34, 38]]
  let perm (t : Fin 3) (i : Fin 42) : Fin 42 := (generators.getD t.val []).getD i.val 0
  let related (a b : Fin 42) := decide ((a.val < 21 ∧ 21 ≤ b.val ∧
    (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∨
    (b.val < 21 ∧ 21 ≤ a.val ∧ (a.val + 21 - b.val) % 21 ∈ ([0,5,7,17,20] : List Nat)))
  have relSpec (a b : Fin 42) : related a b = true ↔ edge a b ∨ edge b a := by
    simp only [related, decide_eq_true_eq, edge]
  have adjCheck : ∀ (t : Fin 3) (a b : Fin 42),
      related (perm t a) (perm t b) = related a b := by decide
  have ontoCheck : ∀ (t : Fin 3) (i : Fin 42), ∃ j : Fin 42, perm t j = i := by decide
  have edgePairs (x : Fin 42 → Bool) :
      hasEdge x ↔ ∃ a b : Fin 42, (edge a b ∨ edge b a) ∧ x a = true ∧ x b = true := by
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨a,b,Or.inl hab,ha,hb⟩
    · rintro ⟨a,b,hab,ha,hb⟩
      rcases hab with h | h
      · exact ⟨a,b,h,ha,hb⟩
      · exact ⟨b,a,h,hb,ha⟩
  have preserve (t : Fin 3) (x : Fin 42 → Bool) : hasEdge (x ∘ perm t) ↔ hasEdge x := by
    rw [edgePairs, edgePairs]
    have eqv (a b : Fin 42) : (edge (perm t a) (perm t b) ∨ edge (perm t b) (perm t a)) ↔
        (edge a b ∨ edge b a) := by
      rw [← relSpec, ← relSpec, adjCheck]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨_,_,(eqv a b).2 hab,ha,hb⟩
    · rintro ⟨a,b,hab,ha,hb⟩
      obtain ⟨u,rfl⟩ := ontoCheck t a
      obtain ⟨v,rfl⟩ := ontoCheck t b
      exact ⟨u,v,(eqv u v).1 hab,ha,hb⟩
  let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
    if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

  let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wmap n m π)⟩

  let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
    ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
    n ≤ W.length ∧ W'.length + n = W.length + m ∧
      ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

  have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
      (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (relGate n m π g).op.eval
        ((relGate n m π g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h3 a
    refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
    intro w
    simp only [step, hv]
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : wmap n m π w < W'.length := by
        unfold wmap
        split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 w
    · have he : wmap n m π w = W'.length := by
        unfold wmap
        split
        · omega
        · omega
      rw [he, hw]; simp
    · have hge : W'.length + 1 ≤ wmap n m π w := by
        unfold wmap
        split
        · omega
        · omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

  have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
      ∀ W W' : List Bool, Rel n m π W W' →
        Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
    induction gs with
    | nil => intro W W' h; exact h
    | cons g gs ih =>
      intro W W' h
      exact ih _ _ (rel_step n m π W W' g h)

  have rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
      Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
    refine ⟨by simp, by simp; omega, ?_⟩
    intro w
    unfold wmap
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
  have goodPull (y : Fin 42 → Bool) (t : Fin 3) (hy : good y) : good (y ∘ perm t) := by
    intro C hc hs he hh
    let p := perm t
    let D := relabel 42 42 p C
    have hDmono : Monotone2 D := by
      intro g hg
      obtain ⟨g₀,hmem,rfl⟩ := List.mem_map.mp hg
      exact ⟨(hc _ hmem).1, by simpa [relGate] using (hc _ hmem).2⟩
    have hDsize : D.size ≤ 124 := by
      change (C.gates.map (relGate 42 42 p)).length ≤ 124
      rw [List.length_map]
      exact hs
    have vals (x : Fin 42 → Bool) (w : Nat) :
        (D.wires (List.ofFn x)).getD (wmap 42 42 p w) false =
        (C.wires (List.ofFn (x ∘ p))).getD w false :=
      (rel_fold 42 42 p C.gates _ _ (rel_init 42 42 p x)).2.2 w
    have hDeval (x : Fin 42 → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ p)) :=
      vals x C.output
    apply hy D hDmono hDsize (fun x => (hDeval x) ▸ ((he (x ∘ p)).trans (preserve t x)))
    obtain ⟨k,g,hg,hop,hv⟩ := hh
    refine ⟨k,relGate 42 42 p g,?_,hop,?_⟩
    · change (C.gates.map (relGate 42 42 p))[k]? = some _
      simp [hg]
    · have hk : wmap 42 42 p (42 + k) = 42 + k := by simp [wmap]; omega
      change (D.wires _).getD (42 + k) false = true
      rw [← hk, vals]
      exact hv
  let walk (b : Bool) (w : List (Fin 3)) : Fin 42 → Bool :=
    w.foldl (fun y t => y ∘ perm t) (seed b)
  have goodWalk (b : Bool) (w : List (Fin 3)) : good (walk b w) := by
    have lift (l : List (Fin 3)) (y : Fin 42 → Bool) (hy : good y) :
        good (l.foldl (fun z t => z ∘ perm t) y) := by
      induction l generalizing y with
      | nil => exact hy
      | cons a l ih => exact ih _ (goodPull y a hy)
    exact lift w (seed b) (goodSeed b)
  let samples : List (Bool × List (Fin 3)) := [(false, []), (false, [0, 0, 2, 0, 0, 0, 0]), (false, [2, 0, 2, 0, 2, 0, 2]), (false, [0, 0, 2, 0, 2, 0]), (false, [0, 0, 2, 1, 2, 1, 0]), (true, [0, 2, 0, 2, 0]), (true, [2, 2, 2, 2]), (true, [0, 0, 2, 0, 2, 1]), (true, [2]), (false, [1, 0, 1]), (false, [0, 1, 2, 2, 0, 0, 1, 2]), (false, [1, 0, 0, 0, 2, 1]), (false, [2, 1, 0, 1]), (true, [2, 1, 2, 0, 2, 0]), (true, [2, 2, 2, 1, 0, 1]), (true, [2, 1, 0, 2, 0, 1]), (true, [0, 0, 2, 0, 1]), (false, [1, 2, 0, 0, 1]), (false, [2, 0, 2, 2, 0, 0, 2]), (false, [0, 1, 2, 2, 0, 1]), (true, [0, 0, 0, 1]), (true, [2, 0, 2, 2, 1, 0]), (true, [0, 2, 2, 0, 1]), (true, [2, 1, 0, 2, 2, 0]), (false, [0, 0, 2, 1, 0, 0, 1]), (false, [1, 0, 1, 2, 2, 0, 0]), (true, [2, 0, 1, 2, 0, 1]), (true, [2, 0, 1, 2, 2, 2, 2]), (true, [2, 0, 0, 2]), (true, [0, 2, 2, 0, 0, 0, 0]), (false, [0, 0, 0, 1, 2, 2, 1]), (true, [2, 0, 0, 0, 1]), (true, [0, 0, 0, 2, 0, 0, 2]), (true, [0, 2, 0, 1, 2, 0]), (true, [2, 1, 2, 0]), (true, [0, 0, 2, 2, 2, 1, 2, 1, 0]), (true, [0, 2, 0, 0, 1, 2, 0]), (true, [0, 0, 2, 1, 0, 0, 0]), (true, [0, 0, 2, 2, 0]), (false, [1, 2, 2, 0, 2, 0]), (false, [0, 0, 1, 2, 2, 0]), (false, [0, 0, 0, 2, 2, 1, 0, 2]), (false, [1, 0, 0, 2, 0]), (false, [0, 0, 0, 2, 2, 2, 0, 1]), (false, [0, 2, 2, 2, 1, 2, 0])]
  have cover : base.all (fun a => base.all (fun b =>
      samples.any (fun s => walk s.1 s.2 a && walk s.1 s.2 b))) = true := by decide
  intro C hc hs he
  change hit C baseInput → _ → False
  intro hactive _
  obtain ⟨a,ha,b,hb,hpair⟩ := getPair hc hactive
  have entry := List.all_eq_true.mp (List.all_eq_true.mp cover a ha) b hb
  obtain ⟨s,_,hh⟩ := List.any_eq_true.mp entry
  obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hh
  exact goodWalk s.1 s.2 C hc hs he (hpair _ h₁ h₂)
