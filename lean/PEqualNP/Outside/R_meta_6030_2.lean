import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6030_2
    (cofactor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
    (elim : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
      (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate), C.gates = g :: gs ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) →
      PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  classical
  intro C rho hFan hsize hnoth
  by_contra hcon
  push_neg at hcon

  let ρ : ℕ → ℕ := fun i => if h : i < 10 then (rho ⟨i, h⟩ : ℕ) else i
  have rho_lt10 : ∀ i, i < 10 → ρ i < 10 := by
    intro i hi
    show (if h : i < 10 then (rho ⟨i, h⟩ : ℕ) else i) < 10
    rw [dif_pos hi]
    exact Fin.isLt _
  have rlt : ∀ i L, 11 ≤ L → (ρ i < L ↔ i < L) ∧ (ρ i = L ↔ i = L) := by
    intro i L hL
    by_cases hi : i < 10
    · have p : ρ i = (rho ⟨i, hi⟩ : ℕ) := dif_pos hi
      rw [p]
      exact ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun e => by omega, fun e => by omega⟩⟩
    · have p : ρ i = i := dif_neg hi
      rw [p]
      exact ⟨⟨fun h => h, fun h => h⟩, ⟨fun h => h, fun h => h⟩⟩

  let F : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w
  let G : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD (ρ j) false)]) w

  have step_eq : ∀ (g : Gate) (w : List Bool),
      { g with inputs := g.inputs.map ρ }.op.eval
          ({ g with inputs := g.inputs.map ρ }.inputs.map fun j => w.getD j false) =
        g.op.eval (g.inputs.map fun j => w.getD (ρ j) false) := by
    intro g w
    show g.op.eval ((g.inputs.map ρ).map fun j => w.getD j false) =
      g.op.eval (g.inputs.map fun j => w.getD (ρ j) false)
    rw [List.map_map]
    rfl
  have wire_map : ∀ gs w, F (gs.map fun g => { g with inputs := g.inputs.map ρ }) w = G gs w := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      simp only [F, G, List.map_cons, List.foldl_cons, ih, step_eq]

  have key : ∀ (gs : List Gate) (W W' : List Bool),
      W.length = W'.length → 11 ≤ W.length →
      (∀ i, W'.getD (ρ i) false = W.getD i false) →
      ∀ i, (G gs W').getD (ρ i) false = (F gs W).getD i false := by
    intro gs
    induction gs with
    | nil => intro W W' _ _ h i; exact h i
    | cons g gs ih =>
      intro W W' hl hL h i
      have veq : g.op.eval (g.inputs.map fun j => W'.getD (ρ j) false) =
          g.op.eval (g.inputs.map fun j => W.getD j false) := by
        congr 1
        exact List.map_congr_left (fun j _ => h j)
      have hext : ∀ k,
          (W' ++ [g.op.eval (g.inputs.map fun j => W'.getD (ρ j) false)]).getD (ρ k) false =
            (W ++ [g.op.eval (g.inputs.map fun j => W.getD j false)]).getD k false := by
        intro k
        rw [← veq]
        rcases Nat.lt_trichotomy (ρ k) W.length with hlt | heq | hgt
        · have iL : k < W.length := (rlt k W.length hL).1.mp hlt
          have hl' : ρ k < W'.length := by rw [← hl]; exact hlt
          rw [List.getD_append _ _ _ _ hl', List.getD_append _ _ _ _ iL]
          exact h k
        · have iL : k = W.length := (rlt k W.length hL).2.mp heq
          have sub : ρ k - W'.length = k - W.length := by omega
          rw [List.getD_append_right _ _ _ _ (by omega : W'.length ≤ ρ k),
            List.getD_append_right _ _ _ _ (by omega : W.length ≤ k), sub]
        · have h10 : ¬ k < 10 := fun hk => by
            have a : ρ k < 10 := rho_lt10 k hk
            omega
          have pkeq : ρ k = k := dif_neg h10
          rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega :
              (W' ++ [_]).length ≤ ρ k),
            List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega :
              (W ++ [_]).length ≤ k)]
      show (G (g :: gs) W').getD (ρ i) false = (F (g :: gs) W).getD i false
      have gstep : G (g :: gs) W' =
          G gs (W' ++ [g.op.eval (g.inputs.map fun j => W'.getD (ρ j) false)]) := rfl
      have fstep : F (g :: gs) W =
          F gs (W ++ [g.op.eval (g.inputs.map fun j => W.getD j false)]) := rfl
      rw [gstep, fstep]
      exact ih (W ++ [g.op.eval (g.inputs.map fun j => W.getD j false)])
        (W' ++ [g.op.eval (g.inputs.map fun j => W'.getD (ρ j) false)])
        (by rw [List.length_append, List.length_append, List.length_singleton,
          List.length_singleton]; omega)
        (by rw [List.length_append, List.length_singleton]; omega) hext i

  let C' : Circuit :=
    { gates := C.gates.map fun g => { g with inputs := g.inputs.map ρ }
      output := ρ C.output }
  have wires_eq : ∀ (y : Fin 10 → Bool),
      C'.eval (List.ofFn y ++ [y 0 && y 2]) = C.eval (List.ofFn (y ∘ rho) ++ [y 0 && y 2]) := by
    intro y
    set I' := List.ofFn y ++ [y 0 && y 2] with I'd
    set I := List.ofFn (y ∘ rho) ++ [y 0 && y 2] with Id
    have len11 : I.length = 11 ∧ I'.length = 11 := by
      rw [I'd, Id]
      simp
    have hbase : ∀ i, I'.getD (ρ i) false = I.getD i false := by
      intro i
      by_cases hi : i < 10
      · have p : ρ i = (rho ⟨i, hi⟩ : ℕ) := dif_pos hi
        have h1 : (List.ofFn y ++ [y 0 && y 2]).getD (rho ⟨i, hi⟩ : ℕ) false = y (rho ⟨i, hi⟩) := by
          have hl : (rho ⟨i, hi⟩ : ℕ) < (List.ofFn y).length := by
            rw [List.length_ofFn]; exact Fin.isLt _
          rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
        have h2 : (List.ofFn (y ∘ rho) ++ [y 0 && y 2]).getD i false = (y ∘ rho) ⟨i, hi⟩ := by
          have hl : i < (List.ofFn (y ∘ rho)).length := by rw [List.length_ofFn]; exact hi
          rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
        rw [I'd, Id, p, h1, h2]
        rfl
      · have p : ρ i = i := dif_neg hi
        rw [I'd, Id, p,
          List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega :
            (List.ofFn y).length ≤ i),
          List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega :
            (List.ofFn (y ∘ rho)).length ≤ i),
          List.length_ofFn, List.length_ofFn]
    have hI : ∀ j, (G C.gates I').getD (ρ j) false = (F C.gates I).getD j false :=
      key C.gates I I' (by rw [len11.1, len11.2]) (by rw [len11.1] : 11 ≤ I.length) hbase
    show (F (C.gates.map fun g => { g with inputs := g.inputs.map ρ }) I').getD (ρ C.output) false =
        (F C.gates I).getD C.output false
    rw [wire_map C.gates I', hI (C.output)]
  have hFan' : FanInTwo C' := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hFan g0 hg0).1, by rw [List.length_map]; exact (hFan g0 hg0).2⟩
  have hsize' : C'.size ≤ 18 := by
    show C'.gates.length ≤ 18
    rw [show C'.gates = C.gates.map (fun g => { g with inputs := g.inputs.map ρ }) from rfl,
      List.length_map]
    exact hsize
  have hnot' : ∃ (g : Gate) (gs : List Gate), C'.gates = g :: gs ∧ g.op = GateOp.not := by
    obtain ⟨g0, gs0, hgs, hop⟩ := hnoth
    refine ⟨{ g0 with inputs := g0.inputs.map ρ }, gs0.map (fun g => { g with inputs := g.inputs.map ρ }), ?_, ?_⟩
    · show (C.gates.map fun g => { g with inputs := g.inputs.map ρ }) = _
      rw [hgs, List.map_cons]
    · exact hop
  have hcomp : ∀ x : Fin 10 → Bool,
      C'.eval (List.ofFn x ++ [x 0 && x 2]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    rw [wires_eq x]
    exact hcon x
  exact cofactor (elim C' hFan' hsize' hnot' hcomp)
