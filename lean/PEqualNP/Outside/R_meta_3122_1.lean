import Mathlib
import PEqualNP.Defs

-- Reduction of L-meta-3122. The NOT wire, the OR wire and the gates form a trace from the nine
-- inputs. With at most 12 gates, or with one of the two extra wires unused, it has at most 14
-- steps, which the first hypothesis (the statement of L-meta-2183) forbids. The remaining case,
-- 13 gates with both extra wires used, is the second hypothesis.
theorem PEqualNP.Outside.R_meta_3122_1
    (h1 : have x1 : List ((Fin (9 : ℕ) → Bool) → Bool) := (List.ofFn fun (x1 : Fin (9 : ℕ)) (x2 : Fin (9 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ))]; ∀ (x2 : List ((Fin (9 : ℕ) → Bool) → Bool)),   (∀ (x3 : Fin x2.length),       have x4 : List ((Fin (9 : ℕ) → Bool) → Bool) := (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.false) :: (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.true) :: (x1 ++ List.take (↑x3) x2);       ∃ x5 ∈ x4, ∃ x6 ∈ x4, (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 && x6 x7) ∨ (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 || x6 x7) ∨ x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => !x5 x7) →     (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) ∈ (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.false) :: (x1 ++ x2) → (15 : ℕ) ≤ x2.length)
    (h2 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → ((∃ x4 ∈ x3.gates, (10 : ℕ) ∈ x4.inputs) ∨ x3.output = (10 : ℕ)) → ((∃ x4 ∈ x3.gates, (9 : ℕ) ∈ x4.inputs) ∨ (9 : ℕ) ∈ x1 ∨ x3.output = (9 : ℕ)) → ∃ (x7 : Fin (9 : ℕ) → Bool), have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]; x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro ops hlen C fan size _hgate
  dsimp only
  by_contra hall
  push_neg at hall
  obtain ⟨gs, o⟩ := C
  change gs.length ≤ 13 at size
  have L1 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (hs.foldl (fun w g => w ++ [F w g]) w).length = w.length + hs.length := by
    intro F hs
    induction hs with
    | nil => intro w; simp
    | cons g hs ih => intro w; rw [List.foldl_cons, ih]; simp; omega
  have L2 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length →
      (hs.foldl (fun w g => w ++ [F w g]) w).getD i false = w.getD i false := by
    intro F hs
    induction hs with
    | nil => intro w i _; simp
    | cons g hs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi
  have L3 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ) (hj : j < hs.length),
      (hs.foldl (fun w g => w ++ [F w g]) w).getD (w.length + j) false =
        F ((hs.take j).foldl (fun w g => w ++ [F w g]) w) hs[j] := by
    intro F hs w j hj
    have split : hs = hs.take j ++ (hs[j] :: hs.drop (j + 1)) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have hP : ((hs.take j).foldl (fun w g => w ++ [F w g]) w).length = w.length + j := by
      rw [L1]; simp; omega
    conv_lhs => rw [split]
    rw [List.foldl_append, List.foldl_cons, L2 _ _ _ _ (by simp; omega), ← hP]
    simp
  have L4 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j i : ℕ),
      i < w.length + j → j ≤ hs.length →
      ((hs.take j).foldl (fun w g => w ++ [F w g]) w).getD i false =
        (hs.foldl (fun w g => w ++ [F w g]) w).getD i false := by
    intro F hs w j i hi hj
    have split : hs = hs.take j ++ hs.drop j := by simp
    conv_rhs => rw [split]
    rw [List.foldl_append, L2 F (hs.drop j) ((hs.take j).foldl (fun w g => w ++ [F w g]) w) i
      (by rw [L1]; simp; omega)]
  have L5 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j i : ℕ),
      w.length + j ≤ i → j ≤ hs.length →
      ((hs.take j).foldl (fun w g => w ++ [F w g]) w).getD i false = false := by
    intro F hs w j i hi hj
    apply List.getD_eq_default
    rw [L1]
    simp
    omega
  -- one gate of fan-in at most two over members of a list is one step
  have gate_step : ∀ (pool : List ((Fin 9 → Bool) → Bool)) (g : PEqualNP.CircuitLowerBounds.Gate)
      (P : ℕ → (Fin 9 → Bool) → Bool) (h : (Fin 9 → Bool) → Bool),
      (fun _ => false) ∈ pool → (fun _ => true) ∈ pool →
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) →
      g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, P i ∈ pool) →
      (∀ x, h x = g.op.eval (g.inputs.map fun i => P i x)) →
      ∃ a ∈ pool, ∃ b ∈ pool,
        (h = fun x => a x && b x) ∨ (h = fun x => a x || b x) ∨ h = fun x => !a x := by
    intro pool g P h fm tm hop hlen hP hh
    have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hop
    rcases hin : g.inputs with _ | ⟨i, _ | ⟨i', _ | ⟨i'', rest⟩⟩⟩
    · rcases hop with hop | hop | hop
      · refine ⟨_, tm, _, tm, Or.inl ?_⟩
        funext x; rw [hh, hin, hop]; rfl
      · refine ⟨_, fm, _, fm, Or.inr (Or.inl ?_)⟩
        funext x; rw [hh, hin, hop]; rfl
      · refine ⟨_, fm, _, fm, Or.inr (Or.inr ?_)⟩
        funext x; rw [hh, hin, hop]; rfl
    · have mi := hP i (by rw [hin]; simp)
      rcases hop with hop | hop | hop
      · refine ⟨_, mi, _, mi, Or.inl ?_⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> rfl
      · refine ⟨_, mi, _, mi, Or.inr (Or.inl ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> rfl
      · refine ⟨_, mi, _, mi, Or.inr (Or.inr ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> rfl
    · have mi := hP i (by rw [hin]; simp)
      have mi' := hP i' (by rw [hin]; simp)
      rcases hop with hop | hop | hop
      · refine ⟨_, mi, _, mi', Or.inl ?_⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]
        cases P i x <;> cases P i' x <;> rfl
      · refine ⟨_, mi, _, mi', Or.inr (Or.inl ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]
        cases P i x <;> cases P i' x <;> rfl
      · refine ⟨_, mi, _, mi', Or.inr (Or.inr ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]
        cases P i x <;> cases P i' x <;> rfl
    · rw [hin] at hlen; simp at hlen
  -- the wires of the circuit on the extended input
  -- the inputs with the NOT wire, the OR wire, and all wires of the circuit
  obtain ⟨U, hU⟩ : ∃ U : (Fin 9 → Bool) → List Bool, U = fun x => List.ofFn x ++ [!x 0] :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (Fin 9 → Bool) → Bool, R = fun x =>
      PEqualNP.CircuitLowerBounds.GateOp.or.eval (ops.map fun i => (U x).getD i false) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : (Fin 9 → Bool) → List Bool, E = fun x => U x ++ [R x] := ⟨_, rfl⟩
  have Ulen (x : Fin 9 → Bool) : (U x).length = 10 := by rw [hU]; simp
  have Uin (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : (U x).getD i false = x ⟨i, hi⟩ := by
    rw [hU]
    simp only []
    rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_ofFn]
  have U9 (x : Fin 9 → Bool) : (U x).getD 9 false = !x 0 := by rw [hU]; simp
  have Uhi (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) : (U x).getD i false = false := by
    apply List.getD_eq_default
    rw [Ulen]
    exact hi
  have Elen (x : Fin 9 → Bool) : (E x).length = 11 := by rw [hE]; simp only []; simp [Ulen]
  have Elo (x : Fin 9 → Bool) (i : ℕ) (hi : i < 10) : (E x).getD i false = (U x).getD i false := by
    rw [hE]
    simp only []
    rw [List.getD_append _ _ _ _ (by rw [Ulen]; exact hi)]
  have E10 (x : Fin 9 → Bool) : (E x).getD 10 false = R x := by
    rw [hE]
    simp only []
    rw [List.getD_append_right _ _ _ _ (by simp [Ulen]), Ulen]
    rfl
  obtain ⟨W, hW⟩ : ∃ W : (Fin 9 → Bool) → List Bool,
      W = fun x => gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (E x) := ⟨_, rfl⟩
  have evW (x : Fin 9 → Bool) : (W x).getD o false =
      ({ gates := gs, output := o } : PEqualNP.CircuitLowerBounds.Circuit).eval
        (List.ofFn x ++ [!x 0] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (ops.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) := by
    rw [hW, hE, hR, hU]; rfl
  have ev (x : Fin 9 → Bool) := (evW x).trans (hall x)
  have Wlen (x : Fin 9 → Bool) : (W x).length = 11 + gs.length := by
    rw [hW]; simp only []; rw [L1, Elen]
  have WE (x : Fin 9 → Bool) (i : ℕ) (hi : i < 11) : (W x).getD i false = (E x).getD i false := by
    rw [hW]; simp only []; rw [L2 _ _ _ _ (by rw [Elen]; exact hi)]
  have olt : o < 11 + gs.length := by
    by_contra hge
    have e := ev (fun i => decide (i.val < 2))
    rw [List.getD_eq_default _ _ (by rw [Wlen]; omega)] at e
    revert e
    decide
  have o9 : ¬ o < 9 := by
    intro o9
    have e := ev (fun i => decide (i = ⟨o, o9⟩))
    rw [WE _ o (by omega), Elo _ o (by omega), Uin _ o o9] at e
    revert e
    generalize (⟨o, o9⟩ : Fin 9) = v
    revert v
    decide
  have w9 : (fun x => (W x).getD 9 false) = fun x => !x 0 := by
    funext x; rw [WE x 9 (by omega), Elo x 9 (by omega), U9]
  have w10 : (fun x => (W x).getD 10 false) = R := by
    funext x; rw [WE x 10 (by omega), E10]
  -- input functions and the pool of a trace
  have input_mem : ∀ (L : List ((Fin 9 → Bool) → Bool)) (v : Fin 9),
      (fun x : Fin 9 → Bool => x v) ∈ (fun _ => false) :: (fun _ => true) ::
        ((List.ofFn fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4] ++ L) := by
    intro L v
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨v, rfl⟩))))
  have list_mem : ∀ (L : List ((Fin 9 → Bool) → Bool)) (f : (Fin 9 → Bool) → Bool), f ∈ L →
      f ∈ (fun _ => false) :: (fun _ => true) ::
        ((List.ofFn fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4] ++ L) := by
    intro L f hf
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hf))
  -- the OR wire is one step over the inputs and, when 9 is read, the NOT wire
  have or_step : ∀ (L : List ((Fin 9 → Bool) → Bool)), (9 ∈ ops → (fun x => !x 0) ∈ L) →
      ∃ a ∈ (fun _ => false) :: (fun _ => true) ::
          ((List.ofFn fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4] ++ L),
        ∃ b ∈ (fun _ => false) :: (fun _ => true) ::
          ((List.ofFn fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4] ++ L),
        (R = fun x => a x && b x) ∨ (R = fun x => a x || b x) ∨ R = fun x => !a x := by
    intro L h9
    apply gate_step _ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ops⟩
      (fun i x => (U x).getD i false) R List.mem_cons_self
      (List.mem_cons_of_mem _ List.mem_cons_self) (by simp) hlen
    · intro i hi
      by_cases i9 : i < 9
      · have e : (fun x => (U x).getD i false) = fun x => x ⟨i, i9⟩ := by
          funext x; exact Uin x i i9
        rw [e]
        exact input_mem L _
      · by_cases i9' : i = 9
        · subst i9'
          have e : (fun x => (U x).getD 9 false) = fun x => !x 0 := by
            funext x; exact U9 x
          rw [e]
          exact list_mem L _ (h9 hi)
        · have e : (fun x => (U x).getD i false) = fun _ => false := by
            funext x; exact Uhi x i (by omega)
          rw [e]
          exact List.mem_cons_self
    · intro x
      rw [hR]
  -- a trace made of some extra wires followed by the gates of the circuit
  have core : ∀ X : List ((Fin 9 → Bool) → Bool), X.length + gs.length ≤ 14 →
      (∀ n (hn : n < X.length), ∃ a ∈ (fun _ => false) :: (fun _ => true) ::
          ((List.ofFn fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4] ++
            X.take n),
        ∃ b ∈ (fun _ => false) :: (fun _ => true) ::
          ((List.ofFn fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4] ++
            X.take n),
        (X[n] = fun x => a x && b x) ∨ (X[n] = fun x => a x || b x) ∨ X[n] = fun x => !a x) →
      (∀ g ∈ gs, ∀ i ∈ g.inputs, i = 9 ∨ i = 10 → (fun x => (W x).getD i false) ∈ X) →
      (o = 9 ∨ o = 10 → (fun x => (W x).getD o false) ∈ X) → False := by
    intro X hX hsteps hread hout
    obtain ⟨G, hG⟩ : ∃ G : List ((Fin 9 → Bool) → Bool),
        G = List.ofFn (fun j : Fin gs.length => fun x => (W x).getD (11 + j.val) false) := ⟨_, rfl⟩
    have Glen : G.length = gs.length := by rw [hG]; simp
    have Gget (j : ℕ) (hj : j < G.length) : G[j] = fun x => (W x).getD (11 + j) false := by
      subst hG
      simp only [List.getElem_ofFn]
    have bound := h1 (X ++ G) ?_ ?_
    · simp only [List.length_append, Glen] at bound
      omega
    · intro x3
      obtain ⟨n, hn⟩ := x3
      simp only [List.get_eq_getElem, Fin.val_mk]
      by_cases hnX : n < X.length
      · rw [List.getElem_append_left hnX, List.take_append_of_le_length (by omega)]
        exact hsteps n hnX
      · obtain ⟨j, rfl⟩ : ∃ j, n = X.length + j := ⟨n - X.length, by omega⟩
        have hj : j < gs.length := by simp only [List.length_append, Glen] at hn; omega
        rw [List.getElem_append_right (by omega), List.take_append]
        simp only [Nat.add_sub_cancel_left]
        rw [List.take_of_length_le (l := X) (i := X.length + j) (by omega)]
        rw [Gget j (by omega)]
        have okg := fan gs[j] (List.getElem_mem hj)
        apply gate_step _ gs[j] (fun i x =>
          ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (E x)).getD i false) _ List.mem_cons_self
          (List.mem_cons_of_mem _ List.mem_cons_self) okg.1 okg.2
        · intro i hi
          by_cases i9 : i < 9
          · have e : (fun x => ((gs.take j).foldl
                (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                (E x)).getD i false) = fun x => x ⟨i, i9⟩ := by
              funext x
              rw [L2 _ _ _ _ (by rw [Elen]; omega), Elo x i (by omega), Uin x i i9]
            rw [e]
            exact input_mem _ _
          · by_cases ix : i = 9 ∨ i = 10
            · have e : (fun x => ((gs.take j).foldl
                  (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                  (E x)).getD i false) = fun x => (W x).getD i false := by
                funext x
                rw [L2 _ _ _ _ (by rw [Elen]; omega), WE x i (by omega)]
              rw [e]
              exact list_mem _ _ (List.mem_append_left _
                (hread _ (List.getElem_mem hj) i hi ix))
            · by_cases ilo : i < 11 + j
              · have hl : i - 11 < G.length := by omega
                have e : (fun x => ((gs.take j).foldl
                    (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                    (E x)).getD i false) = G[i - 11] := by
                  rw [Gget (i - 11) hl]
                  funext x
                  rw [L4 _ _ _ j i (by rw [Elen]; omega) (by omega), hW]
                  simp only []
                  congr 1
                  omega
                rw [e]
                apply list_mem
                apply List.mem_append_right
                have h1 : i - 11 < (G.take j).length := by simp; omega
                have h2 : (G.take j)[i - 11] = G[i - 11] := by simp
                rw [← h2]
                exact List.getElem_mem h1
              · have e : (fun x => ((gs.take j).foldl
                    (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                    (E x)).getD i false) = fun _ => false := by
                  funext x
                  exact L5 _ _ _ j i (by rw [Elen]; omega) (by omega)
                rw [e]
                exact List.mem_cons_self
        · intro x
          have h3 := L3 (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) gs (E x) j hj
          rw [Elen] at h3
          rw [hW]
          simp only []
          rw [h3]
    · apply List.mem_cons_of_mem
      have tgt : (fun x : Fin 9 → Bool => (W x).getD o false) ∈ X ++ G := by
        by_cases o10 : o = 9 ∨ o = 10
        · exact List.mem_append_left _ (hout o10)
        · apply List.mem_append_right
          have hl : o - 11 < G.length := by omega
          have e := Gget (o - 11) hl
          have e2 : (fun x : Fin 9 → Bool => (W x).getD (11 + (o - 11)) false) =
              fun x => (W x).getD o false := by
            funext x
            congr 1
            omega
          rw [e2] at e
          rw [← e]
          exact List.getElem_mem hl
      have tm := List.mem_append_right
        ((List.ofFn fun (i : Fin 9) (x : Fin 9 → Bool) => x i) ++ [fun x => x 0 && x 4]) tgt
      convert tm using 1
      funext x
      exact (ev x).symm
  -- the four cases
  by_cases small : gs.length ≤ 12
  · apply core [fun x => (W x).getD 9 false, fun x => (W x).getD 10 false] (by simp; omega)
    · intro n hn
      rcases n with _ | _ | n
      · refine ⟨fun x => x 0, input_mem _ 0, fun x => x 0, input_mem _ 0, Or.inr (Or.inr ?_)⟩
        exact w9
      · have h := or_step [fun x => (W x).getD 9 false]
          (fun _ => by rw [w9]; exact List.mem_cons_self)
        rw [← w10] at h
        exact h
      · simp at hn
    · intro g _ i _ hi
      rcases hi with rfl | rfl <;> simp
    · intro hi
      rcases hi with rfl | rfl <;> simp
  by_cases u10 : (∃ g ∈ gs, 10 ∈ g.inputs) ∨ o = 10
  · by_cases u9 : (∃ g ∈ gs, 9 ∈ g.inputs) ∨ 9 ∈ ops ∨ o = 9
    · obtain ⟨x, hx⟩ := h2 ops hlen ⟨gs, o⟩ fan (by change gs.length = 13; omega) u10 u9
      exact hx (hall x)
    · push_neg at u9
      apply core [fun x => (W x).getD 10 false] (by simp; omega)
      · intro n hn
        rcases n with _ | n
        · have h := or_step [] (fun h => absurd h u9.2.1)
          rw [← w10] at h
          exact h
        · simp at hn
      · intro g hg i hi hix
        rcases hix with rfl | rfl
        · exact absurd hi (u9.1 g hg)
        · simp
      · intro hix
        rcases hix with h | h
        · exact absurd h u9.2.2
        · subst h; simp
  · push_neg at u10
    apply core [fun x => (W x).getD 9 false] (by simp; omega)
    · intro n hn
      rcases n with _ | n
      · refine ⟨fun x => x 0, input_mem _ 0, fun x => x 0, input_mem _ 0, Or.inr (Or.inr ?_)⟩
        exact w9
      · simp at hn
    · intro g hg i hi hix
      rcases hix with rfl | rfl
      · simp
      · exact absurd hi (u10.1 g hg)
    · intro hix
      rcases hix with h | h
      · subst h; simp
      · exact absurd h u10.2
