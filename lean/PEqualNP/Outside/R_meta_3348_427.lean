import Mathlib
import PEqualNP.Defs

-- A degenerate second gate (constant, a copy of an earlier wire, or a repeat of the
-- first gate) is deleted, which gives a circuit one gate smaller and contradicts h1.
-- Otherwise its two inputs are put in increasing order and h2 or h3 applies.
theorem PEqualNP.Outside.R_meta_3348_427
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 < (9 : ℕ) → x5 ≠ (4 : ℕ) → x5 ≠ (6 : ℕ) → x1.gates[(1 : ℕ)]? = Option.some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [x5, (9 : ℕ)]) → (16 : ℕ) ≤ x1.size)
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ) (x6 : ℕ), x5 < x6 → x6 < (9 : ℕ) → ¬(x5 = (4 : ℕ) ∧ x6 = (6 : ℕ)) → x1.gates[(1 : ℕ)]? = Option.some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [x5, x6]) → (16 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  intro C hfan h9 hfun hop
  by_contra hlt
  have hwi : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (y : List Bool), D.wires y =
      D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y :=
    fun _ _ => rfl
  have hcf : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 9 → Bool),
      PEqualNP.MetaComplexity.circuitFun 9 D x =
        (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD D.output false := fun _ _ => rfl
  have hsz : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  have hstab : ∀ (U : List Bool) (v : Bool) (m : ℕ), m ≠ U.length →
      (U ++ [v]).getD m false = U.getD m false := by
    intro U v m hm
    by_cases h : m < U.length
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  have hlast : ∀ (U : List Bool) (v : Bool) (m : ℕ), m = U.length →
      (U ++ [v]).getD m false = v := by
    intro U v m hm
    subst hm
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
    simp
  have hpref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W : List Bool) (k : ℕ),
      k < W.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
        k false = W.getD k false := by
    intro gs
    induction gs with
    | nil =>
      intro W k _
      rfl
    | cons g gs ih =>
      intro W k hk
      simp only [List.foldl_cons]
      rw [ih _ k (by simp; omega)]
      exact hstab W _ k (by omega)
  -- deleting wire 10: an index below 10 stays, index 10 is sent to c, a later index drops by one
  have hsim : ∀ (c : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length + 1 → 10 ≤ W'.length → (c < 10 ∨ W'.length + gs.length < c) →
      (∀ k : ℕ, W'.getD (if k < 10 then k else if k = 10 then c else k - 1) false =
        W.getD k false) →
      ∀ k : ℕ,
        ((gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.Gate.mk g.op
              (g.inputs.map fun i => if i < 10 then i else if i = 10 then c else i - 1)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
            (if k < 10 then k else if k = 10 then c else k - 1) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
          k false := by
    intro c gs
    induction gs with
    | nil =>
      intro W W' _ _ _ hW k
      exact hW k
    | cons g gs ih =>
      intro W W' hl h10 hc hW
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [hl]
      · simp only [List.length_append, List.length_singleton]
        omega
      · rcases hc with hc | hc
        · exact Or.inl hc
        · right
          simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢
          omega
      · have hv : g.op.eval
            ((g.inputs.map fun i => if i < 10 then i else if i = 10 then c else i - 1).map
              fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro k
        rw [hv]
        by_cases hk : k = W.length
        · have e : (if k < 10 then k else if k = 10 then c else k - 1) = W'.length := by
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          rw [e, hlast _ _ _ rfl, hlast _ _ _ hk]
        · have hne : (if k < 10 then k else if k = 10 then c else k - 1) ≠ W'.length := by
            split_ifs <;> omega
          rw [hstab _ _ _ hne, hstab _ _ _ hk]
          exact hW k
  have he1 : ∀ p : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [p] = p := by
    intro p
    cases p <;> rfl
  have he2 : ∀ p q : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [p, q] = (p || q) := by
    intro p q
    cases p <;> cases q <;> rfl
  have e10 : ∀ (x : Fin 9 → Bool) (v : Bool), (List.ofFn x ++ [v]).length = 10 := by
    intro x v
    simp
  have hW10 : ∀ (x : Fin 9 → Bool) (v : Bool) (i : ℕ), 10 ≤ i →
      (List.ofFn x ++ [v]).getD i false = false := by
    intro x v i hi
    apply List.getD_eq_default
    rw [e10]
    exact hi
  have hW9 : ∀ (x : Fin 9 → Bool) (v : Bool), (List.ofFn x ++ [v]).getD 9 false = v := by
    intro x v
    exact hlast _ _ 9 (by simp)
  have hW4 : ∀ (x : Fin 9 → Bool) (v : Bool), (List.ofFn x ++ [v]).getD 4 false = x 4 := by
    intro x v
    rfl
  have hW6 : ∀ (x : Fin 9 → Bool) (v : Bool), (List.ofFn x ++ [v]).getD 6 false = x 6 := by
    intro x v
    rfl
  obtain ⟨gates, out⟩ := C
  rcases gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp at hop
  · simp at hop
  obtain ⟨op1, l⟩ := g1
  have hop1 : op1 = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hop
  subst hop1
  have hlen : l.length ≤ 2 :=
    (hfan (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or l)
      (by simp)).2
  have hsize : rest.length + 2 ≤ 15 := by
    have h := hlt
    rw [hsz] at h
    dsimp only at h
    simp only [List.length_cons] at h
    omega
  have hfin : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, 16 ≤ D.size →
      D.gates.length = rest.length + 2 → False := by
    intro D h hD
    rw [hsz, hD] at h
    omega
  have hv0 : ∀ x : Fin 9 → Bool,
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
    intro x
    have h := h9 x
    rw [hwi] at h
    dsimp only at h
    simp only [List.foldl_cons] at h
    rw [hpref _ _ 9 (by simp), hstab _ _ 9 (by simp), hlast _ _ 9 (by simp)] at h
    exact h
  -- a second gate that only repeats wire c (or is constant false) can be deleted
  have hdeg : ∀ c : ℕ, (c < 10 ∨ c = rest.length + 11) →
      (∀ x : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.or.eval
            (l.map fun i => (List.ofFn x ++ [(x 4 || x 6)]).getD i false) =
          (List.ofFn x ++ [(x 4 || x 6)]).getD c false) → False := by
    intro c hc hcopy
    have hbound := h1
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (g0 :: rest.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
          PEqualNP.CircuitLowerBounds.Gate.mk g.op
            (g.inputs.map fun i => if i < 10 then i else if i = 10 then c else i - 1))
        (if out < 10 then out else if out = 10 then c else out - 1)) ?_ ?_
    · rw [hsz] at hbound
      dsimp only at hbound
      simp only [List.length_cons, List.length_map] at hbound
      omega
    · intro d hd
      dsimp only at hd
      simp only [List.mem_cons, List.mem_map] at hd
      rcases hd with rfl | ⟨d0, hd0, rfl⟩
      · exact hfan _ (by simp)
      · have hd1 := hfan d0 (by simp [hd0])
        exact ⟨hd1.1, by simpa using hd1.2⟩
    · funext x
      have hf := congrFun hfun x
      rw [hcf] at hf
      rw [hcf]
      dsimp only at hf ⊢
      simp only [List.foldl_cons] at hf ⊢
      rw [hv0 x] at hf ⊢
      refine Eq.trans ?_ hf
      apply hsim c rest
      · simp
      · have e := e10 x (x 4 || x 6)
        omega
      · have e := e10 x (x 4 || x 6)
        omega
      · intro k
        by_cases hk : k = 10
        · subst hk
          have e : (if (10 : ℕ) < 10 then 10 else if (10 : ℕ) = 10 then c else 10 - 1) = c := by
            simp
          rw [e, hlast _ _ 10 (by simp)]
          exact (hcopy x).symm
        · rw [hstab (List.ofFn x ++ [(x 4 || x 6)]) _ k (by rw [e10]; exact hk)]
          by_cases hk2 : k < 10
          · rw [if_pos hk2]
          · rw [if_neg hk2, if_neg hk, hW10 x _ (k - 1) (by omega), hW10 x _ k (by omega)]
  -- the two inputs of the second gate can be exchanged
  have hswap : ∀ (a b : ℕ) (y : List Bool),
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (g0 :: PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [b, a]
          :: rest) out).wires y =
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (g0 :: PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [a, b]
          :: rest) out).wires y := by
    intro a b y
    rw [hwi, hwi]
    dsimp only
    simp only [List.foldl_cons, List.map_cons, List.map_nil]
    rw [he2, he2, Bool.or_comm]
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c2, t⟩⟩⟩
  · exact hdeg (rest.length + 11) (Or.inr rfl)
      (fun x => Eq.trans (by rfl) (hW10 x _ _ (by omega)).symm)
  · by_cases ha : a < 10
    · exact hdeg a (Or.inl ha) (fun x => by
        simp only [List.map_cons, List.map_nil]
        rw [he1])
    · exact hdeg (rest.length + 11) (Or.inr rfl) (fun x => by
        simp only [List.map_cons, List.map_nil]
        rw [he1, hW10 x _ a (by omega), hW10 x _ _ (by omega)])
  · by_cases ha : a < 10
    · by_cases hb : b < 10
      · by_cases hab : a = b
        · subst hab
          exact hdeg a (Or.inl ha) (fun x => by
            simp only [List.map_cons, List.map_nil]
            rw [he2, Bool.or_self])
        · by_cases hsp : (a = 4 ∧ b = 6) ∨ (a = 6 ∧ b = 4) ∨ (a = 4 ∧ b = 9) ∨
              (a = 9 ∧ b = 4) ∨ (a = 6 ∧ b = 9) ∨ (a = 9 ∧ b = 6)
          · refine hdeg 9 (Or.inl (by omega)) (fun x => ?_)
            simp only [List.map_cons, List.map_nil]
            rw [he2]
            generalize hp : x 4 = p
            generalize hq : x 6 = q
            rcases hsp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
              ⟨rfl, rfl⟩
            · rw [hW9, hW4, hW6, hp, hq]
            · rw [hW9, hW4, hW6, hp, hq, Bool.or_comm]
            · rw [hW9, hW4, hp]
              cases p <;> cases q <;> rfl
            · rw [hW9, hW4, hp]
              cases p <;> cases q <;> rfl
            · rw [hW9, hW6, hq]
              cases p <;> cases q <;> rfl
            · rw [hW9, hW6, hq]
              cases p <;> cases q <;> rfl
          · have hfan2 : PEqualNP.MetaComplexity.FanInTwo
                (PEqualNP.CircuitLowerBounds.Circuit.mk
                  (g0 :: PEqualNP.CircuitLowerBounds.Gate.mk
                    PEqualNP.CircuitLowerBounds.GateOp.or [b, a] :: rest) out) := by
              intro d hd
              dsimp only at hd
              simp only [List.mem_cons] at hd
              rcases hd with rfl | rfl | hd
              · exact hfan _ (by simp)
              · exact ⟨by simp, by simp⟩
              · exact hfan d (by simp [hd])
            have h92 : ∀ x : Fin 9 → Bool,
                ((PEqualNP.CircuitLowerBounds.Circuit.mk
                  (g0 :: PEqualNP.CircuitLowerBounds.Gate.mk
                    PEqualNP.CircuitLowerBounds.GateOp.or [b, a] :: rest) out).wires
                  (List.ofFn x)).getD 9 false = (x 4 || x 6) := by
              intro x
              rw [hswap a b]
              exact h9 x
            have hfun2 : PEqualNP.MetaComplexity.circuitFun 9
                (PEqualNP.CircuitLowerBounds.Circuit.mk
                  (g0 :: PEqualNP.CircuitLowerBounds.Gate.mk
                    PEqualNP.CircuitLowerBounds.GateOp.or [b, a] :: rest) out) =
                PEqualNP.MetaComplexity.circuitFun 9
                (PEqualNP.CircuitLowerBounds.Circuit.mk
                  (g0 :: PEqualNP.CircuitLowerBounds.Gate.mk
                    PEqualNP.CircuitLowerBounds.GateOp.or [a, b] :: rest) out) := by
              funext x
              unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
              rw [hswap a b]
            by_cases hb9 : b = 9
            · subst hb9
              exact hfin _ (h2 _ hfan h9 hfun a (by omega) (by omega) (by omega) rfl) rfl
            · by_cases ha9 : a = 9
              · subst ha9
                exact hfin _
                  (h2 _ hfan2 h92 (hfun2.trans hfun) b (by omega) (by omega) (by omega) rfl) rfl
              · rcases Nat.lt_or_gt_of_ne hab with hlt2 | hgt
                · exact hfin _ (h3 _ hfan h9 hfun a b hlt2 (by omega) (by omega) rfl) rfl
                · exact hfin _
                    (h3 _ hfan2 h92 (hfun2.trans hfun) b a hgt (by omega) (by omega) rfl) rfl
      · exact hdeg a (Or.inl ha) (fun x => by
          simp only [List.map_cons, List.map_nil]
          rw [he2, hW10 x _ b (by omega), Bool.or_false])
    · by_cases hb : b < 10
      · exact hdeg b (Or.inl hb) (fun x => by
          simp only [List.map_cons, List.map_nil]
          rw [he2, hW10 x _ a (by omega), Bool.false_or])
      · exact hdeg (rest.length + 11) (Or.inr rfl) (fun x => by
          simp only [List.map_cons, List.map_nil]
          rw [he2, hW10 x _ a (by omega), hW10 x _ b (by omega), hW10 x _ _ (by omega),
            Bool.or_false])
  · simp only [List.length_cons] at hlen
    omega
