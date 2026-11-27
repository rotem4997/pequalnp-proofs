import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8059_1
    (t1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
      (∀ (p l : Fin (13 : ℕ)), p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ)) →
        C.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = p)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = l)) = Bool.true) →
      (∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) →
        (∀ (l : Fin (13 : ℕ)), {q ∈ Q | q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) →
        C.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ Q)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ))))) = Bool.false) →
      (64 : ℕ) ≤ C.size)
    (t2 : ∀ (p l : Fin (13 : ℕ)),
      (p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ))) ↔
      p ∈ PEqualNP.HeptadCover.singerLines3 l)
    (t3 : ∀ (Q : Finset (Fin (13 : ℕ))) (l : Fin (13 : ℕ)),
      l ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q ↔
      ∀ q ∈ Q, ¬(q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ)))) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),   have x6 : ℕ := (25 : ℕ) + x4.size;   PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → (26 : ℕ) ≤ x5 → x5 < x6 → (∀ (x11 x12 : Fin (13 : ℕ)), x11 ∈ x1 x12 → x3 x4 x5 (x2 {x11} {x12}) = Bool.true ∨ x3 x4 x6 (x2 {x11} {x12}) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x12 → (x3 x4 x5 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12)) || x3 x4 x6 (x2 x12 (PEqualNP.HeptadCover.missLines x1 x12))) = Bool.false) → (∀ (x13 : Bool), ∃ (x14 : Fin (13 : ℕ)) (x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 ∧ x3 x4 x5 (x2 {x14} {x15}) = x13 ∧ x3 x4 x6 (x2 {x14} {x15}) = !x13) → {x14 : ℕ | x14 < x4.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).inputs, (26 : ℕ) ≤ x15 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (x15 - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and}.encard ≤ (1 : ℕ∞) → (63 : ℕ) ≤ x4.size := by
  intro x1v x2v x3v C k x6v hM hRB h26 hk6 hpos hquad hcomp hnest
  have hx6 : x6v = (25 : ℕ) + C.size := rfl
  have hsz : C.size = C.gates.length := rfl
  rw [hx6] at hk6
  set g0 : PEqualNP.CircuitLowerBounds.Gate :=
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [k, x6v] } with hg0
  set C' : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates ++ [g0], output := (26 : ℕ) + C.size } with hC'
  -- generic length of the wire fold
  have hgen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (M : List Bool),
      ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) M).length) =
      M.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro M; simp
    | cons g gs' ih =>
        intro M
        rw [List.foldl_cons, ih]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
  have hwlen : ∀ L : List Bool, (C.wires L).length = L.length + C.gates.length := by
    intro L
    have h2 : C.wires L = C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) L := rfl
    rw [h2, hgen]
  have hx3eq : ∀ (CC : PEqualNP.CircuitLowerBounds.Circuit) (kk : ℕ) (L : List Bool),
      x3v CC kk L = (CC.wires L).getD kk Bool.false := fun _ _ _ => rfl
  have hor2 : ∀ (a b : Bool),
      PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or [a, b] = (a || b) := by
    intro a b
    cases a <;> cases b <;> rfl
  have hx2len : ∀ (A B : Finset (Fin (13 : ℕ))), (x2v A B).length = (26 : ℕ) := by
    intro A B
    have h3 : (x2v A B).length = ((List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ A)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ B)).length := rfl
    rw [h3, List.length_append, List.length_ofFn, List.length_ofFn]
  have hC'len : C'.gates.length = C.gates.length + 1 := by
    show (C.gates ++ [g0]).length = C.gates.length + 1
    rw [List.length_append, List.length_singleton]
  -- the wires of C'
  have hw : ∀ L : List Bool, C'.wires L = C.wires L ++
      [((C.wires L).getD k Bool.false) || ((C.wires L).getD x6v Bool.false)] := by
    intro L
    have h1 : C'.wires L = (C.gates ++ [g0]).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) L := rfl
    have h2 : C.gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) L = C.wires L := rfl
    rw [h1, List.foldl_append, h2, List.foldl_cons, List.foldl_nil, hg0]
    show C.wires L ++ [PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or
      [((C.wires L).getD k Bool.false), ((C.wires L).getD x6v Bool.false)]] = _
    rw [hor2]
  -- eval of C' at a 26-bit input is the OR of the two output-wire values of C
  have hev : ∀ L : List Bool, L.length = (26 : ℕ) →
      C'.eval L = (((C.wires L).getD k Bool.false) || ((C.wires L).getD x6v Bool.false)) := by
    intro L hL26
    have he : C'.eval L = (C'.wires L).getD ((26 : ℕ) + C.size) Bool.false := rfl
    have hidx : ((26 : ℕ) + C.size) = (C.wires L).length := by
      rw [hwlen L, hL26, hsz]
    rw [he, hw L, hidx, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
    rfl
  -- Monotone2 C'
  have hM' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hM g h
    · have hg0' : g = g0 := by simpa using h
      subst hg0'
      refine ⟨Or.inr rfl, ?_⟩
      rfl
  -- ReadsBack 26 C'
  have hRB' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C' := by
    intro j hj
    rcases Nat.lt_or_ge j C.gates.length with hlt | hge
    · have hgt : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
        PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        show (C.gates ++ [g0]).getD j _ = C.gates.getD j _
        exact List.getD_append _ _ _ _ hlt
      intro i hi
      rw [hgt] at hi
      exact hRB j hlt i hi
    · have hj' : j = C.gates.length := by omega
      subst hj'
      intro i hi
      have hgt : PEqualNP.MetaComplexity.NestedCover.gateAt C' C.gates.length = g0 := by
        show (C.gates ++ [g0]).getD C.gates.length _ = g0
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [hgt, hg0] at hi
      rcases List.mem_cons.mp hi with rfl | hi'
      · omega
      · have hix : i = x6v := by simpa using hi'
        subst hix
        omega
  -- positive spec transfer
  have hpos' : ∀ (p l : Fin (13 : ℕ)), p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ)) →
      C'.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = p)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = l)) = Bool.true := by
    intro p l hpl
    have hin : p ∈ x1v l := (t2 p l).mp hpl
    have hL : ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = p)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = l)) = x2v {p} {l} := by
      have h1 : (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = p)) =
          (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ ({p} : Finset (Fin (13 : ℕ))))) := by
        congr 1; funext x; simp
      have h2 : (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x = l)) =
          (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ ({l} : Finset (Fin (13 : ℕ))))) := by
        congr 1; funext x; simp
      rw [h1, h2]
    rw [hL, hev _ (hx2len {p} {l})]
    rcases hpos p l hin with h | h
    · simp only [hx3eq] at h; rw [h, Bool.true_or]
    · simp only [hx3eq] at h; rw [h, Bool.or_true]
  -- quadrangle spec transfer
  have hquad' : ∀ (Q : Finset (Fin (13 : ℕ))), Q.card = (4 : ℕ) →
      (∀ (l : Fin (13 : ℕ)), {q ∈ Q | q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) →
      C'.eval ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ Q)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ))))) = Bool.false := by
    intro Q hcard hper
    have hq : PEqualNP.HeptadCover.IsQuadrangle x1v Q := by
      refine ⟨hcard, ?_⟩
      intro l
      have hset : Q ∩ x1v l =
          {q ∈ Q | q - l = (0 : Fin (13 : ℕ)) ∨ q - l = (1 : Fin (13 : ℕ)) ∨ q - l = (3 : Fin (13 : ℕ)) ∨ q - l = (9 : Fin (13 : ℕ))} := by
        ext q
        simp only [Finset.mem_inter, Finset.mem_filter]
        rw [← t2 q l]
      rw [hset]
      exact hper l
    have hor := hquad Q hq
    have hL : ((List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ Q)) ++ List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ))))) = x2v Q (PEqualNP.HeptadCover.missLines x1v Q) := by
      have h2 : (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (∀ q ∈ Q, ¬(q - x = (0 : Fin (13 : ℕ)) ∨ q - x = (1 : Fin (13 : ℕ)) ∨ q - x = (3 : Fin (13 : ℕ)) ∨ q - x = (9 : Fin (13 : ℕ))))) =
          (List.ofFn fun (x : Fin (13 : ℕ)) => Decidable.decide (x ∈ PEqualNP.HeptadCover.missLines x1v Q)) := by
        congr 1; funext x
        exact decide_eq_decide.mpr (t3 Q x).symm
      rw [h2]
    rw [hL, hev _ (hx2len Q _)]
    simp only [hx3eq] at hor
    rw [Bool.or_eq_false_iff] at hor
    obtain ⟨h, h'⟩ := hor
    rw [h, h', Bool.false_or]
  -- apply the child
  have h64 := t1 C' hM' hRB' hpos' hquad'
  have hC'sz : C'.size = C.size + 1 := by
    show (C.gates ++ [g0]).length = C.gates.length + 1
    rw [List.length_append, List.length_singleton]
  omega