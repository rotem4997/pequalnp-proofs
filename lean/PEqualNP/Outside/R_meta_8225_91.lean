import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_8225_91
    (repair :
      let I := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let V := fun (C : Circuit) =>
        (∀ i g, C.gates[i]? = some g → (g.op = .and ∨ g.op = .or) ∧
          ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+i ∧ b < 26+i) ∧
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
      let E := fun (C : Circuit) (j : ℕ) (p l : Fin 13) =>
        I p l ∧ Owns 26 C j (Fin.castAdd 13 p) (Fin.natAdd 13 l)
      let A := fun (C : Circuit) (j : ℕ) =>
        ∀ p l q m, E C j p l → E C j q m → p = q ∨ l = m
      ∀ C, V C → ∀ j < C.size, (∀ i < j, A C i) → ¬ A C j →
        ∃ D, V D ∧ D.size ≤ C.size ∧ ∀ i ≤ j, A D i)
    (ownership :
      let I := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let V := fun (C : Circuit) =>
        (∀ i g, C.gates[i]? = some g → (g.op = .and ∨ g.op = .or) ∧
          ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+i ∧ b < 26+i) ∧
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
      ∀ C, V C → ∀ p l, I p l →
        ∃ j < C.gates.length, Owns 26 C j (Fin.castAdd 13 p) (Fin.natAdd 13 l)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) ∧ x4.size ≤ x1.size ∧ ∃ (x5 : SimpleGraph (Fin (26 : ℕ))), x5 = PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x6 : Fin (13 : ℕ)) => List.map (fun (x7 : Fin (13 : ℕ)) => (↑x6, (13 : ℕ) + ↑x7)) (List.filter (fun (x7 : Fin (13 : ℕ)) => Decidable.decide (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)))) (List.finRange (13 : ℕ)))) (List.finRange (13 : ℕ))) ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x5 x4 ∧ PEqualNP.EdgeOwnership.EveryEdgeOwned (26 : ℕ) x5 x4 := by
  intro source legal computes
  classical
  let I := fun (p l : Fin 13) => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let V := fun (C : Circuit) =>
    (∀ i g, C.gates[i]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+i ∧ b < 26+i) ∧
    (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  let E := fun (C : Circuit) (j : ℕ) (p l : Fin 13) =>
    I p l ∧ Owns 26 C j (Fin.castAdd 13 p) (Fin.natAdd 13 l)
  let A := fun (C : Circuit) (j : ℕ) =>
    ∀ p l q m, E C j p l → E C j q m → p = q ∨ l = m
  have step : ∀ C, V C → ∀ j < C.size, (∀ i < j, A C i) → ¬ A C j →
      ∃ D, V D ∧ D.size ≤ C.size ∧ ∀ i ≤ j, A D i := repair
  have buildPrefix : ∀ k : ℕ, ∃ D, V D ∧ D.size ≤ source.size ∧ ∀ i < k, A D i := by
    intro k
    induction k with
    | zero => exact ⟨source, ⟨legal, computes⟩, le_rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
    | succ k ih =>
      obtain ⟨C, cv, cs, pre⟩ := ih
      by_cases a : A C k
      · refine ⟨C, cv, cs, ?_⟩
        intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
        · exact pre i h
        · exact a
      · have bound : k < C.size := by
          by_contra h
          apply a
          intro p l q m ep _
          exact (h ep.2.1).elim
        obtain ⟨D, dv, ds, fixed⟩ := step C cv k bound pre a
        exact ⟨D, dv, ds.trans cs, fun i h => fixed i (Nat.le_of_lt_succ h)⟩
  obtain ⟨D, dv, ds, stable⟩ := buildPrefix source.size
  let pairs := (List.finRange 13).flatMap fun p =>
    (((List.finRange 13).filter fun l => decide (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)).map
      fun l => (p.val, 13+l.val))
  let G := edgeGraph 26 pairs
  refine ⟨D, dv.1, dv.2, ds, G, rfl, ?_, ?_⟩
  all_goals
    have orient (u v : Fin 26) (adj : G.Adj u v) :
        ∃ p l, I p l ∧ ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
          (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) := by
      have direct (a b : Fin 26) (hp : (a.val,b.val) ∈ pairs) :
          ∃ p l, I p l ∧ a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l := by
        obtain ⟨p, _, hm⟩ := List.mem_flatMap.mp hp
        obtain ⟨l, hf, eq⟩ := List.mem_map.mp hm
        have hl := (List.mem_filter.mp hf).2
        exact ⟨p, l, of_decide_eq_true hl, Fin.ext (congrArg Prod.fst eq).symm,
          Fin.ext (congrArg Prod.snd eq).symm⟩
      rcases adj.2 with h | h
      · obtain ⟨p,l,ip,eq⟩ := direct u v h
        exact ⟨p,l,ip,Or.inl eq⟩
      · obtain ⟨p,l,ip,eq⟩ := direct v u h
        exact ⟨p,l,ip,Or.inr eq⟩
    have swap (j : ℕ) (u v : Fin 26) (ow : Owns 26 D j u v) : Owns 26 D j v u := by
      have e : pairInput v u = pairInput u v := by
        funext t
        change decide (t = v ∨ t = u) = decide (t = u ∨ t = v)
        simp only [or_comm (a := t = v) (b := t = u)]
      unfold Owns at *
      rwa [e]
  · intro j hj _
    right
    have noMatch := stable j (lt_of_lt_of_le hj ds)
    have center : (∃ a, ∀ p l, E D j p l → p = a) ∨
        (∃ b, ∀ p l, E D j p l → l = b) := by
      by_cases any : ∃ p l, E D j p l
      · obtain ⟨a,b,ab⟩ := any
        by_cases left : ∀ p l, E D j p l → p = a
        · exact Or.inl ⟨a,left⟩
        · push Not at left
          obtain ⟨c,d,cd,ca⟩ := left
          have db := (noMatch c d a b cd ab).resolve_left ca
          subst d
          refine Or.inr ⟨b, ?_⟩
          intro p l pl
          by_contra ne
          exact ca (((noMatch p l c b pl cd).resolve_right ne).symm.trans
            ((noMatch p l a b pl ab).resolve_right ne))
      · exact Or.inl ⟨0, fun p l pl => (any ⟨p,l,pl⟩).elim⟩
    rcases center with ⟨a,h⟩ | ⟨b,h⟩
    · refine ⟨Fin.castAdd 13 a, ?_⟩
      intro u v adj ow
      obtain ⟨p,l,ip,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := orient u v adj
      · exact Or.inl (congrArg (Fin.castAdd 13) (h p l ⟨ip,ow⟩))
      · exact Or.inr (congrArg (Fin.castAdd 13) (h p l ⟨ip,swap j _ _ ow⟩))
    · refine ⟨Fin.natAdd 13 b, ?_⟩
      intro u v adj ow
      obtain ⟨p,l,ip,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := orient u v adj
      · exact Or.inr (congrArg (Fin.natAdd 13) (h p l ⟨ip,ow⟩))
      · exact Or.inl (congrArg (Fin.natAdd 13) (h p l ⟨ip,swap j _ _ ow⟩))
  · intro u v adj
    obtain ⟨p,l,ip,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := orient u v adj
    · exact ownership D dv p l ip
    · obtain ⟨j,hj,ow⟩ := ownership D dv p l ip
      exact ⟨j,hj,swap j _ _ ow⟩
