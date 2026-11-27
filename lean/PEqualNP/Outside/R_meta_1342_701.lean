import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1342_701
    (basis : let E := ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (Fin 11 × Fin 11)); let B := ([15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546] : List ℕ); ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → (∀ p ∈ E, D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput p.1 p.2)) = true) → (∀ m ∈ B, D.eval (List.ofFn (fun i : Fin 11 => m.testBit i.val)) = false) → PEqualNP.MetaComplexity.circuitFun 11 D = (fun x : Fin 11 → Bool => E.any (fun p => x p.1 && x p.2)))
    (finite_witness : let E := ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (Fin 11 × Fin 11)); let B := ([15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546] : List ℕ); ∃ (t : Fin 22) (ops : Fin t → Bool) (src : Fin t → Option (Fin 33) × Option (Fin 33)) (out : Fin 33), let D := ({ gates := List.ofFn (fun i : Fin t => { op := if ops i then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := ((src i).1.toList ++ (src i).2.toList).map Fin.val }), output := out.val } : PEqualNP.CircuitLowerBounds.Circuit); (∀ p ∈ E, D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput p.1 p.2)) = true) ∧ (∀ m ∈ B, D.eval (List.ofFn (fun i : Fin 11 => m.testBit i.val)) = false) ∧ 3 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 (E.map (fun p => (p.1.val,p.2.val)))) D).card) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  obtain ⟨t, ops, src, out, hp, hn, _⟩ := finite_witness
  let D := ({ gates := List.ofFn (fun i : Fin t => { op := if ops i then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := ((src i).1.toList ++ (src i).2.toList).map Fin.val }), output := out.val } : PEqualNP.CircuitLowerBounds.Circuit)
  have hm : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    constructor
    · cases hi : ops i <;> simp [hi]
    · simp only [List.length_map, List.length_append]
      cases ha : (src i).1 <;> cases hb : (src i).2 <;> simp [ha, hb]
  have hsem := basis D hm hp hn
  have hsize : D.size ≤ 21 := by
    have ht := t.isLt
    change (List.ofFn _).length ≤ 21
    rw [List.length_ofFn]
    omega
  have edges_match : ∀ u v : Fin 11, (u,v) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (Fin 11 × Fin 11)) ↔ (u.val,v.val) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) := by
    decide +kernel
  refine ⟨D, hm, ?_, hsize⟩
  intro x
  change PEqualNP.MetaComplexity.circuitFun 11 D x = true ↔ _
  rw [hsem]
  simp only [List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨p, hp, hu, hv⟩
    exact ⟨p.1,p.2,(edges_match p.1 p.2).mp hp,hu,hv⟩
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨(u,v),(edges_match u v).mpr he,hu,hv⟩
