import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1342_677
    (compile : ∀ (B : Circuit) (T : List (ℕ × ℕ)), IsAO2 11 B → T ≠ [] →
      (∀ e ∈ T, e.1 < 11 + B.size ∧ e.2 < 11 + B.size) →
      ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = B.size + 2 * T.length ∧
        (∀ x : Fin 11 → Bool, D.eval (List.ofFn x) = T.any (fun e =>
          BlindGate.wireValue B 11 x e.1 && BlindGate.wireValue B 11 x e.2)) ∧
        (∀ x y : Fin 11 → Bool, (∀ i, x i = true → y i = true) →
          D.eval (List.ofFn x) = true → D.eval (List.ofFn y) = true))
    (boundary : ∃ (B : Circuit) (T : List (ℕ × ℕ)),
      let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
      let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let v := fun (r w : ℕ) => BlindGate.wireValue B 11 (fun i => r.testBit i.val) w
      IsAO2 11 B ∧ T ≠ [] ∧ B.size + 2 * T.length ≤ 22 ∧ 3 ≤ ReadTwo.nAnd B ∧
      (∀ e ∈ T, e.1 < 11 + B.size ∧ e.2 < 11 + B.size) ∧
      (∀ j < B.size, (P.any fun r => v r (11+j)) = true ∧ (Q.any fun r => v r (11+j)) = true) ∧
      (∀ j < B.size, ReadTwo.isAnd B j → ∃ e ∈ T, ∃ w ∈ [e.1,e.2],
        w = 11+j ∨ (11 ≤ w ∧ EdgeOwnership.InCone 11 B j (w-11))) ∧
      (∀ r ∈ P ++ Q, (T.any fun e => v r e.1 && v r e.2) = decide (r ∈ P))) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let row (r : ℕ) (i : Fin 11) := r.testBit i.val
  let edge (x : Fin 11 → Bool) :=
    E.any fun e => x (Fin.ofNat 11 e.1) && x (Fin.ofNat 11 e.2)
  let leRow (x y : Fin 11 → Bool) :=
    (List.finRange 11).all (fun i => !x i || y i)
  have leRow_imp (x y : Fin 11 → Bool) (h : leRow x y = true) :
      ∀ i, x i = true → y i = true := by
    intro i hxi
    have hi := List.all_eq_true.mp h i (List.mem_finRange i)
    simpa [hxi] using hi
  have cover : ∀ x : Fin 11 → Bool,
      (P.any (fun r => leRow (row r) x) = edge x) ∧
      (Q.any (fun r => leRow x (row r)) = !edge x) := by
    decide +kernel
  have edge_spec (x : Fin 11 → Bool) :
      edge x = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true := by
    dsimp only [edge]
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨a,b⟩, hab, ha, hb⟩
      have bounds : ∀ e ∈ E, e.1 < 11 ∧ e.2 < 11 := by decide
      obtain ⟨ba,bb⟩ := bounds (a,b) hab
      refine ⟨Fin.ofNat 11 a, Fin.ofNat 11 b, ?_, ha, hb⟩
      change (a % 11,b % 11) ∈ E
      rwa [Nat.mod_eq_of_lt ba, Nat.mod_eq_of_lt bb]
    · rintro ⟨u,v,hm,hu,hv⟩
      refine ⟨(u.val,v.val), hm, ?_, ?_⟩
      · convert hu using 2
        exact Fin.ext (Nat.mod_eq_of_lt u.isLt)
      · convert hv using 2
        exact Fin.ext (Nat.mod_eq_of_lt v.isLt)
  obtain ⟨B,T,hB,ne,budget,_,pins,_,_,tests⟩ := boundary
  obtain ⟨C,model,size,eval,mono⟩ := compile B T hB ne pins
  have exact_test (r : ℕ) (hr : r ∈ P ++ Q) :
      C.eval (List.ofFn (row r)) = decide (r ∈ P) := (eval _).trans (tests r hr)
  have disjoint : ∀ r ∈ Q, r ∉ P := by decide
  refine ⟨C,model,?_,by omega⟩
  intro x
  change C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true
  rw [← edge_spec]
  constructor
  · intro hx
    by_cases he : edge x = true
    · exact he
    · have he0 : edge x = false := Bool.eq_false_of_not_eq_true he
      have nq : Q.any (fun r => leRow x (row r)) = true := by rw [(cover x).2, he0]; rfl
      obtain ⟨r,hr,hle⟩ := List.any_eq_true.mp nq
      have neg : C.eval (List.ofFn (row r)) = false := by
        rw [exact_test r (List.mem_append.mpr (Or.inr hr)), decide_eq_false (disjoint r hr)]
      exact (Bool.false_ne_true (neg.symm.trans (mono x (row r) (leRow_imp _ _ hle) hx))).elim
  · intro hx
    have np : P.any (fun r => leRow (row r) x) = true := (cover x).1.trans hx
    obtain ⟨r,hr,hle⟩ := List.any_eq_true.mp np
    have pos : C.eval (List.ofFn (row r)) = true := by
      rw [exact_test r (List.mem_append.mpr (Or.inl hr)), decide_eq_true hr]
    exact mono (row r) x (leRow_imp _ _ hle) pos
