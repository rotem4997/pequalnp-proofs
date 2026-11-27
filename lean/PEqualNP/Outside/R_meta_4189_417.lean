import PEqualNP.Defs

-- The first claim collects each AND-only part into a conjunction of available columns.
-- Only the OR gates introduce new columns, leaving a finite search on the boundary inputs.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4189_417
    (normalize : ∀ (k : ℕ) (base : List (BitVec k)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      have meet : List (BitVec k) → List ℕ → BitVec k := fun w is =>
        is.foldr (fun i a => w.getD i 0 &&& a) (~~~ (0 : BitVec k));
      ∃ zs : List (BitVec k), zs.length = C.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op false true false (fun _ : ℕ => false) false) ∧
        (∀ j : Fin zs.length,
          have bank : List (BitVec k) := (0 : BitVec k) :: base ++ zs.take j.val;
          ∃ a b : List ℕ, (∀ i ∈ a ++ b, i < bank.length) ∧
            zs.get j = meet bank a ||| meet bank b) ∧
        ∃ a : List ℕ, (∀ i ∈ a, i < ((0 : BitVec k) :: base ++ zs).length) ∧
          ∀ r : Fin k, (meet ((0 : BitVec k) :: base ++ zs) a).getLsbD r.val =
            C.eval (base.map fun v => v.getLsbD r.val))
    (bound : have base : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239];
      have meet : List (BitVec 58) → List ℕ → BitVec 58 := fun w is =>
        is.foldr (fun i a => w.getD i 0 &&& a) (~~~ (0 : BitVec 58));
      ∀ zs : List (BitVec 58), (∀ j : Fin zs.length,
          have bank : List (BitVec 58) := (0 : BitVec 58) :: base ++ zs.take j.val;
          ∃ a b : List ℕ, (∀ i ∈ a ++ b, i < bank.length) ∧
            zs.get j = meet bank a ||| meet bank b) →
        (∃ a : List ℕ, (∀ i ∈ a, i < ((0 : BitVec 58) :: base ++ zs).length) ∧
          meet ((0 : BitVec 58) :: base ++ zs) a = (2097151 : BitVec 58)) →
        19 ≤ zs.length) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 (1 : Fin (14 : ℕ))]]) = Bool.true ↔ x2 x6)) → (19 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x7.op Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false) x4.gates := by
  intro fixedEdges fixedAccept fixedBoundary C hmono heval

  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let accept : (Fin 14 → Bool) → Prop := fun x =>
    ∃ p l : Fin 14, (p.val, l.val) ∈ edges ∧ x p = true ∧ x l = true
  let boundary : (Fin 14 → Bool) → Prop := fun x =>
    (accept x ∧ ∀ i, x i = true → ¬ accept (Function.update x i false)) ∨
      ¬ accept x ∧ ∀ i, x i = false → accept (Function.update x i true)
  let base : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 95274182876594239]
  let input (r : Fin 58) (i : Fin 14) : Bool := (base.getD i.val 0).getLsbD r.val
  have packed : ∀ r : Fin 58,
      (base.map fun x => x.getLsbD r.val) =
        List.ofFn (input r) ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [input r 0, input r 1]] := by
    dsimp [base, input]
    decide +kernel
  let acceptB (x : Fin 14 → Bool) : Bool := edges.any fun e =>
    x (Fin.ofNat 14 e.1) && x (Fin.ofNat 14 e.2)
  have edges_lt : ∀ e ∈ edges, e.1 < 14 ∧ e.2 < 14 := by
    dsimp [edges]
    decide +kernel
  have accept_spec (x : Fin 14 → Bool) : acceptB x = true ↔ accept x := by
    simp only [acceptB, accept, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨p,l⟩, he, hp, hl⟩
      have hh := edges_lt (p,l) he
      refine ⟨Fin.ofNat 14 p, Fin.ofNat 14 l, ?_, hp, hl⟩
      simpa [Fin.ofNat, Nat.mod_eq_of_lt hh.1, Nat.mod_eq_of_lt hh.2] using he
    · rintro ⟨p,l,he,hp,hl⟩
      refine ⟨(p.val,l.val), he, ?_, ?_⟩
      · have ep : Fin.ofNat 14 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
        exact ep.symm ▸ hp
      · have el : Fin.ofNat 14 l.val = l := Fin.ext (Nat.mod_eq_of_lt l.isLt)
        exact el.symm ▸ hl
  have checked : ∀ r : Fin 58, acceptB (input r) = (2097151 : BitVec 58).getLsbD r.val ∧
      (List.finRange 14).all (fun i =>
        if acceptB (input r) then !input r i || !(acceptB (Function.update (input r) i false))
        else input r i || acceptB (Function.update (input r) i true)) = true := by
    dsimp [acceptB, input, base, edges]
    decide +kernel
  have rows : ∀ r : Fin 58,
      boundary (input r) ∧ (accept (input r) ↔ (2097151 : BitVec 58).getLsbD r.val = true) := by
    intro r
    obtain ⟨heq, hchecks⟩ := checked r
    refine ⟨?_, ?_⟩
    · have hat (i : Fin 14) := List.all_eq_true.mp hchecks i (by simp)
      cases hv : acceptB (input r) with
      | false =>
        right
        refine ⟨fun h => by simpa [hv] using (accept_spec _).mpr h, ?_⟩
        intro i hi
        exact (accept_spec _).mp (by simpa [hv, hi] using hat i)
      | true =>
        left
        refine ⟨(accept_spec _).mp hv, ?_⟩
        intro i hi hbad
        have hgood := (accept_spec _).mpr hbad
        simpa [hv, hi, hgood] using hat i
    · rw [← accept_spec, heq]
  obtain ⟨zs, hcount, hsteps, out, hout, houtput⟩ := normalize 58 base C hmono
  have heq :
      out.foldr (fun i a => ((0 : BitVec 58) :: base ++ zs).getD i 0 &&& a)
        (~~~ (0 : BitVec 58)) = (2097151 : BitVec 58) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 58 := ⟨i, hi⟩
    change _ = (2097151 : BitVec 58).getLsbD r.val
    rw [houtput r, packed r]
    apply Bool.eq_iff_iff.mpr
    exact (heval (input r) (rows r).1).trans (rows r).2
  have hc : 19 ≤ zs.length := bound zs hsteps ⟨out, hout, heq⟩
  exact hcount ▸ hc
