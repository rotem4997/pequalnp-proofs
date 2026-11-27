import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2636_517
    (restrict : ∀ (n : ℕ) (f : (Fin (n+1) → Bool) → Bool) (p : Fin (n+1)) (b : Bool) (s : ℕ),
      (∃ x : Fin (n+1) → Bool, f (Function.update x p (!x p)) ≠ f x) →
      (∃ x y : Fin (n+1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) →
      HasCircuitSize (n+1) f (s+1) →
      HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s)
    (extend : ∀ (n : ℕ) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) (s : ℕ),
      HasCircuitSize n f s →
      HasCircuitSize n (fun x => f x || decide (∃ a ∈ A, x a = true)) (s + A.card))
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool, f x = true ↔ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s : ℕ, HasCircuitSize n f s →
      ∃ v : Fin n, (G.neighborSet v).ncard = 3 ∧ ∃ t : ℕ, t + 4 ≤ s ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) t) :∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → (∀ (x9 : Fin x1 → Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 → ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 → Bool) => x4 (Function.update x14 x12 Bool.false)) x13 := by
  classical
  intro n G A f degree girth isolated edges computes s has
  cases n with
  | zero =>
    obtain ⟨i, _, _⟩ := edges
    exact Fin.elim0 i
  | succ n =>
    let pureEdge : (Fin (n+1) → Bool) → Bool := fun x =>
      @decide (∃ i j : Fin (n+1), G.Adj i j ∧ x i = true ∧ x j = true)
        (Classical.propDecidable _)
    have pureSpec (x : Fin (n+1) → Bool) :
        pureEdge x = true ↔ ∃ i j : Fin (n+1), G.Adj i j ∧ x i = true ∧ x j = true :=
      @decide_eq_true_iff _ (Classical.propDecidable _)
    have noDegree (v : Fin (n+1)) (hv : v ∈ A) : (G.neighborSet v).ncard = 0 := by
      have empty : G.neighborSet v = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun w hw => isolated v w hw hv)
      simp [empty]
    have cubic (v : Fin (n+1)) :
        (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
      by_cases h : v ∈ A
      · exact Or.inl (noDegree v h)
      · exact Or.inr (degree v h)
    have strip (S : Finset (Fin (n+1))) : S ⊆ A →
        ∀ (F : (Fin (n+1) → Bool) → Bool) (t : ℕ),
        (∀ x : Fin (n+1) → Bool, F x = true ↔
          (∃ a ∈ S, x a = true) ∨ ∃ i j : Fin (n+1), G.Adj i j ∧ x i = true ∧ x j = true) →
        HasCircuitSize (n+1) F t → ∃ r : ℕ, r + S.card ≤ t ∧ HasCircuitSize (n+1) pureEdge r := by
      induction S using Finset.induction_on with
      | empty =>
        intro _ F t hF hsize
        have eq : F = pureEdge := by
          funext x
          apply Bool.eq_iff_iff.mpr
          rw [pureSpec]
          simpa using hF x
        exact ⟨t, by simp, eq ▸ hsize⟩
      | @insert p S hp ih =>
        intro sub F t hF hsize
        have pA : p ∈ A := sub (Finset.mem_insert_self p S)
        have sA : S ⊆ A := fun q hq => sub (Finset.mem_insert_of_mem hq)
        let Z : Fin (n+1) → Bool := fun _ => false
        let O : Fin (n+1) → Bool := fun _ => true
        have zero : F Z = false := by
          cases h : F Z with
          | false => rfl
          | true => exact False.elim (by simpa [Z] using (hF Z).mp h)
        have one : F (Function.update Z p (!Z p)) = true := by
          apply (hF _).mpr
          exact Or.inl ⟨p, Finset.mem_insert_self p S, by simp [Z]⟩
        have zeroUpdate : Function.update Z p false = Z := by
          funext i
          by_cases h : i = p <;> simp [Function.update, h, Z]
        obtain ⟨i,j,hij⟩ := edges
        have hip : i ≠ p := fun e => isolated i j hij (e ▸ pA)
        have hjp : j ≠ p := fun e => isolated j i hij.symm (e ▸ pA)
        have oneUpdate : F (Function.update O p false) = true := by
          apply (hF _).mpr
          exact Or.inr ⟨i, j, hij, by simp [Function.update_of_ne hip, O],
            by simp [Function.update_of_ne hjp, O]⟩
        have tpos : 0 < t := by
          obtain ⟨C, fan, small, eval⟩ := hsize
          by_contra hn
          have nil : C.gates = [] := List.eq_nil_of_length_eq_zero (by
            change C.gates.length ≤ t at small
            omega)
          have read (x : Fin (n+1) → Bool) :
              F x = (List.ofFn x).getD C.output false := by
            rw [← eval x]
            change (C.gates.foldl (fun w g =>
              w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
              (List.ofFn x)).getD C.output false = _
            rw [nil]
            rfl
          have out : C.output = p.val := by
            have h := read (Function.update Z p (!Z p))
            rw [one] at h
            by_cases hlt : C.output < n+1
            · have hx : (⟨C.output,hlt⟩ : Fin (n+1)) = p := by
                by_contra hne
                have hd : (List.ofFn (Function.update Z p (!Z p))).getD C.output false =
                    false := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt)]
                  simp only [Option.getD_some, List.getElem_ofFn]
                  exact Function.update_of_ne (show (⟨C.output,hlt⟩ : Fin (n+1)) ≠ p from hne) _ _
                rw [hd] at h
                contradiction
              exact congrArg Fin.val hx
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)] at h
              contradiction
          have h := read (Function.update O p false)
          rw [oneUpdate, out, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simpa using p.isLt)] at h
          simp only [Option.getD_some, List.getElem_ofFn, Fin.eta, Function.update_self] at h
          exact Bool.noConfusion h
        obtain ⟨u,rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        have smaller := restrict n F p false u ⟨Z, by simp [one, zero]⟩
          ⟨Z, O, by rw [zeroUpdate, zero, oneUpdate]; decide⟩ hsize
        have hsmall (x : Fin (n+1) → Bool) :
            F (Function.update x p false) = true ↔ (∃ a ∈ S, x a = true) ∨
              ∃ i j : Fin (n+1), G.Adj i j ∧ x i = true ∧ x j = true := by
          rw [hF]
          constructor
          · rintro (⟨a, ha, hax⟩ | ⟨v,w,hvw,hvx,hwx⟩)
            · rcases Finset.mem_insert.mp ha with rfl | ha
              · simp at hax
              · have hap : a ≠ p := fun e => hp (e ▸ ha)
                exact Or.inl ⟨a,ha,by simpa [Function.update_of_ne hap] using hax⟩
            · have hvp : v ≠ p := fun e => isolated v w hvw (e ▸ pA)
              have hwp : w ≠ p := fun e => isolated w v hvw.symm (e ▸ pA)
              exact Or.inr ⟨v,w,hvw,by simpa [Function.update_of_ne hvp] using hvx,
                by simpa [Function.update_of_ne hwp] using hwx⟩
          · rintro (⟨a,ha,hax⟩ | ⟨v,w,hvw,hvx,hwx⟩)
            · have hap : a ≠ p := fun e => hp (e ▸ ha)
              exact Or.inl ⟨a,Finset.mem_insert_of_mem ha,by simpa [Function.update_of_ne hap] using hax⟩
            · have hvp : v ≠ p := fun e => isolated v w hvw (e ▸ pA)
              have hwp : w ≠ p := fun e => isolated w v hvw.symm (e ▸ pA)
              exact Or.inr ⟨v,w,hvw,by simpa [Function.update_of_ne hvp] using hvx,
                by simpa [Function.update_of_ne hwp] using hwx⟩
        obtain ⟨r,hr,hcore⟩ := ih sA _ u hsmall smaller
        refine ⟨r, ?_, hcore⟩
        rw [Finset.card_insert_of_notMem hp]
        omega
    obtain ⟨r,hr,hcore⟩ := strip A (fun _ h => h) f s computes has
    obtain ⟨v,hv,t,ht,smaller⟩ := core (n+1) G pureEdge cubic girth edges pureSpec r hcore
    have vA : v ∉ A := by intro h; have := noDegree v h; omega
    have restored := extend (n+1) A (fun x => pureEdge (Function.update x v false)) t smaller
    have eq : (fun x : Fin (n+1) → Bool =>
        pureEdge (Function.update x v false) || decide (∃ a ∈ A, x a = true)) =
        (fun x : Fin (n+1) → Bool => f (Function.update x v false)) := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, pureSpec, computes]
      have aux : (∃ a ∈ A, (Function.update x v false) a = true) ↔ (∃ a ∈ A, x a = true) := by
        constructor <;> rintro ⟨a,ha,hx⟩
        · have ne : a ≠ v := fun e => vA (e ▸ ha)
          exact ⟨a,ha,by simpa only [Function.update_of_ne ne] using hx⟩
        · have ne : a ≠ v := fun e => vA (e ▸ ha)
          exact ⟨a,ha,by simpa only [Function.update_of_ne ne] using hx⟩
      rw [aux,or_comm]
    exact ⟨v,vA,t + A.card,by omega,eq ▸ restored⟩
