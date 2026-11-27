import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Each borrowed line sum is the neighbor sum of a new point with a private line.
-- Its three incidences and new matching edge pay for four gates.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_5759_248
    (core : ∃ (n k : ℕ) (E : Finset (Fin n × Fin n)) (a b : Fin k → Fin n) (C : Circuit),
      (∀ i, (i,i) ∈ E) ∧
      (∀ p q l t, p ≠ q → l ≠ t → ¬ ((p,l) ∈ E ∧ (p,t) ∈ E ∧ (q,l) ∈ E ∧ (q,t) ∈ E)) ∧
      (∀ j, a j < b j) ∧ Function.Injective (fun j => (a j,b j)) ∧
      (∀ j p, ¬ ((p,a j) ∈ E ∧ (p,b j) ∈ E)) ∧
      IsAO2 (n+n+k) C ∧ C.output < n+n+k+C.size ∧ C.size+1 < E.card+n ∧
      ∀ x y : Fin n → Bool,
        C.eval ((List.ofFn x ++ List.ofFn y) ++ List.ofFn (fun j => y (a j) || y (b j))) =
          decide (∃ e ∈ E, x e.1 = true ∧ y e.2 = true))
    (compile : ∀ (n k : ℕ) (a b : Fin k → Fin n) (C : Circuit),
      IsAO2 (n+n+k) C → C.output < n+n+k+C.size →
      ∃ D : Circuit, IsAO2 ((n+k)+(n+k)) D ∧ D.size ≤ C.size+4*k ∧
      ∀ x y : Fin (n+k) → Bool,
        D.eval (List.ofFn x ++ List.ofFn y) =
          (C.eval ((List.ofFn (fun i : Fin n => x (Fin.castAdd k i)) ++
                    List.ofFn (fun i : Fin n => y (Fin.castAdd k i))) ++
                    List.ofFn (fun j => y (Fin.castAdd k (a j)) || y (Fin.castAdd k (b j)))) ||
           (List.finRange k).any (fun j => x (Fin.natAdd n j) &&
             ((y (Fin.castAdd k (a j)) || y (Fin.castAdd k (b j))) || y (Fin.natAdd n j))))) :
  ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4 ⊆ x3 ∧ (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) ∧ (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.2 = x8.2 → x6 = x8) ∧ (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ (∀ (x6 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x2), (x7, x8) ∈ x3 ∧ x6 (Fin.castAdd x2 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true)) ∧ x5.size + (1 : ℕ) < x3.card + x4.card := by
  classical
  have geometry : ∀ (n k : ℕ) (E : Finset (Fin n × Fin n)) (a b : Fin k → Fin n),
        (∀ i, (i,i) ∈ E) →
        (∀ p q l t, p ≠ q → l ≠ t → ¬ ((p,l) ∈ E ∧ (p,t) ∈ E ∧ (q,l) ∈ E ∧ (q,t) ∈ E)) →
        (∀ j, a j < b j) → Function.Injective (fun j => (a j,b j)) →
        (∀ j p, ¬ ((p,a j) ∈ E ∧ (p,b j) ∈ E)) →
        let adj : Fin (n+k) → Fin (n+k) → Bool := Fin.addCases
          (fun p => Fin.addCases (fun l => decide ((p,l) ∈ E)) (fun _ => false))
          (fun j => Fin.addCases (fun l => decide (l=a j ∨ l=b j)) (fun t => decide (j=t)))
        let H := Finset.univ.filter (fun e : Fin (n+k) × Fin (n+k) => adj e.1 e.2)
        (∀ i, (i,i) ∈ H) ∧ H.card=E.card+3*k ∧
        ∀ p q l t, p ≠ q → l ≠ t → ¬ ((p,l) ∈ H ∧ (p,t) ∈ H ∧ (q,l) ∈ H ∧ (q,t) ∈ H) := by
    classical
    intro n k E a b diagonal free order injective available
    dsimp only
    let adj : Fin (n+k) → Fin (n+k) → Bool := Fin.addCases
      (fun p => Fin.addCases (fun l => decide ((p,l) ∈ E)) (fun _ => false))
      (fun j => Fin.addCases (fun l => decide (l=a j ∨ l=b j)) (fun t => decide (j=t)))
    let H := Finset.univ.filter (fun e : Fin (n+k) × Fin (n+k) => adj e.1 e.2)
    change (∀ i, (i,i) ∈ H) ∧ H.card = E.card + 3*k ∧ _
    let s : Fin n ⊕ Fin k ≃ Fin (n+k) := finSumFinEquiv
    have mem (x y : Fin n ⊕ Fin k) : (s x,s y) ∈ H ↔
        Sum.elim (fun p => Sum.elim (fun l => (p,l) ∈ E) (fun _ => False) y)
          (fun j => Sum.elim (fun l => l = a j ∨ l = b j) (fun t => j = t) y) x := by
      cases x <;> cases y <;> simp [s,H,adj]
    refine ⟨?_,?_,?_⟩
    · intro u
      obtain ⟨x,rfl⟩ := s.surjective u
      rw [mem]
      cases x <;> simp_all
    · have count (N : Nat) (F : Finset (Fin N × Fin N)) :
          F.card = ∑ p : Fin N, ∑ l : Fin N, if (p,l) ∈ F then (1 : Nat) else 0 := by
        rw [← Fintype.sum_prod_type (fun e : Fin N × Fin N => if e ∈ F then (1 : Nat) else 0),
          Finset.sum_boole]
        simp
      have pair (j : Fin k) : (∑ l : Fin n, if l = a j ∨ l = b j then (1 : Nat) else 0) = 2 := by
        have eq : (Finset.univ.filter (fun l => l = a j ∨ l = b j)) = {a j,b j} := by ext; simp
        rw [Finset.sum_boole,eq]
        simp [(order j).ne]
      rw [count (n+k) H,count n E,Fin.sum_univ_add]
      simp only [Fin.sum_univ_add, H, Finset.mem_filter, Finset.mem_univ, true_and, adj,
        Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq, Bool.false_eq_true,
        ite_false, Finset.sum_const_zero, add_zero, pair]
      simp
      omega
    · change ∀ p q l t, p ≠ q → l ≠ t → ¬ ((p,l) ∈ H ∧ (p,t) ∈ H ∧ (q,l) ∈ H ∧ (q,t) ∈ H)
      intro p q l t hp hl
      obtain ⟨p,rfl⟩ := s.surjective p
      obtain ⟨q,rfl⟩ := s.surjective q
      obtain ⟨l,rfl⟩ := s.surjective l
      obtain ⟨t,rfl⟩ := s.surjective t
      have row : p ≠ q := fun h => hp (congrArg s h)
      have col : l ≠ t := fun h => hl (congrArg s h)
      simp only [mem]
      have pairs (i j : Fin k) (ha : a i = a j) (hb : b i = b j) : i = j :=
        injective (Prod.ext ha hb)
      cases l with
      | inr i => cases p <;> cases q <;> cases t <;> simp_all; grind
      | inl l =>
        cases t with
        | inr i => cases p <;> cases q <;> simp_all; grind
        | inl t =>
          cases p <;> cases q <;> simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq] at * <;>
            grind
  obtain ⟨n,k,E,a,b,C,diag,square,ordered,inj,free,ao,valid,budget,accept⟩ := core
  let adj : Fin (n+k) → Fin (n+k) → Bool := Fin.addCases
    (fun p => Fin.addCases (fun l => decide ((p,l) ∈ E)) (fun _ => false))
    (fun j => Fin.addCases (fun l => decide (l=a j ∨ l=b j)) (fun t => decide (j=t)))
  let H := Finset.univ.filter (fun e : Fin (n+k) × Fin (n+k) => adj e.1 e.2)
  let M := Finset.univ.image (fun i : Fin (n+k) => (i,i))
  obtain ⟨diagonal,card,noSq⟩ := geometry n k E a b diag square ordered inj free
  change (∀ i, (i,i) ∈ H) at diagonal
  change H.card = E.card+3*k at card
  obtain ⟨D,model,price,spec⟩ := compile n k a b C ao valid
  have memM (e : Fin (n+k) × Fin (n+k)) : e ∈ M → e.1 = e.2 := by
    intro he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    rfl
  have cardM : M.card = n+k := by
    dsimp only [M]
    rw [Finset.card_image_of_injective _ (fun _ _ he => congrArg Prod.fst he)]
    simp
  refine ⟨n+k,n+k,H,M,D,?_,?_,?_,noSq,model,?_,by omega⟩
  · rintro ⟨u,v⟩ h
    have uv : u = v := memM _ h
    subst v
    exact diagonal _
  · intro e he f hf same
    exact Prod.ext same ((memM e he).symm.trans (same.trans (memM f hf)))
  · intro e he f hf same
    exact Prod.ext ((memM e he).trans (same.trans (memM f hf).symm)) same
  · intro z
    let x : Fin (n+k) → Bool := fun p => z (Fin.castAdd (n+k) p)
    let y : Fin (n+k) → Bool := fun l => z (Fin.natAdd (n+k) l)
    have parts : List.ofFn z = List.ofFn x ++ List.ofFn y := List.ofFn_add
    change D.eval (List.ofFn z) = decide (∃ p l, (p,l) ∈ H ∧ x p = true ∧ y l = true)
    rw [parts,spec,accept]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true, List.mem_finRange, true_and]
    constructor
    · rintro (⟨e,he,hx,hy⟩ | ⟨i,hx,hy⟩)
      · exact ⟨Fin.castAdd k e.1,Fin.castAdd k e.2, by simpa [H,adj] using he,hx,hy⟩
      · rcases hy with (ha|hb)|ht
        · exact ⟨Fin.natAdd n i,Fin.castAdd k (a i),by simp [H,adj],hx,ha⟩
        · exact ⟨Fin.natAdd n i,Fin.castAdd k (b i),by simp [H,adj],hx,hb⟩
        · exact ⟨Fin.natAdd n i,Fin.natAdd n i,by simp [H,adj],hx,ht⟩
    · rintro ⟨p,l,he,hx,hy⟩
      revert he hx hy
      refine Fin.addCases ?_ ?_ p
      · intro u
        refine Fin.addCases ?_ ?_ l
        · intro v hv hu hline
          exact Or.inl ⟨(u,v),by simpa [H,adj] using hv,hu,hline⟩
        · intro j hj
          simp [H,adj] at hj
      · intro i
        refine Fin.addCases ?_ ?_ l
        · intro v h uon von
          have eq : v = a i ∨ v = b i := by simpa [H,adj] using h
          rcases eq with rfl | rfl
          · exact Or.inr ⟨i,uon,Or.inl (Or.inl von)⟩
          · exact Or.inr ⟨i,uon,Or.inl (Or.inr von)⟩
        · intro j h uon von
          have eq : i = j := by simpa [H,adj] using h
          exact Or.inr ⟨i,uon,Or.inr (eq ▸ von)⟩
