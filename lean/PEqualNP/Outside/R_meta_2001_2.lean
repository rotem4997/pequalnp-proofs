import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2001_2
    (append_pairs : ∀ (n : ℕ) (E : List (Fin n × Fin n)) (C : Circuit), Monotone2 C →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size + 2*E.length ∧ ∀ x y : Fin n → Bool,
        D.eval (List.ofFn x ++ List.ofFn y) = (C.eval (List.ofFn x ++ List.ofFn y) ||
          E.any fun e => x e.1 && y e.2))
    (approx : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ (R : Circuit) (E : Finset (Fin n × Fin n)), Monotone2 R ∧
        (∀ y : Fin n → Bool, R.eval
          (List.ofFn (fun u => decide (∀ v, G.Adj u v → y v = false)) ++ List.ofFn y) = false) ∧
        R.size + E.card ≤ k * (C.size+1) ∧ ∀ e, e ∈ E ↔ G.Adj e.1 e.2 ∧
          R.eval (List.ofFn (fun i : Fin n => decide (i = e.1)) ++
            List.ofFn (fun j : Fin n => decide (j = e.2))) = false) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_increasing (C : Circuit) (mono : Monotone2 C) (xs ys : List Bool)
      (length : xs.length = ys.length)
      (reads : ∀ i, xs.getD i false = true → ys.getD i false = true) :
      C.eval xs = true → C.eval ys = true := by
    have run (gs : List Gate) (legal : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (x y : List Bool) (len : x.length = y.length)
        (atWire : ∀ i, x.getD i false = true → y.getD i false = true) :
        ∀ i, (gs.foldl step x).getD i false = true → (gs.foldl step y).getD i false = true := by
      induction gs generalizing x y with
      | nil => exact atWire
      | cons g gs ih =>
        have gate : g.op.eval (g.inputs.map fun i => x.getD i false) = true →
            g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
          rcases legal g List.mem_cons_self with h | h
          · rw [h]
            change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
            simp only [List.all_map,List.all_eq_true,Function.comp_def,id_eq]
            exact fun hx i hi => atWire i (hx i hi)
          · rw [h]
            change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
            simp only [List.any_map,List.any_eq_true,Function.comp_def,id_eq]
            rintro ⟨i,hi,bit⟩
            exact ⟨i,hi,atWire i bit⟩
        apply ih (fun h hh => legal h (List.mem_cons_of_mem _ hh)) (step x g) (step y g)
          (by simp [step,len])
        intro i
        by_cases before : i < x.length
        · change ((_ ++ _)[i]?).getD false = true → ((_ ++ _)[i]?).getD false = true
          rw [List.getElem?_append_left before,List.getElem?_append_left (len ▸ before)]
          exact atWire i
        · by_cases last : i = x.length
          · subst i
            change ((x ++ [_])[x.length]?).getD false = true → ((y ++ [_])[x.length]?).getD false = true
            rw [List.getElem?_concat_length,len,List.getElem?_concat_length]
            exact gate
          · rw [List.getD_eq_default _ _ (by simp [step]; omega)]
            simp
    exact run C.gates (fun g hg => (mono g hg).1) xs ys length reads C.output

  have banks_increasing {n : ℕ} (C : Circuit) (mono : Monotone2 C)
      (x y x' y' : Fin n → Bool) (left : ∀ i, x i = true → x' i = true)
      (right : ∀ i, y i = true → y' i = true) :
      C.eval (List.ofFn x ++ List.ofFn y) = true → C.eval (List.ofFn x' ++ List.ofFn y') = true := by
    apply eval_increasing C mono _ _ (by simp)
    intro i
    by_cases hi : i < n
    · rw [List.getD_append _ _ _ _ (by simpa using hi),List.getD_append _ _ _ _ (by simpa using hi)]
      simpa [hi] using left ⟨i,hi⟩
    · rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      by_cases hj : i-n < n
      · simpa [hj] using right ⟨i-n,hj⟩
      · rw [List.getD_eq_default _ _ (by simp; omega)]; simp

  have repair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (mono : Monotone2 C)
      (safe : ∀ y : Fin n → Bool,
        C.eval (List.ofFn (fun u => decide (∀ v, G.Adj u v → y v = false)) ++ List.ofFn y) = false) :
      let missed := Finset.univ.filter fun e : Fin n × Fin n => G.Adj e.1 e.2 ∧
        C.eval (List.ofFn (fun i : Fin n => decide (i = e.1)) ++
          List.ofFn (fun j : Fin n => decide (j = e.2))) = false
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size + 2 * missed.card ∧
        ∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ u v, G.Adj u v ∧ x u = true ∧ y v = true) := by
    intro missed
    obtain ⟨D,model,cost,eval⟩ := append_pairs n missed.toList C mono
    refine ⟨D,model,by simpa only [Finset.length_toList] using cost,?_⟩
    intro x y
    rw [eval,Bool.eq_iff_iff]
    simp only [Bool.or_eq_true_iff,List.any_eq_true,Finset.mem_toList,Bool.and_eq_true_iff,decide_eq_true_eq]
    constructor
    · rintro (h | ⟨⟨u,v⟩,he,hu,hv⟩)
      · by_contra none
        let z (u : Fin n) := decide (∀ v, G.Adj u v → y v = false)
        have above (i : Fin n) (hi : x i = true) : z i = true := by
          apply decide_eq_true
          intro j edge
          cases hj : y j with
          | false => rfl
          | true => exact (none ⟨i,j,edge,hi,hj⟩).elim
        have up := banks_increasing C mono x y z y above (fun _ hy => hy) h
        exact Bool.noConfusion (up.symm.trans (safe y))
      · exact ⟨u,v,(Finset.mem_filter.mp he).2.1,hu,hv⟩
    · rintro ⟨u,v,adj,hu,hv⟩
      let point (i : Fin n) := decide (i = u)
      let line (i : Fin n) := decide (i = v)
      cases h : C.eval (List.ofFn point ++ List.ofFn line) with
      | true =>
        left
        apply banks_increasing C mono point line x y _ _ h
        · intro i hi; exact (of_decide_eq_true hi : i = u) ▸ hu
        · intro i hi; exact (of_decide_eq_true hi : i = v) ▸ hv
      | false =>
        right
        exact ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,adj,h⟩,hu,hv⟩
  obtain ⟨k, build⟩ := approx
  refine ⟨2*k+1,?_⟩
  intro n G inst degree girth C mono correct
  obtain ⟨R,E,modelR,safe,budget,errors⟩ := build n G degree girth C mono correct
  obtain ⟨D,modelD,price,works⟩ := repair n G R modelR safe
  have same : (Finset.univ.filter fun e : Fin n × Fin n => G.Adj e.1 e.2 ∧
      R.eval (List.ofFn (fun i : Fin n => decide (i = e.1)) ++
        List.ofFn (fun j : Fin n => decide (j = e.2))) = false) = E := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (errors e).symm
  rw [same] at price
  refine ⟨D,modelD,?_,works⟩
  rw [price, Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  omega
