import Mathlib.Data.List.GetD
import Mathlib.Order.Preorder.Finite
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Extend soundness to one more gate of a minimum circuit.
-- It suffices to repair the gate on maximal independent assignments.
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 14000 in
theorem PEqualNP.Outside.R_meta_2658_73
    (normal : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∃ D : Circuit,
      Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∃ u v, G.Adj u v) →
      (∀ a b c d, a ≠ c → b ≠ d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      let F (x : Fin n → Bool) := ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
      let ok (D : Circuit) := Monotone2 D ∧ ∀ x, D.eval (List.ofFn x) = true ↔ F x
      let cl (D : Circuit) (k : ℕ) := ∀ i < k, (NestedCover.gateAt D i).op = .and →
        ∀ x, Maximal (fun y => ¬F y) x → gateVal n D i x = false
      ∀ (C : Circuit) (k : ℕ), ok C → NestedCover.ReadsBack n C → (∀ E, ok E → C.size ≤ E.size) →
        k < C.size → cl C k → ¬cl C (k+1) →
        ∃ D, ok D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧ cl D (k+1)) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  classical
  intro n G A he h4 ha fa
  let F (x : Fin n → Bool) := ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  let ok (D : Circuit) := Monotone2 D ∧ ∀ x, D.eval (List.ofFn x) = true ↔ F x
  let cl (D : Circuit) (k : ℕ) := ∀ i < k, (NestedCover.gateAt D i).op = .and →
    ∀ x, Maximal (fun y => ¬F y) x → gateVal n D i x = false
  have four : ∀ a b c d, a ≠ c → b ≠ d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    intro a b c d ac bd
    rintro ⟨ab,bc,cd,da⟩
    exact h4 a b c d ab.ne ac da.ne.symm bc.ne bd cd.ne ab bc cd da
  have R : ∀ (C : Circuit) (k : ℕ), ok C → NestedCover.ReadsBack n C →
      (∀ E, ok E → C.size ≤ E.size) → k < C.size → cl C k → ¬cl C (k+1) →
      ∃ D, ok D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧ cl D (k+1) :=
    repair n G he four
  have existsSize : ∃ m : ℕ, ∃ C : Circuit, ok C ∧ C.size = m :=
    ⟨A.size,A,⟨ha,fa⟩,rfl⟩
  let m := Nat.find existsSize
  obtain ⟨C,hC,hCm⟩ : ∃ C : Circuit, ok C ∧ C.size=m := Nat.find_spec existsSize
  have least (D : Circuit) (hD : ok D) : m ≤ D.size :=
    Nat.find_min' existsSize ⟨D,hD,rfl⟩
  have hA : ok A := ⟨ha,fa⟩
  obtain ⟨E,hm,hr,hs,eq⟩ := normal n C hC.1
  have hE : ok E := ⟨hm,fun x => (eq x) ▸ hC.2 x⟩
  have sE : E.size=m := le_antisymm (hs.trans hCm.le) (least E hE)
  have inductionStep (k : ℕ) (bound : k ≤ m) :
      ∃ D : Circuit, ok D ∧ NestedCover.ReadsBack n D ∧ D.size=m ∧ cl D k := by
    induction k with
    | zero => exact ⟨E,hE,hr,sE,fun i hi => (Nat.not_lt_zero i hi).elim⟩
    | succ k ih =>
      obtain ⟨D,good,back,sz,soundSoFar⟩ := ih (by omega)
      by_cases done : cl D (k+1)
      · exact ⟨D,good,back,sz,done⟩
      · obtain ⟨T,okT,bt,st,next⟩ := R D k good back (fun V h => sz ▸ least V h)
          (by omega) soundSoFar done
        exact ⟨T,okT,bt,le_antisymm (st.trans sz.le) (least T okT),next⟩
  obtain ⟨D,good,_,sz,soundSoFar⟩ := inductionStep m le_rfl
  refine ⟨D,good.1,good.2,sz ▸ least A hA,?_⟩
  intro j g hj hop x hval
  by_contra hno
  obtain ⟨y,hxy,maxY⟩ := exists_maximal_ge_of_wellFoundedGT (fun z => ¬F z) x hno
  have hidx := (List.getElem?_eq_some_iff.mp hj).1
  have within : j < m := by change j < D.size at hidx; omega
  have atg : NestedCover.gateAt D j = g := by
    change D.gates.getD j _ = g
    rw [List.getD_eq_getElem _ _ hidx]
    exact Option.some.inj ((List.getElem?_eq_getElem hidx).symm.trans hj)
  have noY := soundSoFar j within (atg ▸ hop) y maxY
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let run (gs : List Gate) (w : List Bool) := (⟨gs,0⟩ : Circuit).wires w
  have ext (w z : List Bool) (len : w.length=z.length)
      (rel : ∀ i, w.getD i false = true → z.getD i false = true)
      (u v : Bool) (huv : u = true → v = true) :
      ∀ i, (w++[u]).getD i false = true → (z++[v]).getD i false = true := by
    intro i hv
    by_cases small : i < w.length
    · rw [List.getD_append _ _ _ _ small] at hv
      rw [List.getD_append _ _ _ _ (by omega)]
      exact rel i hv
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hv ⊢
      rw [len] at hv
      generalize i - z.length = k at hv ⊢
      cases k with
      | zero => exact huv hv
      | succ k => simp at hv
  have mono (gs : List Gate) (w z : List Bool) (len : w.length=z.length)
      (rel : ∀ i, w.getD i false = true → z.getD i false = true)
      (ops : ∀ v ∈ gs, v.op = .and ∨ v.op = .or) :
      ∀ i, (run gs w).getD i false = true → (run gs z).getD i false = true := by
    induction gs generalizing w z with
    | nil => exact rel
    | cons a gs ih =>
      change ∀ i, (run gs (w++[a.op.eval _])).getD i false = true →
        (run gs (z++[a.op.eval _])).getD i false = true
      apply ih _ _ (by simp [len]) (ext w z len rel _ _ _) (fun v hv => ops v (List.mem_cons_of_mem _ hv))
      rcases ops a (by simp) with h | h
      · simp only [h,evalAnd,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        exact fun h0 i hi => rel i (h0 i hi)
      · simp only [h,evalOr,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,ht⟩
        exact ⟨i,hi,rel i ht⟩
  have lifted (k : ℕ) : (List.ofFn x).getD k false = true → (List.ofFn y).getD k false = true := by
    intro hk
    by_cases e : k<n
    · rw [List.getD_eq_getElem _ _ (by simpa using e),List.getElem_ofFn] at hk ⊢
      exact (Bool.le_iff_imp.mp (hxy ⟨k,e⟩)) hk
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
      contradiction
  have yesY := mono D.gates (List.ofFn x) (List.ofFn y) (by simp) lifted
    (fun v hv => by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (good.1 v hv).1)
    (n+j) hval
  exact Bool.false_ne_true (noY.symm.trans yesY)
