import PEqualNP.Defs

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4289_417
    (realize : ∀ (n s o : Nat) (W : Nat → Set (Fin n → Bool)),
    (∀ i : Fin n, W i={x | x i=true}) →
    (∀ j<s, ∃ a b, max a b<n+j ∧ W (n+j)∈[W a∪W b,W a,∅,W a∩W b]) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.output=o ∧ C.size=s ∧ PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    ∀ k<n+s, ∀ x, (C.wires (List.ofFn x)).getD k false=true ↔ x∈W k)
    (rank : ∀ (N q : Nat) (S : Fin N → Finset (Fin N)) (F : PEqualNP.MetaComplexity.DMFormula (N+N)),
    (∀ l, (S l).card=q+1) → PEqualNP.MetaComplexity.DMFormula.rec (motive:=fun _ => Prop) (fun _ b => b=true) (fun _ _ a b => a∧b) (fun _ _ a b => a∧b) F → (let e := fun (X Y : Finset (Fin N)) => F.eval (Fin.append (fun a => decide (a∈X)) (fun b => decide (b∈Y)))
    e Finset.univ ∅=false ∧ ∀ l, ∀ p∈S l, e {p} {l}=true ∧
      e ((S l).erase p) (Finset.univ.filter (fun k => p∈S k ∧ k≠l))=false) → N*q≤F.leaves)
    (compression : ∀ (q N : Nat) (S : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    199<q → N=q^2+q+1 → (∀ l,(S l).card=q+1) →
    (∀ a b, a≠b → ∃! l, a∈S l ∧ b∈S l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C →
    PEqualNP.GenericRejection.RightOnIncidentPairs S C →
    (∀ Y : Finset (Fin N), Y.card≤q → C.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet S Y) Y)=false) →
    (let A := fun (k : Nat) => {p : Fin N | (C.wires (List.ofFn (fun a : Fin N => decide (a=p)) ++ List.replicate N false)).getD k false=true}
     ∃ j<C.size, let w:=N+N+j
                (A w).Nontrivial ∧ ¬∃ a<w, ∃ b<w, A w=A a∪A b) →
    ∃ F : PEqualNP.MetaComplexity.DMFormula (N+N), F.leaves≤100*C.size ∧ PEqualNP.MetaComplexity.DMFormula.rec (motive:=fun _ => Prop) (fun _ b => b=true) (fun _ _ a b => a∧b) (fun _ _ a b => a∧b) F ∧ (let e := fun (X Y : Finset (Fin N)) => F.eval (Fin.append (fun a => decide (a∈X)) (fun b => decide (b∈Y)))
    e Finset.univ ∅=false ∧ ∀ l, ∀ p∈S l, e {p} {l}=true ∧
      e ((S l).erase p) (Finset.univ.filter (fun k => p∈S k ∧ k≠l))=false))
    (support : ∀ (N : Nat) (S : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p, ∃ l,p∈S l) → (∀ l,(S l).Nonempty) → PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.GenericRejection.RightOnIncidentPairs S C →
    (∀ Y : Finset (Fin N), Y.card≤1 → C.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet S Y) Y)=false) →
    N+N≤C.size+1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Fin x2) (x22 : Fin x2), x21 ≠ x22 ∧ x21 ∈ x19 Bool.true (x12 + x20) ∧ x22 ∈ x19 Bool.true (x12 + x20) ∧ ¬∃ x23 < x12 + x20, ∃ x24 < x12 + x20, x19 Bool.true (x12 + x20) = x19 Bool.true x23 ∪ x19 Bool.true x24) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I d hq order cols pairs s out W
  dsimp only
  intro outLt raw gates yes no dirty
  let S : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => I p l)
  let pull := fun (z : Fin (N+N) → Bool) => (fun i : Fin N => z (Fin.castAdd N i),fun i : Fin N => z (Fin.natAdd N i))
  let V := fun k => pull ⁻¹' (W k)
  have pin (i : Fin (N+N)) : V i={x | x i=true} := by
    refine Fin.addCases (motive:=fun j => V j={x | x j=true}) ?_ ?_ i
    · intro j; ext x
      change pull x∈W j ↔ x (Fin.castAdd N j)=true
      rw [(raw j).1]; rfl
    · intro j; ext x
      change pull x∈W (N+j.val) ↔ x (Fin.natAdd N j)=true
      rw [(raw j).2]; rfl
  have vops (j : Nat) (hj : j<s) : ∃ a b, max a b<N+N+j ∧ V (N+N+j)∈[V a∪V b,V a,∅,V a∩V b] := by
    obtain ⟨a,b,bd,kind⟩ := gates j hj
    refine ⟨a,b,bd,?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at kind ⊢
    rcases kind with h|h|h|h
    · exact Or.inl (congrArg (fun U => pull ⁻¹' U) h)
    · exact Or.inr (Or.inl (congrArg (fun U => pull ⁻¹' U) h))
    · exact Or.inr (Or.inr (Or.inl (congrArg (fun U => pull ⁻¹' U) h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg (fun U => pull ⁻¹' U) h)))
  obtain ⟨C,oc,sc,mc,bc,ev⟩ := realize (N+N) s out V pin vops
  have evaluate (k : Nat) (hk : k<N+N+s) (X Y : Finset (Fin N)) :
      (C.wires (PEqualNP.GenericRejection.incidenceInput X Y)).getD k false=true ↔
      (fun i => decide (i∈X),fun i => decide (i∈Y))∈W k := by
    let z : Fin (N+N) → Bool := Fin.addCases (fun a => decide (a∈X)) (fun b => decide (b∈Y))
    have input : List.ofFn z=PEqualNP.GenericRejection.incidenceInput X Y := by
      exact List.ofFn_fin_append (fun a : Fin N => decide (a∈X)) (fun b : Fin N => decide (b∈Y))
    have eq : pull z=(fun i => decide (i∈X),fun i => decide (i∈Y)) := by
      apply Prod.ext <;> funext j
      · simp only [pull,z,Fin.addCases_left]
      · simp only [pull,z,Fin.addCases_right]
    have step := ev k hk z
    rw [input] at step
    change _ ↔ pull z∈W k at step
    rwa [eq] at step
  have ord (l : Fin N) : (S l).card=q+1 := by simpa [S,Fintype.card_subtype] using cols l
  have uniq (a b : Fin N) (ne : a≠b) : ∃! l, a∈S l ∧ b∈S l := by simpa [S] using pairs a b ne
  have accepts : PEqualNP.GenericRejection.RightOnIncidentPairs S C := by
    intro l p h
    change (C.wires _).getD C.output false=true
    rw [oc]
    apply (evaluate _ outLt _ _).2
    have inc : I p l := (Finset.mem_filter.mp h).2
    simpa only [Finset.mem_singleton] using yes p l inc
  have rejects (Y : Finset (Fin N)) (hy : Y.card≤q) :
      C.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet S Y) Y)=false := by
    apply Bool.eq_false_iff.mpr
    change ¬(C.wires _).getD C.output false=true
    rw [oc,(evaluate _ outLt _ _)]
    let y:=fun j : Fin N => decide (j∈Y)
    have count : Fintype.card {j : Fin N // y j=true}≤q := by
      simpa [y,Fintype.card_subtype] using hy
    have mask : (fun i => decide (i∈PEqualNP.GenericRejection.zeroSet S Y)) =
        (fun i => decide (¬∃ j, I i j ∧ y j=true)) := by
      funext i
      change decide (i∈Finset.univ.filter (fun a : Fin N => ∀ l∈Y, a∉S l)) = _
      simp [S,y]
      tauto
    rw [mask]; exact no y count
  let A := fun (k : Nat) => {p : Fin N | (C.wires (List.ofFn (fun a : Fin N => decide (a=p)) ++ List.replicate N false)).getD k false=true}
  let old := fun k => {p : Fin N | ((fun j : Fin N => decide (j=p)),(fun _ : Fin N => false))∈W k}
  have Aeq (k : Nat) (hk : k<N+N+s) : A k=old k := by
    ext p
    have row : PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N)) =
        List.ofFn (fun a : Fin N => decide (a=p)) ++ List.replicate N false := by
      change (List.ofFn (fun a : Fin N => decide (a∈({p} : Finset (Fin N)))) ++ List.ofFn (fun a : Fin N => decide (a∈(∅ : Finset (Fin N)))))=_
      simp
    have test := evaluate k hk {p} ∅
    rw [row] at test
    simpa [A,old] using test
  obtain ⟨j,jbound,v,u,ne,vv,uu,new⟩ := dirty
  have top : N+N+j<N+N+s := by omega
  have novel : ∃ j<C.size, let k:=N+N+j
      (A k).Nontrivial ∧ ¬∃ a<k, ∃ b<k, A k=A a∪A b := by
    refine ⟨j,by omega,?_,?_⟩
    · rw [Aeq _ top]; exact ⟨v,vv,u,uu,ne⟩
    · rintro ⟨a,ha,b,hb,h⟩
      rw [Aeq _ top,Aeq a (by omega),Aeq b (by omega)] at h
      exact new ⟨a,ha,b,hb,h⟩
  by_cases hard : 199<q
  · obtain ⟨F,small,positive,test⟩ := compression q N S C hard order ord uniq mc bc accepts rejects novel
    exact (rank N q S F ord positive test).trans (by simpa [sc] using small)
  · have nh : 100≤N := by omega
    letI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have pointLive (p : Fin N) : ∃ l,p∈S l := by
      obtain ⟨a,ne⟩ := exists_ne p
      obtain ⟨l,inc,_⟩ := uniq p a ne.symm
      exact ⟨l,inc.1⟩
    have lineLive (l : Fin N) : (S l).Nonempty := Finset.card_pos.mp (by rw [ord]; omega)
    have count := support N S C pointLive lineLive mc accepts (fun Y hy => rejects Y (by omega))
    rw [sc] at count
    have small := Nat.mul_le_mul_left N (show q≤199 by omega)
    omega
