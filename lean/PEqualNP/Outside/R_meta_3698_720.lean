import Mathlib.Data.Set.Prod
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Every flag needs both its empty-query column and its own singleton column.
-- Neither source leaf can contain both. Charge the first meeting to an actual gate.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3698_720
    (compile : ∀ (n m : ℕ) (C : Circuit), PEqualNP.TopForm.IsAO2 n C →
      ∀ (U : Fin m × Fin m → Fin n → Bool) (V : Finset (Fin m) → Fin n → Bool),
      ∃ R : ℕ → Set ((Fin m × Fin m) × Finset (Fin m)),
        (∀ k, ∃ (A : Set (Fin m × Fin m)) (B : Set (Finset (Fin m))), R k = A ×ˢ B) ∧
        (∀ i : Fin n, R i.val = {z | U z.1 i = true ∧ V z.2 i = false}) ∧
        (∀ j : Fin C.size, ∃ a < n+j.val, ∃ b < n+j.val, (C.gates.get j).inputs = [a,b] ∧ R (n+j.val) ⊆ R a ∪ R b) ∧
        (C.output < n+C.size ∨ R C.output = ∅) ∧
        R C.output = {z | circuitFun n C (U z.1) = true ∧ circuitFun n C (V z.2) = false})
    (crowd : ∀ (N n s o : ℕ) (E : Finset (Fin N × Fin N))
      (R : ℕ → Set ((Fin N × Fin N) × Finset (Fin N))),
      let both := fun k (e : Fin N × Fin N) => (e,∅) ∈ R k ∧ (e,{e.2}) ∈ R k
      o < n+s → (∀ e ∈ E, both o e) → (∀ k < n, ∀ e ∈ E, ¬ both k e) →
      24*s < E.card → ∃ j < s, ∃ F ⊆ E, 24 < F.card ∧
        ∀ e ∈ F, both (n+j) e ∧ ∀ k < n+j, ¬ both k e)
    (orient : ∀ (X Y : Type) (F : Set X) (empty : Y) (query : X → Y)
    (A B : Set X) (U V : Set Y)
    (cover : ∀ e ∈ F, ((e ∈ A ∧ empty ∈ U) ∨ (e ∈ B ∧ empty ∈ V)) ∧
      ((e ∈ A ∧ query e ∈ U) ∨ (e ∈ B ∧ query e ∈ V)))
    (first : ∀ e ∈ F, ¬ (e ∈ A ∧ empty ∈ U ∧ query e ∈ U) ∧
      ¬ (e ∈ B ∧ empty ∈ V ∧ query e ∈ V)),
    (∀ e ∈ F, e ∈ A ∧ e ∈ B ∧ empty ∈ U ∧ empty ∉ V ∧ query e ∉ U ∧ query e ∈ V) ∨
    (∀ e ∈ F, e ∈ A ∧ e ∈ B ∧ empty ∈ V ∧ empty ∉ U ∧ query e ∉ V ∧ query e ∈ U))
    (forest : ∀ (q N : ℕ), let X : Type := Fin N; let n : ℕ := N+N
      ∀ (I : X → X → Prop) (E : Finset (X × X)),
      (87 : ℕ) ≤ q → N = ((q ^ (2 : ℕ) : ℕ) + q + (1 : ℕ) : ℕ) →
      (∀ (l : X), Nat.card {p : X // I p l} = q+(1 : ℕ)) →
      (∀ (p p' : X), p ≠ p' → ∃! l : X, I p l ∧ I p' l) →
      (∀ e ∈ E, I e.1 e.2) →
      ∀ (C : Circuit) (R : ℕ → Set ((X × X) × Finset X)), PEqualNP.TopForm.IsAO2 n C →
      (∀ e ∈ E, circuitFun n C (fun i : Fin n => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
      (∀ e ∈ E, ∀ (b : Bool),
        PEqualNP.ReadK.lineSingle C n (fun i : ℕ => decide (i < N) == b) e.1.val (N+e.2.val) = false) →
      (∀ (i : Fin n), have d : ℕ := (E.filter (fun e => i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)).card
        (0 : ℕ) < d → (24 : ℕ) * max (1 : ℕ) (Fintype.card {j : Fin C.size // i.val ∈ (C.gates.get j).inputs}) < d) →
      (∀ (k : ℕ), ∃ (A : Set (X × X)) (B : Set (Finset X)), R k = A ×ˢ B) →
      (∀ (p : X), R p.val ⊆ {z : (X × X) × Finset X | z.1.1 = p ∧ ∃ l ∈ z.2, I p l}) →
      (∀ (l : X), R (N+l.val) ⊆ {z : (X × X) × Finset X | z.1.2 = l ∧ l ∉ z.2}) →
      (∀ (j : Fin C.size), ∃ a < n+j.val, ∃ b < n+j.val,
        (C.gates.get j).inputs = [a,b] ∧ R (n+j.val) ⊆ R a ∪ R b) →
      ((E : Set (X × X)) ×ˢ {Y : Finset X | Y.card ≤ q}) ⊆ R C.output →
      (∃ (j : Fin C.size) (a b : ℕ), (C.gates.get j).inputs.Perm [a,b] ∧
        ∃ F ⊆ E, (24 : ℕ) < F.card ∧ ∀ e ∈ F,
          (e,(@EmptyCollection.emptyCollection (Finset X) (@Finset.instEmptyCollection (Fin N)))) ∈ R a ∧ (e,(@Singleton.singleton X (Finset X) (@Finset.instSingleton (Fin N)) e.2)) ∈ R b ∧ (e,(@EmptyCollection.emptyCollection (Finset X) (@Finset.instEmptyCollection (Fin N)))) ∉ R b ∧ (e,(@Singleton.singleton X (Finset X) (@Finset.instSingleton (Fin N)) e.2)) ∉ R a) →
      E.card ≤ (24 : ℕ)*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           have x9 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) => {x10 : Fin x2 × Fin x2 | x3 x10.1 x10.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x9 fun (x11 : Fin (x2 + x2)) => Decidable.decide (x11 = Fin.castAdd x2 x10.1 ∨ x11 = Fin.natAdd x2 x10.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x9 (x2 + x2) (fun (x11 : ℕ) => Decidable.decide (x2 ≤ x11)) (↑x10.1) (x2 + ↑x10.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x9 (x2 + x2) (fun (x11 : ℕ) => Decidable.decide (x11 < x2)) (↑x10.1) (x2 + ↑x10.2) = Bool.false};           have x10 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.false;           have x11 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x11 : PEqualNP.CircuitLowerBounds.Circuit) =>             ∀ (x12 : Fin (x2 + x2)),               have x13 : ℕ := {x13 ∈ x9 x11 | x12 = Fin.castAdd x2 x13.1 ∨ x12 = Fin.natAdd x2 x13.2}.card;               (0 : ℕ) < x13 → (24 : ℕ) * Max.max (1 : ℕ) (Fintype.card { x15 : Fin x11.size // ↑x12 ∈ (x11.gates.get x15).inputs }) < x13;           ∀ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x12 → x10 x12 → (4513 : ℕ) ≤ x12.size → x11 x12 → (x9 x12).card ≤ (24 : ℕ) * x12.size := by
  classical
  intro q N I inst hq hN reg uniq
  dsimp only
  intro C ao sound size dense
  let E : Finset (Fin N × Fin N) := {x10 : Fin N × Fin N | I x10.1 x10.2 ∧ (PEqualNP.MetaComplexity.circuitFun (N + N) C fun (x11 : Fin (N + N)) => Decidable.decide (x11 = Fin.castAdd N x10.1 ∨ x11 = Fin.natAdd N x10.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun (x11 : ℕ) => Decidable.decide (N ≤ x11)) (↑x10.1) (N + ↑x10.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun (x11 : ℕ) => Decidable.decide (x11 < N)) (↑x10.1) (N + ↑x10.2) = Bool.false}
  change E.card ≤ 24*C.size
  let U := fun (e : Fin N × Fin N) (i : Fin (N+N)) =>
    decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
  let V : Finset (Fin N) → Fin (N+N) → Bool := fun Y => Fin.addCases
    (fun p : Fin N => decide (∀ l ∈ Y, ¬ I p l))
    (fun l : Fin N => decide (l ∈ Y))
  have cross (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro e
    have h := congrArg Fin.val e
    change p.val = N + l.val at h
    omega
  have cross' (p l : Fin N) := Ne.symm (cross p l)
  obtain ⟨R,rect,leaf,gate,limit,out⟩ := compile _ N C ao U V
  have accept (e) (he : e ∈ E) : I e.1 e.2 ∧ circuitFun (N+N) C (U e) = true := by
    have h := (Finset.mem_filter.mp he).2
    exact ⟨h.1,h.2.1⟩
  have reject (Y : Finset (Fin N)) (hy : Y.card ≤ q) : circuitFun (N+N) C (V Y) = false := by
    apply sound
    · simpa only [V,Fin.addCases_right,decide_eq_true_eq,Fintype.card_coe] using hy
    · rintro ⟨p,l,hI,hp,hl⟩
      simp only [V,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq] at hp hl
      exact hp l hl hI
  have root : ((E : Set (Fin N × Fin N)) ×ˢ {Y : Finset (Fin N) | Y.card ≤ q}) ⊆ R C.output := by
    rw [out]
    rintro ⟨e,Y⟩ ⟨he,hY⟩
    exact ⟨(accept e he).2,reject Y hY⟩
  rcases E.eq_empty_or_nonempty with em|ne
  · simp [em]
  have ho : C.output < N+N+C.size := by
    rcases limit with h|h
    · exact h
    obtain ⟨e,he⟩ := ne
    have hh := root (show (e,∅) ∈ ((E : Set (Fin N × Fin N)) ×ˢ {Y : Finset (Fin N) | Y.card ≤ q}) from ⟨he,by simp⟩)
    rw [h] at hh
    exact hh.elim
  have point (p : Fin N) : R p.val ⊆ {z | z.1.1 = p ∧ ∃ l ∈ z.2, I p l} := by
    intro z hz
    have h := (leaf (Fin.castAdd N p)) ▸ hz
    change U z.1 (Fin.castAdd N p) = true ∧ V z.2 (Fin.castAdd N p) = false at h
    simp only [U,V,Fin.addCases_left, Fin.addCases_right,Fin.castAdd_inj,Fin.natAdd_inj,
      cross,cross',or_false,false_or,decide_eq_true_eq,decide_eq_false_iff_not] at h
    try push Not at h
    exact ⟨h.1.symm,h.2⟩
  have line (l : Fin N) : R (N+l.val) ⊆ {z | z.1.2 = l ∧ l ∉ z.2} := by
    intro z hz
    have h := (leaf (Fin.natAdd N l)) ▸ hz
    change U z.1 (Fin.natAdd N l) = true ∧ V z.2 (Fin.natAdd N l) = false at h
    simp only [U,V,Fin.addCases_left, Fin.addCases_right,Fin.castAdd_inj,Fin.natAdd_inj,
      cross,cross',or_false,false_or,decide_eq_true_eq,decide_eq_false_iff_not] at h
    try push Not at h
    exact ⟨h.1.symm,h.2⟩
  by_contra! bad
  have bothRoot (e) (he : e ∈ E) : (e,∅) ∈ R C.output ∧ (e,{e.2}) ∈ R C.output := by
    refine ⟨root ⟨he,by simp⟩,root ⟨he,?_⟩⟩
    change ({e.2} : Finset (Fin N)).card ≤ q
    simp only [Finset.card_singleton]
    omega
  have noLeaf (k) (hk : k < N+N) (e) (_ : e ∈ E) :
      ¬ ((e,∅) ∈ R k ∧ (e,{e.2}) ∈ R k) := by
    rintro ⟨empty,singleton⟩
    by_cases h : k < N
    · obtain ⟨l,hl,_⟩ := (point ⟨k,h⟩ empty).2
      exact Finset.notMem_empty l hl
    · let l : Fin N := ⟨k-N,by omega⟩
      have hidx : N+l.val = k := by dsimp [l]; omega
      rw [←hidx] at singleton
      obtain ⟨ee,nn⟩ := line l singleton
      exact nn (by rw [←ee]; exact Finset.mem_singleton_self _)
  have collision := crowd N (N+N) C.size C.output E R ho bothRoot noLeaf bad
  obtain ⟨j,hj,F,sub,many,first⟩ := collision
  obtain ⟨a,ha,b,hb,ins,cover⟩ := gate ⟨j,hj⟩
  obtain ⟨A,U,hA⟩ := rect a
  obtain ⟨B,V,hB⟩ := rect b
  let y := fun e : Fin N × Fin N => ({e.2} : Finset (Fin N))
  have cells (e) (he : e ∈ F) := (first e he).1
  have sep := orient _ _ (F : Set _) ∅ y A B U V (by
    intro e he
    have z := cells e he
    have h := cover z.1
    have h' := cover z.2
    rw [hA,hB] at h h'
    exact ⟨h,h'⟩) (by
    intro e he
    have none := (first e he).2
    constructor
    · rintro ⟨row,emp,sing⟩
      apply none a ha
      rw [hA]
      exact ⟨⟨row,emp⟩,⟨row,sing⟩⟩
    · rintro ⟨row,emp,sing⟩
      apply none b hb
      rw [hB]
      exact ⟨⟨row,emp⟩,⟨row,sing⟩⟩)
  apply (Nat.not_le_of_gt bad)
  apply forest q N I E hq hN (fun l => by simpa only [Nat.card_eq_fintype_card] using reg l)
    uniq (fun e he => (accept e he).1) C R ao (fun e he => (accept e he).2) _ dense rect point line gate root ?_
  · intro e he b
    obtain ⟨_,_,h1,h2⟩ := (Finset.mem_filter.mp he).2
    cases b
    · have ht : (fun i : ℕ => decide (i < N) == false) = (fun i => decide (N ≤ i)) := by
        funext i
        by_cases small : i < N
        · simp [small, Nat.not_le_of_gt small]
        · simp [small, Nat.le_of_not_gt small]
      rw [ht]
      exact h1
    · have ht : (fun i : ℕ => decide (i < N) == true) = (fun i => decide (i < N)) := by
        funext i
        cases decide (i < N) <;> rfl
      rw [ht]
      exact h2
  · rcases sep with h|h
    · refine ⟨⟨j,hj⟩,a,b,by rw [ins],F,sub,many,?_⟩
      intro e he
      obtain ⟨rowA,rowB,emp,noEmp,noSing,sing⟩ := h e he
      rw [hA,hB]
      exact ⟨⟨rowA,emp⟩,⟨rowB,sing⟩,fun hh => noEmp hh.2,fun hh => noSing hh.2⟩
    · refine ⟨⟨j,hj⟩,b,a,by rw [ins]; exact List.Perm.swap _ _ [],F,sub,many,?_⟩
      intro e he
      obtain ⟨rowA,rowB,emp,noEmp,noSing,sing⟩ := h e he
      rw [hA,hB]
      exact ⟨⟨rowB,emp⟩,⟨rowA,sing⟩,fun hh => noEmp hh.2,fun hh => noSing hh.2⟩
