import Mathlib.Data.Set.Prod
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Third cut of L-meta-3698 (at most three reductions per step): split the
-- argument into a rectangular normal form for AO2 circuits (compile) and a
-- counting lemma that derives the 24 * size bound from that normal form
-- together with the plane axioms, the double re-read conditions and the
-- heavy-wire property (count). The two earlier reductions (R_meta_3698_720,
-- R_meta_3698_731) use different decompositions of the same argument.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3698_1
    (compile : ∀ (n m : ℕ) (C : Circuit), PEqualNP.TopForm.IsAO2 n C →
      ∀ (U : Fin m × Fin m → Fin n → Bool) (V : Finset (Fin m) → Fin n → Bool),
      ∃ R : ℕ → Set ((Fin m × Fin m) × Finset (Fin m)),
        (∀ k, ∃ (A : Set (Fin m × Fin m)) (B : Set (Finset (Fin m))), R k = A ×ˢ B) ∧
        (∀ i : Fin n, R i.val = {z | U z.1 i = true ∧ V z.2 i = false}) ∧
        (∀ j : Fin C.size, ∃ a < n+j.val, ∃ b < n+j.val, (C.gates.get j).inputs = [a,b] ∧ R (n+j.val) ⊆ R a ∪ R b) ∧
        (C.output < n+C.size ∨ R C.output = ∅) ∧
        R C.output = {z | circuitFun n C (U z.1) = true ∧ circuitFun n C (V z.2) = false})
    (count : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (E : Finset (Fin N × Fin N)) (C : Circuit)
      (R : ℕ → Set ((Fin N × Fin N) × Finset (Fin N))),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      (∀ e ∈ E, I e.1 e.2) →
      (∀ e ∈ E, circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
      (∀ e ∈ E, PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i))
        e.1.val (N + e.2.val) = false) →
      (∀ e ∈ E, PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N))
        e.1.val (N + e.2.val) = false) →
      (∀ (i : Fin (N + N)), have d : ℕ := (E.filter (fun e => i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)).card
        (0 : ℕ) < d → (24 : ℕ) * max (1 : ℕ) (Fintype.card {j : Fin C.size // i.val ∈ (C.gates.get j).inputs}) < d) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ k, ∃ (A : Set (Fin N × Fin N)) (B : Set (Finset (Fin N))), R k = A ×ˢ B) →
      (∀ p : Fin N, R p.val ⊆ {z | z.1.1 = p ∧ ∃ l ∈ z.2, I p l}) →
      (∀ l : Fin N, R (N + l.val) ⊆ {z | z.1.2 = l ∧ l ∉ z.2}) →
      (∀ j : Fin C.size, ∃ a < N + N + j.val, ∃ b < N + N + j.val,
        (C.gates.get j).inputs = [a, b] ∧ R (N + N + j.val) ⊆ R a ∪ R b) →
      ((E : Set (Fin N × Fin N)) ×ˢ {Y : Finset (Fin N) | Y.card ≤ q}) ⊆ R C.output →
      C.output < N + N + C.size →
      E.card ≤ 24 * C.size) :
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
  exact count q N I E C R hq hN reg uniq
    (fun e he => (accept e he).1)
    (fun e he => (accept e he).2)
    (fun e he => (Finset.mem_filter.mp he).2.2.2.1)
    (fun e he => (Finset.mem_filter.mp he).2.2.2.2)
    dense ao rect point line gate root ho

