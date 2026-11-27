import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Sparse queries decide intersection with the union of the selected lines.
-- Compile those queries into a shared binary union program for the neighborhoods.
-- A union containing two points can be counted against at most one line.
theorem PEqualNP.Outside.R_meta_2866_714
    (compileRows : ∀ (q N : ℕ) (F : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 → (∀ l, (F l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ F l ∧ r ∈ F l) → Monotone2 C →
      (∀ x : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        circuitFun (N+N) C x = decide (∃ p l, p ∈ F l ∧
          x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      ∃ xs : List (Finset (Fin N)), xs.length ≤ 100 * C.size ∧ (∀ l, F l ∈ xs) ∧
        ∀ j S, xs[j]? = some S →
          ∃ A B : Finset (Fin N), S = A ∪ B ∧
            (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j))
    (oneOutput : ∀ (N : ℕ) (xs : List (Finset (Fin N))),
      (∀ j S, xs[j]? = some S →
          ∃ A B : Finset (Fin N), S = A ∪ B ∧
            (A.card ≤ 1 ∨ A ∈ xs.take j) ∧ (B.card ≤ 1 ∨ B ∈ xs.take j)) →
      ∀ T ∈ xs, T.card ≤ Fintype.card {j : Fin xs.length //
        1 < (xs.get j).card ∧ xs.get j ⊆ T} + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);                 have x14 : ℕ → Fin x2 → Fin x2 → Bool := fun (x14 : ℕ) (x15 x16 : Fin x2) => (x5.wires (List.ofFn (x13 x15) ++ List.ofFn (x13 x16))).getD x14 Bool.false;                 have x15 : ℕ → ℕ → Fin x2 → Fin x2 → Bool := fun (x15 x16 : ℕ) (x17 x18 : Fin x2) => x14 x15 x17 x18 && x14 x16 x17 x18;                 ∀ (x16 : Finset ℕ), (∀ (x17 : ℕ) (x18 : PEqualNP.CircuitLowerBounds.Gate) (x19 x20 : ℕ), x5.gates[x17]? = Option.some x18 → x18.op = PEqualNP.CircuitLowerBounds.GateOp.and → x18.inputs = [x19, x20] → x17 ∉ x16 → (∃ x25 ∈ [x19, x20], ∀ (x26 x27 : Fin x2), x15 x19 x20 x26 x27 = x14 x25 x26 x27) ∨ ((∀ (x25 x26 : Fin x2), x15 x19 x20 x25 x26 = Bool.true → x3 x25 x26) → ∀ (x26 x27 x28 x29 : Fin x2), x15 x19 x20 x26 x28 = Bool.true → x15 x19 x20 x27 x29 = Bool.true → x26 = x27 ∨ x28 = x29)) → (100 : ℕ) * x16.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq order degree unique mono pos sound
  dsimp only
  intro marked outside budget
  let F (l : Fin N) := Finset.univ.filter fun p => I p l
  have memF (p l) : p ∈ F l ↔ I p l := by simp [F]
  have degreeF (l) : (F l).card = q + 1 :=
    (Fintype.card_subtype (fun p => I p l)).symm.trans (degree l)
  have joins (p r : Fin N) (ne : p ≠ r) : ∃! l, p ∈ F l ∧ r ∈ F l := by
    simpa only [memF] using unique p r ne
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have propagate (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (len : u.length = v.length)
      (sub : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (gs.foldl step u).getD i false = true → (gs.foldl step v).getD i false = true := by
    induction gs generalizing u v with
    | nil => exact sub
    | cons g gs ih =>
      apply ih (fun a ha => ops a (List.mem_cons_of_mem _ ha)) (step u g) (step v g)
        (by simp [step,len])
      intro i h
      change (v ++ [_]).getD i false = true
      change (u ++ [_]).getD i false = true at h
      by_cases hi : i < u.length
      · rw [List.getD_append _ _ _ _ hi] at h
        rw [List.getD_append _ _ _ _ (hi.trans_eq len)]
        exact sub i h
      · rw [List.getD_append_right _ _ _ _ (by omega)] at h ⊢
        rw [← len]
        cases hidx : i - u.length with
        | zero =>
          rw [hidx] at h
          simp only [List.getD_cons_zero] at h ⊢
          rcases ops g List.mem_cons_self with op | op <;> rw [op] at h ⊢
          · change (g.inputs.map fun j => u.getD j false).all id = true at h
            change (g.inputs.map fun j => v.getD j false).all id = true
            simp at h ⊢
            exact fun j hj => sub j (h j hj)
          · change (g.inputs.map fun j => u.getD j false).any id = true at h
            change (g.inputs.map fun j => v.getD j false).any id = true
            simp at h ⊢
            obtain ⟨j,hj,hb⟩ := h
            exact ⟨j,hj,sub j hb⟩
        | succ t => simp [hidx,List.getD_eq_getElem?_getD] at h
  have exactQuery (x : Fin (N+N) → Bool)
      (few : Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q) :
      circuitFun (N+N) C x = decide (∃ p l, p ∈ F l ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) := by
    by_cases h : ∃ p l, p ∈ F l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true
    · rw [decide_eq_true h]
      obtain ⟨p,l,pl,hp,hl⟩ := h
      let y := fun i : Fin (N+N) => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
      have inclusion (j : ℕ) : (List.ofFn y).getD j false = true → (List.ofFn x).getD j false = true := by
        by_cases hj : j < N+N
        · simp [List.getD_eq_getElem?_getD,hj,y]
          intro he
          rcases he with he | he
          · simpa only [he] using hp
          · rw [he]; simpa using hl
        · simp [List.getD_eq_getElem?_getD,hj]
      exact propagate C.gates (fun g hg => (mono g hg).1) (List.ofFn y) (List.ofFn x) (by simp)
        inclusion C.output (pos p l ((memF _ _).mp pl))
    · rw [decide_eq_false h]
      apply sound x few
      simpa only [memF] using h
  obtain ⟨xs,cost,outputs,binary⟩ := compileRows q N F C hq order degreeF joins mono exactQuery
  let paid (l : Fin N) := Finset.univ.filter fun j : Fin xs.length =>
    1 < (xs.get j).card ∧ xs.get j ⊆ F l
  have perLine (l : Fin N) : q ≤ (paid l).card := by
    have bound := oneOutput N xs binary (F l) (outputs l)
    rw [Fintype.card_subtype] at bound
    change (F l).card ≤ (paid l).card + 1 at bound
    rw [degreeF] at bound
    omega
  have apart : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint paid := by
    intro l _ s _ ne
    apply Finset.disjoint_left.mpr
    intro j jl js
    obtain ⟨large,subL⟩ := (Finset.mem_filter.mp jl).2
    have subS := (Finset.mem_filter.mp js).2.2
    obtain ⟨p,r,hp,hr,diff⟩ := Finset.one_lt_card_iff.mp large
    exact ne ((joins p r diff).unique ⟨subL hp,subL hr⟩ ⟨subS hp,subS hr⟩)
  calc
    N*q = ∑ _l : Fin N, q := by simp
    _ ≤ ∑ l : Fin N, (paid l).card := Finset.sum_le_sum fun l _ => perLine l
    _ = (Finset.univ.biUnion paid).card := (Finset.card_biUnion apart).symm
    _ ≤ xs.length := (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    _ ≤ 100*C.size := cost
