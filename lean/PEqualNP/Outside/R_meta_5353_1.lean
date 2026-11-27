import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_5353_1
    (factor : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → n ≤ C.output →
      (∃ g, C.gates[C.output - n]? = some g ∧ g.op = .and) →
      ∃ (D : Circuit) (a b : ℕ), IsAO2 n D ∧ D.size < C.size ∧
        a < n + D.size ∧ b < n + D.size ∧ ∀ x : List Bool, x.length = n →
          C.eval x = ((D.wires x).getD a false && (D.wires x).getD b false))
    (rules : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      ∀ (A B : Type) (pos : A → List Bool) (neg : B → List Bool),
      (∀ a, (pos a).length = n) → (∀ b, (neg b).length = n) →
      let R (i : ℕ) := ({a | (C.wires (pos a)).getD i false = true} : Set A) ×ˢ
        ({b | (C.wires (neg b)).getD i false = false} : Set B)
      (∀ i < n, R i = {z | (pos z.1).getD i false = true ∧ (neg z.2).getD i false = false}) ∧
      ∀ j < C.size, ∃ u < n+j, ∃ v < n+j, R (n+j) ⊆ R u ∪ R v)
    (geometry : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)), 350 ≤ q →
      N = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      ∀ (s : ℕ) (U : ℕ → Set (Fin N × Fin N)) (V : ℕ → Set (Finset (Fin N))),
      let R i := U i ×ˢ V i
      (∀ i < N+N, R i = {z | (incidenceInput {z.1.1} {z.1.2}).getD i false = true ∧
        (incidenceInput (zeroSet S z.2) z.2).getD i false = false}) →
      (∀ j < s, ∃ u < N+N+j, ∃ v < N+N+j, R (N+N+j) ⊆ R u ∪ R v) →
      (∃ a < N+N+s, ∃ b < N+N+s,
        (∀ l, ∀ p ∈ S l, (p,l) ∈ U a ∩ U b) ∧
        (∀ Y : Finset (Fin N), Y.card ≤ q → Y ∈ V a ∪ V b)) →
      N*q ≤ 100*(s+1)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (350 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * (x1 - (349 : ℕ)) ≤ (100 : ℕ) * x4.size - (349 : ℕ) * x2 := by
  intro q N S C hq order regular uniqueLine model lower _ root positive negative
  obtain ⟨D,a,b,modelD,smaller,ha,hb,eval⟩ := factor _ C model lower root
  let pos (f : Fin N × Fin N) := incidenceInput ({f.1} : Finset (Fin N)) ({f.2} : Finset (Fin N))
  let neg (Y : Finset (Fin N)) := incidenceInput (zeroSet S Y) Y
  let U (i : ℕ) : Set (Fin N × Fin N) := {f | (D.wires (pos f)).getD i false = true}
  let V (i : ℕ) : Set (Finset (Fin N)) := {Y | (D.wires (neg Y)).getD i false = false}
  have length (X Y : Finset (Fin N)) : (incidenceInput X Y).length = N+N := by
    change (List.ofFn _ ++ List.ofFn _).length = _
    simp only [List.length_append,List.length_ofFn]
  obtain ⟨leaves,splits⟩ := rules (N+N) D modelD _ _ pos neg
    (fun _ => length _ _) (fun _ => length _ _)
  have flags (l : Fin N) (p : Fin N) (hp : p ∈ S l) : (p,l) ∈ U a ∩ U b := by
    exact Bool.and_eq_true_iff.mp ((eval _ (length {p} {l})).symm.trans (positive l p hp))
  have cover (Y : Finset (Fin N)) (hy : Y.card ≤ q) : Y ∈ V a ∪ V b := by
    have safe : IsFalseInput S (zeroSet S Y) Y := fun l hl =>
      Finset.disjoint_left.mpr fun p hp hz => (Finset.mem_filter.mp hz).2 l hl hp
    have h := (eval _ (length (zeroSet S Y) Y)).symm.trans (negative _ Y hy safe)
    exact Bool.and_eq_false_iff.mp h
  have count := geometry q N S hq order regular uniqueLine D.size U V leaves splits
    ⟨a,ha,b,hb,flags,cover⟩
  have bound : N*q ≤ 100*C.size := by omega
  rw [Nat.mul_sub, Nat.mul_comm N 349]
  exact Nat.sub_le_sub_right bound _
