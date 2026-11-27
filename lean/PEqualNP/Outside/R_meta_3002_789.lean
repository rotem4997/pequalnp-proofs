import Mathlib
import PEqualNP.Defs

-- One choice bit per gate suffices to realize every minimal sparse-line cover.
-- Orient those bits so that the all-false setting gives exactly the line inputs.
-- The pair tests already cost three times the number of points minus one gates.
set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3002_789
    (linear : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < N+N+s →
      (∀ v < N+N, F v = {{v}}) → (∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j,
        F (N+N+j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) ∨
        F (N+N+j) = F a ∨ F (N+N+j) = {∅} ∨ F (N+N+j) = F a ∪ F b) →
      (∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N+l.val ∈ A) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N, (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T)) → 3*N ≤ s+1)
    (globalChoices : ∀ (m s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < m+s →
      (∀ v < m, F v = {{v}}) → (∀ j < s, ∃ a < m+j, ∃ b < m+j,
        F (m+j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) ∨
        F (m+j) = F a ∨ F (m+j) = {∅} ∨ F (m+j) = F a ∪ F b) →
      ∃ D : (Fin s → Bool) → ℕ → Finset ℕ,
        (∀ z v, v < m → D z v = {v}) ∧ (∀ j : Fin s, ∃ a < m+j.val, ∃ b < m+j.val,
        (∀ z, D z (m+j.val) = D z a ∪ D z b) ∨
        (∀ z, D z (m+j.val) = if z j then D z a else D z b) ∨
        ∀ z, D z (m+j.val) = ∅) ∧
        (∀ z, D z o ∈ F o) ∧ ∀ A ∈ F o, ∃ z, D z o ⊆ A)
    (minimal : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (T : Finset (Fin N)) (A B : Finset ℕ), T.card ≤ q → B ⊆ A →
      (∀ p l : Fin N, I p l → p.val ∈ B ∨ N+l.val ∈ B) →
      (∀ p : Fin N, (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T)) → ∀ p : Fin N, (p.val ∈ B ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ B ↔ p ∉ T))
    (network : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 300 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ),
      o < N+N+s → 3*N ≤ s+1 → (∀ z v, v < N+N → D z v = {v}) →
      (∀ j : Fin s, ∃ a < N+N+j.val, ∃ b < N+N+j.val,
        (∀ z, D z (N+N+j.val) = D z a ∪ D z b) ∨
        (∀ z, D z (N+N+j.val) = if z j then D z a else D z b) ∨
        ∀ z, D z (N+N+j.val) = ∅) →
      (∀ z, ∀ p l : Fin N, I p l → p.val ∈ D z o ∨ N+l.val ∈ D z o) →
      (∀ p : Fin N, p.val ∉ D (fun _ => false) o ∧ N+p.val ∈ D (fun _ => false) o) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ z, ∀ p : Fin N, (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ D z o ↔ p ∉ T)) →
      N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI q200 order degree unique s o F room inputs gates safe saturated
  have count := linear q N I (by omega) order degree unique s o F room inputs gates safe saturated
  by_cases modest : q ≤ 299
  · have product := Nat.mul_le_mul_left N modest
    omega
  · obtain ⟨D, bits, steps, sound, realize⟩ := globalChoices (N+N) s o F room inputs gates
    have chosen (T : Finset (Fin N)) (small : T.card ≤ q) : ∃ z, ∀ p : Fin N,
        (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ D z o ↔ p ∉ T) := by
      obtain ⟨A,inA,spec⟩ := saturated T small
      obtain ⟨z,sub⟩ := realize A inA
      exact ⟨z,minimal q N I degree unique T A (D z o) small sub (safe _ (sound z)) spec⟩
    obtain ⟨base, empty⟩ := chosen ∅ (by simp)
    let flip := fun (z : Fin s → Bool) (j : Fin s) => if base j then !z j else z j
    let norm := fun (z : Fin s → Bool) => D (flip z)
    have twice (z : Fin s → Bool) : flip (flip z) = z := by
      funext j
      cases hb : base j <;> simp [flip,hb]
    have zero : flip (fun _ => false) = base := by
      funext j
      cases hb : base j <;> simp [flip,hb]
    apply network q N I (by omega) order degree unique s o norm room count
    · exact fun z v hv => bits (flip z) v hv
    · intro j
      obtain ⟨a,ha,b,hb,join | choice | unit⟩ := steps j
      · exact ⟨a,ha,b,hb,Or.inl (fun z => join (flip z))⟩
      · cases baseBit : base j with
        | false =>
          refine ⟨a,ha,b,hb,Or.inr (Or.inl (fun z => ?_))⟩
          simpa only [norm,flip,baseBit,Bool.false_eq_true,if_false] using choice (flip z)
        | true =>
          refine ⟨b,hb,a,ha,Or.inr (Or.inl (fun z => ?_))⟩
          have h := choice (flip z)
          change D (flip z) (N + N + j.val) = if z j then D (flip z) b else D (flip z) a
          rw [h]
          have sj : flip z j = !z j := by simp [flip,baseBit]
          cases v : z j <;> simp [sj,v]
      · exact ⟨a,ha,b,hb,Or.inr (Or.inr (fun z => unit (flip z)))⟩
    · exact fun z p l pl => safe _ (sound (flip z)) p l pl
    · intro p
      change p.val ∉ D (flip (fun _ => false)) o ∧ N+p.val ∈ D (flip (fun _ => false)) o
      rw [zero]
      have h := empty p
      simpa using h
    · intro T small
      obtain ⟨z,hz⟩ := chosen T small
      refine ⟨flip z, fun p => ?_⟩
      simpa only [norm, twice] using hz p
