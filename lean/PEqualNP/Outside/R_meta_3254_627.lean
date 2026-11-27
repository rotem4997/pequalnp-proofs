import Mathlib.Data.Set.Card
import Mathlib.Tactic
import PEqualNP.Defs

-- Normalize the trace before the geometric charge. Empty wires are replaced
-- by an input known not to imply the output. Their predecessors can be relabeled
-- to that same input, so the normalization creates no new charged pairs.
theorem PEqualNP.Outside.R_meta_3254_627
    (normalize : ∀ (X Y : Type) (m s o : ℕ) (W : ℕ → Set (X × Y)),
      let hit (U : ℕ → Set (X × Y)) (z : X × Y) : Prop :=
        ∃ i < s, U (m+i) ⊆ U o ∧ z ∈ U (m+i) ∧
          ∃ a b, max a b < m+i ∧ U (m+i) = U a ∩ U b ∧
            ∃ A B, U a = A ×ˢ Set.univ ∧ U b = Set.univ ×ˢ B
      0 < m → (∀ i < m, W i ≠ ∅) → W o ≠ ∅ → ¬ W 0 ⊆ W o →
      (∀ i < s, ∃ a b, max a b < m+i ∧ W (m+i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
      ∃ U : ℕ → Set (X × Y), (∀ i < m, U i = W i) ∧ U o = W o ∧
        (∀ i, U i ≠ ∅) ∧ (∀ i < s, ∃ a b, max a b < m+i ∧
          (U (m+i) = U a ∪ U b ∨ U (m+i) = U a ∩ U b)) ∧
        (∀ z, hit U z → hit W z))
    (cleanLower : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      let B := Fin n → Bool
      let m := n+n
      let atom (i j : Fin n) : Bool := decide (j=i)
      100 < q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (U : ℕ → Set (B × B)),
        o < m+s → (∀ i, U i ≠ ∅) →
        (∀ i : Fin n, U i.val = {z | z.1 i = true} ∧ U (n+i.val) = {z | z.2 i = true}) →
        (∀ i < s, ∃ a b, max a b < m+i ∧ (U (m+i) = U a ∪ U b ∨ U (m+i) = U a ∩ U b)) →
        (∀ p l, I p l → (atom p,atom l) ∈ U o) →
        (∀ L : B, Fintype.card {l // L l = true} ≤ q →
          ((fun p => decide (¬∃ l, I p l ∧ L l = true)), L) ∉ U o) →
        {e : Fin n × Fin n | I e.1 e.2 ∧ ∃ i < s, U (m+i) ⊆ U o ∧ (atom e.1,atom e.2) ∈ U (m+i) ∧
          ∃ a b, max a b < m+i ∧ U (m+i) = U a ∩ U b ∧
            ∃ A C, U a = A ×ˢ Set.univ ∧ U b = Set.univ ×ˢ C}.ncard ≤ 4*s → n*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 → (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) → (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) → (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) → {x19 : Fin x2 × Fin x2 | x3 x19.1 x19.2 ∧ ∃ x20 < x9, x11 (x12 + x20) ⊆ x11 x10 ∧ (x13 x19.1, x13 x19.2) ∈ x11 (x12 + x20) ∧ ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x12 + x20 ∧ x11 (x12 + x20) = x11 x21 ∩ x11 x22 ∧ ∃ (x23 : Set (Fin x2 → Bool)) (x24 : Set (Fin x2 → Bool)), x11 x21 = x23 ×ˢ Set.univ ∧ x11 x22 = Set.univ ×ˢ x24}.ncard ≤ (4 : ℕ) * x9 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q n I d hq hn degrees unique s o W m0 atom ho inputs steps accept reject count
  let B := Fin n → Bool
  let m := n+n
  have hp : 0 < n := by omega
  let zer : Fin n := ⟨0,hp⟩
  have hI : ∀ i < m, W i ≠ ∅ := by
    intro i hi
    have zmem : ((fun _ : Fin n => true), (fun _ : Fin n => true)) ∈ W i := by
      by_cases h : i < n
      · let j : Fin n := ⟨i,h⟩
        change ((fun _ : Fin n => true), (fun _ : Fin n => true)) ∈ W j.val
        rw [(inputs j).1]
        rfl
      · let j : Fin n := ⟨i-n,by dsimp [m] at hi; omega⟩
        have e : i = n+j.val := by dsimp [j]; omega
        rw [e, (inputs j).2]
        rfl
    intro e
    rw [e] at zmem
    exact zmem
  have hO : W o ≠ ∅ := by
    have nc : 0 < Fintype.card {p : Fin n // I p zer} := by rw [degrees zer]; omega
    let z : {p : Fin n // I p zer} := (Fintype.card_pos_iff.mp nc).some
    have h := accept z.val zer z.property
    intro e
    rw [e] at h
    exact h
  have hBad : ¬ W 0 ⊆ W o := by
    intro sub
    have mem : ((fun _ : Fin n => true), (fun _ : Fin n => false)) ∈ W 0 := by
      change ((fun _ : Fin n => true), (fun _ : Fin n => false)) ∈ W zer.val
      rw [(inputs zer).1]
      rfl
    have rej := reject (fun _ => false) (by simp)
    apply rej
    have same : (fun p : Fin n => decide (¬∃ l, I p l ∧ false = true)) = fun _ => true := by
      funext p
      simp
    rw [same]
    exact sub mem
  obtain ⟨U, hPrim, hOut, hLive, hSteps, hHit⟩ := normalize B B m s o W (by dsimp [m]; omega) hI hO hBad steps
  have hInputs : ∀ j : Fin n, U j.val = {z | z.1 j = true} ∧ U (n+j.val) = {z | z.2 j = true} := by
    intro j
    rw [hPrim j.val (by dsimp [m]; have := j.isLt; omega),
        hPrim (n+j.val) (by dsimp [m]; have := j.isLt; omega)]
    exact inputs j
  apply cleanLower q n I hq hn degrees unique s o U ho hLive hInputs hSteps
  · simpa only [hOut] using accept
  · simpa only [hOut] using reject
  · refine (Set.ncard_le_ncard ?_).trans count
    intro e he
    exact ⟨he.1, hHit _ he.2⟩
