import Mathlib
import PEqualNP.Defs

-- Compile each gate to the rectangle of incident flags and sparse-line tests it separates.
-- The remaining bound concerns rectangle covers by two earlier rectangles, with no switch histories.
theorem PEqualNP.Outside.R_meta_3769_719
  (compile : ∀ (m s : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ), (∀ z v, v < m → D z v={v}) → (∀ j : Fin s, ∃ a < m+j.val, ∃ b < m+j.val, (∀ z, D z (m+j.val)=D z a ∪ D z b) ∨ (∀ z, D z (m+j.val)=if z j=true then D z a else D z b) ∨ ∀ z, D z (m+j.val)=∅) → let F := fun v => {A : Set ℕ | ∃ z, ∀ u∈D z v, u∈A}; ∀ j : Fin s, ∃ a < m+j.val, ∃ b < m+j.val, F (m+j.val)=F a ∩ F b ∨ F (m+j.val)=F a ∪ F b ∨ F (m+j.val)=Set.univ)
  (separator : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 300 ≤ q → N=q^2+q+1 → (∀ l, Fintype.card {p // I p l}=q+1) → (∀ p r, p≠r → ∃! l, I p l ∧ I r l) → ∀ (s o : ℕ) (X : ℕ → Set (Fin N × Fin N)) (Y : ℕ → Set (Finset (Fin N))), o < N+N+s → 3*N ≤ s+1 → (∀ v < N+N, ∀ e∈X v, ∀ T∈Y v, (v=e.1.val ∧ ∃ l∈T, I e.1 l) ∨ (v=N+e.2.val ∧ e.2∉T)) → (∀ j : Fin s, ∃ a < N+N+j.val, ∃ b < N+N+j.val, (X (N+N+j.val)).prod (Y (N+N+j.val)) ⊆ (X a).prod (Y a) ∪ (X b).prod (Y b)) → (∀ p l,I p l → (p,l)∈X o) → (∀ T : Finset (Fin N), T.card ≤ q → T∈Y o) → N*q ≤ 100*s) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ), x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) → (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) → (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15, (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨ (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨ ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) → (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) → (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2), (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI hq hN degree join s o D bound lin inputs gates safe base realize
  let F := fun v => {A : Set ℕ | ∃ z, ∀ u∈D z v, u∈A}
  let bad (e : Fin N × Fin N) : Set ℕ := ({e.1.val,N+e.2.val} : Set ℕ)ᶜ
  let allow (T : Finset (Fin N)) : Set ℕ := {v | (∀ p : Fin N, v=p.val → ∃ l∈T, I p l) ∧ (∀ l : Fin N, v=N+l.val → l∉T)}
  let X := fun v => {e | bad e ∉ F v}
  let Y := fun v => {T | allow T ∈ F v}
  have leaf v (hv : v < N+N) (A : Set ℕ) : A∈F v ↔ v∈A := by
    constructor
    · rintro ⟨z,h⟩; exact h v (by simp [inputs z v hv])
    · intro hx; refine ⟨fun _ => false,?_⟩; simpa [inputs _ v hv] using hx
  apply separator q N I hq hN degree join s o X Y bound lin
  · intro v hv e he T hT
    have hy := (leaf v hv (allow T)).mp hT
    have hx : v∉bad e := fun h => he ((leaf v hv _).mpr h)
    have either : v=e.1.val ∨ v=N+e.2.val := Classical.not_not.mp hx
    rcases either with hp|hl
    · exact .inl ⟨hp,hy.1 _ hp⟩
    · exact .inr ⟨hl,hy.2 _ hl⟩
  · intro j; obtain ⟨a,ha,b,hb,op⟩ := compile _ _ D inputs gates j
    refine ⟨a,ha,b,hb,?_⟩; rintro ⟨e,T⟩ ⟨hx,hy⟩
    change bad e ∉ F (N+N+j.val) at hx; change allow T ∈ F (N+N+j.val) at hy
    change (bad e ∉ F a ∧ allow T ∈ F a) ∨ (bad e ∉ F b ∧ allow T ∈ F b)
    rcases op with op|op|op <;> change F (N+N+j.val)=_ at op <;> rw [op] at hx hy
    · change ¬ (_ ∧ _) at hx; change _ ∧ _ at hy; tauto
    · change ¬ (_ ∨ _) at hx; change _ ∨ _ at hy; tauto
    · exact (hx trivial).elim
  · intro p l edge; rintro ⟨z,h⟩; rcases safe z p l edge with left|right
    · exact h _ left (by simp)
    · exact h _ right (by simp)
  · intro T hT; obtain ⟨z,h⟩ := realize T hT; refine ⟨z,?_⟩
    intro v hv; exact ⟨fun p e => (h p).1.mp (e ▸ hv),fun l e => (h l).2.mp (e ▸ hv)⟩
