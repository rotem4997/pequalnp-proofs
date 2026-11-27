import Mathlib
import PEqualNP.Defs

-- A primitive intersection rejects every sparse background, but each operand accepts one.
-- Charge the union of flags at these physical intersections. No distinguished output remains.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3002_407
    (hitProgram : ∀ (m s : ℕ) (F : ℕ → Set (Finset ℕ)), (∀ i < m, F i = {{i}}) →
      (∀ j < s, ∃ a < m+j, ∃ b < m+j, F (m+j) = Set.image2 (fun x y : Finset ℕ => x ∪ y) (F a) (F b) ∨
        F (m+j) = F a ∨ F (m+j) = {∅} ∨ F (m+j) = F a ∪ F b) →
      ∃ W : ℕ → Set (Finset ℕ), (∀ w X, X ∈ W w ↔ ∀ A ∈ F w, ¬ Disjoint A X) ∧
        (∀ i < m, W i = {X | i ∈ X}) ∧ ∀ j < s, ∃ a < m+j, ∃ b < m+j,
          W (m+j) ∈ [W a ∪ W b, W a ∩ W b, W a, ∅])
    (primitive : ∀ (α : Type) (m s o : ℕ) (W : ℕ → Set α) (Z : Set α), o < m+s →
      (∀ i < m, ¬ Disjoint (W i) Z) → (∀ j < s, ∃ a < m+j, ∃ b < m+j,
        W (m+j) ∈ [W a ∪ W b, W a ∩ W b, W a, ∅]) → Disjoint (W o) Z →
      ∀ x ∈ W o, ∃ j < s, ∃ a < m+j, ∃ b < m+j, W (m+j) = W a ∩ W b ∧
        ¬ Disjoint (W a) Z ∧ ¬ Disjoint (W b) Z ∧ Disjoint (W (m+j)) Z ∧ x ∈ W (m+j) ∧
        ∀ w < m+j, x ∈ W w → ¬ Disjoint (W w) Z)
    (frontier : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q → N=q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) → (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s : ℕ) (W : ℕ → Set (Finset ℕ)) (Z : Set (Finset ℕ)), let m := N+N
      (∀ i < m, W i = {X | i ∈ X}) → (∀ j < s, ∃ a < m+j, ∃ b < m+j, W (m+j) ∈ [W a ∪ W b,W a ∩ W b,W a,∅]) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ X ∈ Z, ∀ p : Fin N, (p.val ∈ X ↔ ¬ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ X ↔ p ∈ T)) →
      (∀ p l, I p l → ∃ j < s, ∃ a < m+j, ∃ b < m+j, W (m+j) = W a ∩ W b ∧
        ¬ Disjoint (W a) Z ∧ ¬ Disjoint (W b) Z ∧ Disjoint (W (m+j)) Z ∧ {p.val,N+l.val} ∈ W (m+j) ∧
        ∀ w < m+j, {p.val,N+l.val} ∈ W w → ¬ Disjoint (W w) Z) → N*q ≤ 100*s) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI hq hN deg geom s o F room inputs gates safe sat
  obtain ⟨W,hit,raw,ops⟩ := hitProgram (N+N) s F inputs gates
  let P := fun (T : Finset (Fin N)) => (Finset.univ.filter (fun p : Fin N => ¬ ∃ l ∈ T, I p l)).image Fin.val
  let L := fun (T : Finset (Fin N)) => T.image (fun l => N+l.val)
  let mask := fun T => P T ∪ L T
  let Z : Set (Finset ℕ) := {X | ∃ T : Finset (Fin N), T.card ≤ q ∧ mask T = X}
  have spec (T : Finset (Fin N)) (p : Fin N) : (p.val ∈ mask T ↔ ¬ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ mask T ↔ p ∈ T) := by
    have left : p.val ∈ P T ↔ ¬ ∃ l ∈ T, I p l := by
      constructor
      · intro h; obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
        obtain rfl : a=p := Fin.ext e
        exact (Finset.mem_filter.mp ha).2
      · intro h; exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
    have right : N+p.val ∈ L T ↔ p ∈ T := by
      constructor
      · intro h; obtain ⟨a,ha,e⟩ := Finset.mem_image.mp h
        exact (Fin.ext (Nat.add_left_cancel e) : a=p) ▸ ha
      · intro h; exact Finset.mem_image.mpr ⟨p,h,rfl⟩
    have noL : p.val ∉ L T := by intro h; obtain ⟨k,_,hk⟩ := Finset.mem_image.mp h; have := p.isLt; omega
    have noP : N+p.val ∉ P T := by intro h; obtain ⟨k,_,hk⟩ := Finset.mem_image.mp h; have := k.isLt; omega
    simpa only [mask,Finset.mem_union,noL,noP,or_false,false_or] using And.intro left right
  have sparse (T : Finset (Fin N)) (ht : T.card ≤ q) : ∃ X ∈ Z, ∀ p : Fin N, (p.val ∈ X ↔ ¬ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ X ↔ p ∈ T) :=
    ⟨mask T,⟨T,ht,rfl⟩,spec T⟩
  have dirty (i : ℕ) (hi : i<N+N) : ¬ Disjoint (W i) Z := by
    rw [raw i hi,Set.not_disjoint_iff]
    by_cases h : i<N
    · let p : Fin N := ⟨i,h⟩
      exact ⟨mask ∅,(spec ∅ p).1.mpr (by simp),∅,by simp,rfl⟩
    · let l : Fin N := ⟨i-N,by omega⟩
      have eq : N+l.val=i := by dsimp [l]; omega
      exact ⟨mask {l},eq ▸ (spec {l} l).2.mpr (by simp),{l},by simp; omega,rfl⟩
  have clean : Disjoint (W o) Z := by
    apply Set.disjoint_left.mpr
    intro X hm hz
    obtain ⟨T,ht,eq⟩ := hz
    obtain ⟨A,ha,shape⟩ := sat T ht
    apply (hit o X).mp hm A ha
    apply Finset.disjoint_left.mpr
    intro n hn hx
    rw [← eq] at hx
    rcases Finset.mem_union.mp hx with hp|hl
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hp
      exact (spec T p).1.mp hx ((shape p).1.mp hn)
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hl
      exact (shape l).2.mp hn ((spec T l).2.mp hx)
  apply frontier q N I hq hN deg geom s W Z raw ops sparse
  intro p l inc
  apply primitive (Finset ℕ) (N+N) s o W Z room dirty ops clean
  apply (hit o _).mpr
  intro A ha d
  rcases safe A ha p l inc with hp|hl
  · exact Finset.disjoint_left.mp d hp (by simp)
  · exact Finset.disjoint_left.mp d hl (by simp)
