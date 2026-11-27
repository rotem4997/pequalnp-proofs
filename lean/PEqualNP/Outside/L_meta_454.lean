import Mathlib
import PEqualNP.Defs

private theorem slotBlock_eq {w i j r s : ℕ}
    (hr : r < w) (hs : s < w) (h : i * w + r = j * w + s) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hle := Nat.mul_le_mul_right w (show i + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega
  · exact heq
  · have hle := Nat.mul_le_mul_right w (show j + 1 ≤ i by omega)
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega

theorem PEqualNP.Outside.L_meta_454 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ u : Fin m, (S.neighborSet (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) u)).ncard = (H.neighborSet u).ncard := by
  intro m k H Q S hk hQ hS u
  classical
  let d := 2 * k
  let U := Fin.castLE (Nat.le_add_right m (d * (m * m))) u
  let base (a b : Fin m) := m + d * (a.val * m + b.val)
  let left (v : Fin m) := if u < v then u else v
  let right (v : Fin m) := if u < v then v else u
  let offset (v : Fin m) := if u < v then 0 else d - 1
  let code (v : Fin m) := base (left v) (right v) + offset v
  have hd : 0 < d := by dsimp [d]; omega
  have hU : U.val = u.val := rfl
  have code_forward (v : Fin m) (hv : u < v) : code v = base u v := by
    simp [code, left, right, offset, hv]
  have code_backward (v : Fin m) (hv : ¬ u < v) :
      code v = base v u + (d - 1) := by
    simp [code, left, right, offset, hv]
  have offset_lt (v : Fin m) : offset v < d := by
    dsimp [offset]
    split <;> omega
  have code_inj : Function.Injective code := by
    intro v w heq
    have h : (left v).val * m + (right v).val = (left w).val * m + (right w).val := by
      apply slotBlock_eq (offset_lt v) (offset_lt w)
      simpa [code, base, Nat.mul_comm d, Nat.add_assoc] using heq
    have hl : left v = left w := Fin.ext (slotBlock_eq (right v).isLt (right w).isLt h)
    have hr : right v = right w := by
      apply Fin.ext
      rw [hl] at h
      omega
    by_cases hv : u < v <;> by_cases hw : u < w <;>
      simp [left, right, hv, hw] at hl hr <;> grind
  have code_lt (v : Fin m) : code v < m + d * (m * m) := by
    have hl := (left v).isLt
    have hr := (right v).isLt
    have hmul := Nat.mul_le_mul_right m (show (left v).val + 1 ≤ m by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    have hi : (left v).val * m + (right v).val + 1 ≤ m * m := by omega
    have hm := Nat.mul_le_mul_left d hi
    rw [Nat.mul_add, Nat.mul_one] at hm
    have ho := offset_lt v
    dsimp [code, base]
    omega
  have q_orig {a b : Fin m} {p : ℕ} (hq : Q a b p U) :
      (p = 0 ∧ a = u) ∨ (p = d + 1 ∧ b = u) := by
    rcases (hQ a b p U).mp hq with h | h | h
    · exact Or.inl ⟨h.1, Fin.ext (h.2.symm.trans hU)⟩
    · exact Or.inr ⟨h.1, Fin.ext (h.2.symm.trans hU)⟩
    · have hu := u.isLt
      rw [hU] at h
      omega
  have q_inner {a b : Fin m} {p : ℕ} {x : Fin (m + d * (m * m))}
      (hp : 1 ≤ p) (hp' : p ≤ d) :
      Q a b p x ↔ x.val + 1 = base a b + p := by
    rw [hQ]
    change ((p = 0 ∧ x.val = a.val) ∨ (p = d + 1 ∧ x.val = b.val) ∨
      (1 ≤ p ∧ p ≤ d ∧ x.val + 1 = base a b + p)) ↔ _
    constructor
    · rintro (h | h | h)
      · omega
      · omega
      · exact h.2.2
    · exact fun h => Or.inr (Or.inr ⟨hp, hp', h⟩)
  have hImage : Fin.val '' S.neighborSet U = code '' H.neighborSet u := by
    ext n
    constructor
    · rintro ⟨x, hx, rfl⟩
      change S.Adj U x at hx
      obtain ⟨a, b, hab, hadj, p, hp, hpath⟩ := (hS U x).mp hx
      change p ≤ d at hp
      rcases hpath with ⟨hstart, hnext⟩ | ⟨hstart, hnext⟩
      · rcases q_orig hstart with ⟨rfl, rfl⟩ | ⟨hp', _⟩
        · refine ⟨b, hadj, ?_⟩
          rw [code_forward b hab]
          have h := (q_inner (by omega) (by omega)).mp hnext
          omega
        · omega
      · rcases q_orig hnext with ⟨hp', _⟩ | ⟨hp', rfl⟩
        · omega
        · have hp_eq : p = d := by omega
          subst p
          refine ⟨a, hadj.symm, ?_⟩
          rw [code_backward a (not_lt_of_gt hab)]
          have h := (q_inner (by omega) (by omega)).mp hstart
          omega
    · rintro ⟨v, hv, rfl⟩
      change H.Adj u v at hv
      let x : Fin (m + d * (m * m)) := ⟨code v, code_lt v⟩
      refine ⟨x, ?_, rfl⟩
      change S.Adj U x
      apply (hS U x).mpr
      by_cases hvlt : u < v
      · refine ⟨u, v, hvlt, hv, 0, Nat.zero_le _, Or.inl ⟨?_, ?_⟩⟩
        · exact (hQ u v 0 U).mpr (Or.inl ⟨rfl, hU⟩)
        · apply (q_inner (by omega) (by omega)).mpr
          change code v + 1 = base u v + 1
          rw [code_forward v hvlt]
      · have hlt : v < u := lt_of_le_of_ne (le_of_not_gt hvlt) hv.ne.symm
        refine ⟨v, u, hlt, hv.symm, d, le_rfl, Or.inr ⟨?_, ?_⟩⟩
        · apply (q_inner (by omega) (by omega)).mpr
          change code v + 1 = base v u + d
          rw [code_backward v hvlt]
          omega
        · exact (hQ v u (d + 1) U).mpr (Or.inr (Or.inl ⟨rfl, hU⟩))
  calc
    (S.neighborSet U).ncard = (Fin.val '' S.neighborSet U).ncard :=
      (Set.ncard_image_of_injective _ Fin.val_injective).symm
    _ = (code '' H.neighborSet u).ncard := congrArg Set.ncard hImage
    _ = (H.neighborSet u).ncard := Set.ncard_image_of_injective _ code_inj
