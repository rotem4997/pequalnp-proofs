import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6361

def sub (a b : ℕ) : Prop := a &&& b = a

def inI (p : ℕ × ℕ) (v : ℕ) : Prop := sub p.1 v ∧ sub v p.2

theorem sub_testBit {a b : ℕ} : sub a b ↔ ∀ i, a.testBit i = true → b.testBit i = true := by
  unfold sub
  constructor
  · intro h i hi
    have hb := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_land, hi, Bool.true_and] at hb
    exact hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    cases ha : a.testBit i
    · simp
    · simp [h i ha]

theorem step_and {p q r : ℕ × ℕ} {v w : ℕ}
    (hl : sub p.1 (q.1 &&& r.1)) (hu : sub (q.2 &&& r.2) p.2)
    (hv : inI q v) (hw : inI r w) : inI p (v &&& w) := by
  constructor
  · rw [sub_testBit] at hl ⊢
    intro i hi
    have hqr := hl i hi
    rw [Nat.testBit_land, Bool.and_eq_true] at hqr ⊢
    exact ⟨(sub_testBit.mp hv.1) i hqr.1, (sub_testBit.mp hw.1) i hqr.2⟩
  · rw [sub_testBit] at hu ⊢
    intro i hi
    rw [Nat.testBit_land, Bool.and_eq_true] at hi
    apply hu i
    rw [Nat.testBit_land, Bool.and_eq_true]
    exact ⟨(sub_testBit.mp hv.2) i hi.1, (sub_testBit.mp hw.2) i hi.2⟩

theorem step_or {p q r : ℕ × ℕ} {v w : ℕ}
    (hl : sub p.1 (q.1 ||| r.1)) (hu : sub (q.2 ||| r.2) p.2)
    (hv : inI q v) (hw : inI r w) : inI p (v ||| w) := by
  constructor
  · rw [sub_testBit] at hl ⊢
    intro i hi
    have hqr := hl i hi
    rw [Nat.testBit_lor, Bool.or_eq_true] at hqr ⊢
    rcases hqr with h1 | h2
    · exact Or.inl ((sub_testBit.mp hv.1) i h1)
    · exact Or.inr ((sub_testBit.mp hw.1) i h2)
  · rw [sub_testBit] at hu ⊢
    intro i hi
    rw [Nat.testBit_lor, Bool.or_eq_true] at hi
    apply hu i
    rw [Nat.testBit_lor, Bool.or_eq_true]
    rcases hi with h1 | h2
    · exact Or.inl ((sub_testBit.mp hv.2) i h1)
    · exact Or.inr ((sub_testBit.mp hw.2) i h2)

theorem main : have x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => x1 &&& x2 = x1; have x2 : ℕ × ℕ → ℕ → Prop := fun (x2 : ℕ × ℕ) (x3 : ℕ) => x1 x2.1 x3 ∧ x1 x3 x2.2; have x3 : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Prop := fun (x3 x4 x5 : ℕ × ℕ) => x1 x3.1 (x4.1 &&& x5.1) ∧ x1 (x4.2 &&& x5.2) x3.2 ∨ x1 x3.1 (x4.1 ||| x5.1) ∧ x1 (x4.2 ||| x5.2) x3.2; have x4 : List (ℕ × ℕ) → List (ℕ × ℕ) → Prop := fun (x4 x5 : List (ℕ × ℕ)) => ∀ (x6 : Fin x5.length), ∃ x7 ∈ x4 ++ List.take (↑x6) x5, ∃ x8 ∈ x4 ++ List.take (↑x6) x5, x3 (x5.get x6) x7 x8; have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9; ∀ (x6 : List (ℕ × ℕ)) (x7 : List ℕ) (x8 : List (ℕ × ℕ)), (∀ x9 ∈ x6, ∃ x11 ∈ x7, x2 x9 x11) → x4 x6 x8 → ∃ (x11 : List ℕ), x11.length = x8.length ∧ x5 x7 x11 ∧ ∀ x12 ∈ x6 ++ x8, ∃ x14 ∈ x7 ++ x11, x2 x12 x14 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hbase hsteps
  induction x8 using List.reverseRecOn with
  | nil =>
    refine ⟨[], rfl, ?_, ?_⟩
    · intro idx; exact Fin.elim0 idx
    · simpa using hbase
  | append_singleton xs p ih =>
    have hsteps_xs : x4 x6 xs := by
      intro i
      have hi_lt : (i : ℕ) < (xs ++ [p]).length := by simp
      have h := hsteps ⟨i.val, hi_lt⟩
      have hget : (xs ++ [p]).get ⟨i.val, hi_lt⟩ = xs.get i := by
        simp [List.getElem_append_left i.isLt]
      have htake : List.take i.val (xs ++ [p]) = List.take i.val xs := by
        rw [List.take_append_of_le_length (Nat.le_of_lt i.isLt)]
      simpa only [hget, htake] using h
    obtain ⟨ys, hlen, hys_ok, hcov⟩ := ih hsteps_xs
    have hlast_lt : xs.length < (xs ++ [p]).length := by simp
    have hlast := hsteps ⟨xs.length, hlast_lt⟩
    have hget_last : (xs ++ [p]).get ⟨xs.length, hlast_lt⟩ = p := by simp
    have htake_last : List.take xs.length (xs ++ [p]) = xs := by simp
    rw [hget_last, htake_last] at hlast
    obtain ⟨q, hq, r, hr, hqr⟩ := hlast
    obtain ⟨v, hv, hqv⟩ := hcov q hq
    obtain ⟨w, hw, hrw⟩ := hcov r hr
    rcases hqr with ⟨hl, hu⟩ | ⟨hl, hu⟩
    · refine ⟨ys ++ [v &&& w], by simp [hlen], ?_, ?_⟩
      · intro k
        by_cases hk : k.val < ys.length
        · have h := hys_ok ⟨k.val, hk⟩
          have hgk : (ys ++ [v &&& w]).get k = ys.get ⟨k.val, hk⟩ := by
            simp [List.getElem_append_left hk]
          have htk : List.take k.val (ys ++ [v &&& w]) = List.take k.val ys := by
            rw [List.take_append_of_le_length (Nat.le_of_lt hk)]
          simpa only [hgk, htk] using h
        · have hkeq : k.val = ys.length := by have := k.isLt; simp at this; omega
          have hgk : (ys ++ [v &&& w]).get k = v &&& w := by
            change (ys ++ [v &&& w])[k.val] = v &&& w
            simp [hkeq]
          have htk : List.take k.val (ys ++ [v &&& w]) = ys := by simp [hkeq]
          rw [hgk, htk]
          exact ⟨v, hv, w, hw, Or.inl rfl⟩
      · intro z hz
        rw [← List.append_assoc, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · obtain ⟨u, hu, hzu⟩ := hcov z hz
          exact ⟨u, by rw [← List.append_assoc]; exact List.mem_append_left _ hu, hzu⟩
        · exact ⟨v &&& w, by simp, step_and hl hu hqv hrw⟩
    · refine ⟨ys ++ [v ||| w], by simp [hlen], ?_, ?_⟩
      · intro k
        by_cases hk : k.val < ys.length
        · have h := hys_ok ⟨k.val, hk⟩
          have hgk : (ys ++ [v ||| w]).get k = ys.get ⟨k.val, hk⟩ := by
            simp [List.getElem_append_left hk]
          have htk : List.take k.val (ys ++ [v ||| w]) = List.take k.val ys := by
            rw [List.take_append_of_le_length (Nat.le_of_lt hk)]
          simpa only [hgk, htk] using h
        · have hkeq : k.val = ys.length := by have := k.isLt; simp at this; omega
          have hgk : (ys ++ [v ||| w]).get k = v ||| w := by
            change (ys ++ [v ||| w])[k.val] = v ||| w
            simp [hkeq]
          have htk : List.take k.val (ys ++ [v ||| w]) = ys := by simp [hkeq]
          rw [hgk, htk]
          exact ⟨v, hv, w, hw, Or.inr rfl⟩
      · intro z hz
        rw [← List.append_assoc, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · obtain ⟨u, hu, hzu⟩ := hcov z hz
          exact ⟨u, by rw [← List.append_assoc]; exact List.mem_append_left _ hu, hzu⟩
        · exact ⟨v ||| w, by simp, step_or hl hu hqv hrw⟩

end PEqualNP.Outside.L_meta_6361

theorem PEqualNP.Outside.L_meta_6361 : have x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => x1 &&& x2 = x1; have x2 : ℕ × ℕ → ℕ → Prop := fun (x2 : ℕ × ℕ) (x3 : ℕ) => x1 x2.1 x3 ∧ x1 x3 x2.2; have x3 : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Prop := fun (x3 x4 x5 : ℕ × ℕ) => x1 x3.1 (x4.1 &&& x5.1) ∧ x1 (x4.2 &&& x5.2) x3.2 ∨ x1 x3.1 (x4.1 ||| x5.1) ∧ x1 (x4.2 ||| x5.2) x3.2; have x4 : List (ℕ × ℕ) → List (ℕ × ℕ) → Prop := fun (x4 x5 : List (ℕ × ℕ)) => ∀ (x6 : Fin x5.length), ∃ x7 ∈ x4 ++ List.take (↑x6) x5, ∃ x8 ∈ x4 ++ List.take (↑x6) x5, x3 (x5.get x6) x7 x8; have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9; ∀ (x6 : List (ℕ × ℕ)) (x7 : List ℕ) (x8 : List (ℕ × ℕ)), (∀ x9 ∈ x6, ∃ x11 ∈ x7, x2 x9 x11) → x4 x6 x8 → ∃ (x11 : List ℕ), x11.length = x8.length ∧ x5 x7 x11 ∧ ∀ x12 ∈ x6 ++ x8, ∃ x14 ∈ x7 ++ x11, x2 x12 x14 :=
  PEqualNP.Outside.L_meta_6361.main
