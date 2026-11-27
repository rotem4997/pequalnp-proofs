import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328_aux

def G (L : List ℕ) (x : ℕ) : Prop := ∃ a ∈ L, ∃ b ∈ L, x = a &&& b ∨ x = a ||| b

def P (B Q : List ℕ) : Prop := ∀ i : Fin Q.length, G (B ++ List.take (↑i) Q) (Q.get i)

def Inv (x3 r : List ℕ) : Prop := P x3 r ∧ r.Nodup ∧ ∀ a ∈ r, a ∉ x3

theorem G_mono {L L' : List ℕ} {x : ℕ} (h : ∀ a ∈ L, a ∈ L') (hG : G L x) : G L' x := by
  obtain ⟨a, ha, b, hb, hab⟩ := hG
  exact ⟨a, h a ha, b, h b hb, hab⟩

theorem P_snoc {B Q : List ℕ} {y : ℕ} (hP : P B Q) (hG : G (B ++ Q) y) : P B (Q ++ [y]) := by
  rintro ⟨i, hi⟩
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i Q.length with h | h
  · have h1 := hP ⟨i, h⟩
    simpa [List.take_append_of_le_length (Nat.le_of_lt h), List.getElem_append_left h] using h1
  · have h2 : i = Q.length := by omega
    subst h2
    simpa using hG

theorem conv {B Q : List ℕ} (hP : P B Q) : ∀ (l1 : List ℕ) (y : ℕ) (l2 : List ℕ),
    Q = l1 ++ y :: l2 → G (B ++ l1) y := by
  intro l1 y l2 h
  subst h
  have h1 := hP ⟨l1.length, by simp⟩
  simpa using h1

theorem step {x3 acc B : List ℕ} {y : ℕ} (hI : Inv x3 acc) (hB : ∀ a ∈ B, a ∈ x3 ++ acc)
    (hG : G B y) : ∃ r, Inv x3 r ∧ r.length ≤ acc.length + 1 ∧ ∀ a ∈ B ++ [y], a ∈ x3 ++ r := by
  by_cases hy : y ∈ x3 ∨ y ∈ acc
  · refine ⟨acc, hI, by omega, ?_⟩
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · exact hB a ha
    · subst ha
      simpa using hy
  · have hy1 : y ∉ x3 := fun h => hy (Or.inl h)
    have hy2 : y ∉ acc := fun h => hy (Or.inr h)
    refine ⟨acc ++ [y], ⟨P_snoc hI.1 (G_mono hB hG), ?_, ?_⟩, by simp, ?_⟩
    · exact List.Nodup.append hI.2.1 (List.nodup_singleton y) (by simpa using hy2)
    · intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · exact hI.2.2 a ha
      · subst ha
        exact hy1
    · intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · have h3 := hB a ha
        simp only [List.mem_append] at h3
        simp only [List.mem_append, List.mem_singleton]
        tauto
      · subst ha
        simp

theorem main (x3 : List ℕ) : ∀ (ys acc B : List ℕ), Inv x3 acc → (∀ a ∈ B, a ∈ x3 ++ acc) →
    (∀ (l1 : List ℕ) (y : ℕ) (l2 : List ℕ), ys = l1 ++ y :: l2 → G (B ++ l1) y) →
    ∃ r, Inv x3 r ∧ r.length ≤ acc.length + ys.length ∧ ∀ a ∈ B ++ ys, a ∈ x3 ++ r := by
  intro ys
  induction ys with
  | nil =>
    intro acc B hI hB _
    exact ⟨acc, hI, by simp, by simpa using hB⟩
  | cons y ys ih =>
    intro acc B hI hB hH
    have hG : G B y := by
      have h1 := hH [] y ys rfl
      simpa using h1
    obtain ⟨r1, hI1, hl1, hB1⟩ := step hI hB hG
    have hH2 : ∀ (l1 : List ℕ) (z : ℕ) (l2 : List ℕ), ys = l1 ++ z :: l2 → G (B ++ [y] ++ l1) z := by
      intro l1 z l2 h
      have h1 := hH (y :: l1) z l2 (by rw [h]; rfl)
      simpa using h1
    obtain ⟨r, hIr, hlr, hBr⟩ := ih r1 (B ++ [y]) hI1 hB1 hH2
    refine ⟨r, hIr, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro a ha
      apply hBr
      simpa using ha

end PEqualNP.Outside.L_meta_3328_aux

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro x1 x2 x3 x4 x5 x6 h5 h4 h6 h56
  have hI0 : PEqualNP.Outside.L_meta_3328_aux.Inv x3 [] :=
    ⟨fun i => absurd i.2 (by simp), List.nodup_nil, by simp⟩
  obtain ⟨r1, hI1, hl1, hB1⟩ := PEqualNP.Outside.L_meta_3328_aux.step (B := x3) (y := x4) hI0
    (by simp) h4
  have hB1b : ∀ a ∈ x4 :: x3, a ∈ x3 ++ r1 := by
    intro a ha
    apply hB1
    simp only [List.mem_cons] at ha
    simp only [List.mem_append, List.mem_singleton]
    tauto
  obtain ⟨r2, hI2, hl2, hB2⟩ := PEqualNP.Outside.L_meta_3328_aux.main x3 x6 r1 (x4 :: x3) hI1 hB1b
    (PEqualNP.Outside.L_meta_3328_aux.conv h6)
  obtain ⟨r3, hI3, hl3, hB3⟩ := PEqualNP.Outside.L_meta_3328_aux.step (y := x5) hI2 hB2 h56
  refine ⟨r3, ?_, hI3.2.1, hI3.2.2, ?_, hI3.1⟩
  · simp only [List.length_nil] at hl1
    omega
  · have h7 := hB3 x5 (by simp)
    simp only [List.mem_append] at h7
    tauto
