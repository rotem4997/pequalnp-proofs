import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6585

def Good (x1 c : List (BitVec 58)) : Prop :=
  ∀ pre v suf, c = pre ++ v :: suf →
    v ∉ x1 ++ pre ∧ v ≠ 0 ∧ v ≠ BitVec.allOnes 58 ∧
      ∃ a ∈ x1 ++ pre, ∃ b ∈ x1 ++ pre, v = a &&& b ∨ v = a ||| b

def Prog (x1 x2 : List (BitVec 58)) : Prop :=
  ∀ pre v suf, x2 = pre ++ v :: suf →
    ∃ a ∈ (0 : BitVec 58) :: BitVec.allOnes 58 :: x1 ++ pre,
      ∃ b ∈ (0 : BitVec 58) :: BitVec.allOnes 58 :: x1 ++ pre, v = a &&& b ∨ v = a ||| b

theorem clos (S : List (BitVec 58)) (a b v : BitVec 58)
    (ha : a = 0 ∨ a = BitVec.allOnes 58 ∨ a ∈ S)
    (hb : b = 0 ∨ b = BitVec.allOnes 58 ∨ b ∈ S)
    (h : v = a &&& b ∨ v = a ||| b) :
    (v = 0 ∨ v = BitVec.allOnes 58 ∨ v ∈ S) ∨ (a ∈ S ∧ b ∈ S) := by
  have e1 : ∀ x : BitVec 58, BitVec.allOnes 58 &&& x = x := fun x => BitVec.allOnes_and
  have e2 : ∀ x : BitVec 58, x &&& BitVec.allOnes 58 = x := fun x => BitVec.and_allOnes
  have e3 : ∀ x : BitVec 58, BitVec.allOnes 58 ||| x = BitVec.allOnes 58 :=
    fun x => BitVec.allOnes_or
  have e4 : ∀ x : BitVec 58, x ||| BitVec.allOnes 58 = BitVec.allOnes 58 :=
    fun x => BitVec.or_allOnes
  generalize BitVec.allOnes 58 = O at *
  rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb <;> rcases h with rfl | rfl <;>
    simp [*]

theorem split_get (l : List (BitVec 58)) (i : Fin l.length) :
    l = l.take i ++ l.get i :: l.drop (i + 1) := by
  simp

theorem key (x1 : List (BitVec 58)) : ∀ x2 : List (BitVec 58), Prog x1 x2 →
    ∃ c : List (BitVec 58), c.length ≤ x2.length ∧
      (∀ v ∈ x2, v ≠ 0 → v ≠ BitVec.allOnes 58 → v ∉ x1 → v ∈ c) ∧ Good x1 c := by
  intro x2
  induction x2 using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], by simp, by simp, ?_⟩
    intro pre v suf h
    simp at h
  | append_singleton l v ih =>
    intro hP
    have hPl : Prog x1 l := by
      intro pre w suf h
      exact hP pre w (suf ++ [v]) (by rw [h]; simp)
    obtain ⟨c, hlen, hcov, hG⟩ := ih hPl
    obtain ⟨a, ha, b, hb, hv⟩ := hP l v [] rfl
    have av : ∀ a, a ∈ (0 : BitVec 58) :: BitVec.allOnes 58 :: x1 ++ l →
        a = 0 ∨ a = BitVec.allOnes 58 ∨ a ∈ x1 ++ c := by
      intro a ha
      by_cases e0 : a = 0
      · exact Or.inl e0
      by_cases e1 : a = BitVec.allOnes 58
      · exact Or.inr (Or.inl e1)
      by_cases e2 : a ∈ x1
      · exact Or.inr (Or.inr (List.mem_append_left _ e2))
      have h3 : a ∈ l := by
        simp only [List.cons_append, List.mem_cons, List.mem_append] at ha
        tauto
      exact Or.inr (Or.inr (List.mem_append_right _ (hcov a h3 e0 e1 e2)))
    by_cases hd : v = 0 ∨ v = BitVec.allOnes 58 ∨ v ∈ x1 ++ c
    · refine ⟨c, by simp; omega, ?_, hG⟩
      intro w hw w0 w1 w2
      rcases List.mem_append.1 hw with hw | hw
      · exact hcov w hw w0 w1 w2
      · have : w = v := by simpa using hw
        subst this
        rcases hd with h | h | h
        · exact absurd h w0
        · exact absurd h w1
        · rcases List.mem_append.1 h with h | h
          · exact absurd h w2
          · exact h
    · have hab : a ∈ x1 ++ c ∧ b ∈ x1 ++ c := by
        rcases clos (x1 ++ c) a b v (av a ha) (av b hb) hv with h | h
        · exact absurd h hd
        · exact h
      refine ⟨c ++ [v], by simp; omega, ?_, ?_⟩
      · intro w hw w0 w1 w2
        rcases List.mem_append.1 hw with hw | hw
        · exact List.mem_append_left _ (hcov w hw w0 w1 w2)
        · exact List.mem_append_right _ hw
      · intro pre w suf h
        rcases List.eq_nil_or_concat suf with rfl | ⟨L, e, rfl⟩
        · obtain ⟨h1, h2⟩ := List.append_inj' h rfl
          have h3 : v = w := by simpa using h2
          subst h1
          subst h3
          refine ⟨fun hm => hd (Or.inr (Or.inr hm)), fun hm => hd (Or.inl hm),
            fun hm => hd (Or.inr (Or.inl hm)), a, hab.1, b, hab.2, hv⟩
        · have h' : c ++ [v] = (pre ++ w :: L) ++ [e] := by rw [h]; simp
          obtain ⟨h1, _⟩ := List.append_inj' h' rfl
          exact hG pre w L h1

theorem main (x1 x2 : List (BitVec 58)) (x3 : BitVec 58)
    (hP : Prog x1 x2) (hmem : x3 ∈ x2) (h0 : x3 ≠ 0) (h1 : x3 ≠ BitVec.allOnes 58)
    (hx : x3 ∉ x1) :
    ∃ x10 : List (BitVec 58), x10.length ≤ x2.length ∧ x10.getLast? = Option.some x3 ∧
      Good x1 x10 := by
  obtain ⟨c, hlen, hcov, hG⟩ := key x1 x2 hP
  obtain ⟨s, t, rfl⟩ := List.append_of_mem (hcov x3 hmem h0 h1 hx)
  refine ⟨s ++ [x3], ?_, by simp, ?_⟩
  · simp at hlen ⊢
    omega
  · intro pre w suf h
    exact hG pre w (suf ++ t) (by
      have : s ++ x3 :: t = (s ++ [x3]) ++ t := by simp
      rw [this, h]; simp)

end PEqualNP.Outside.L_meta_6585

theorem PEqualNP.Outside.L_meta_6585 : ∀ (x1 x2 : List (BitVec (58 : ℕ))) (x3 : BitVec (58 : ℕ)),   have x4 : List (BitVec (58 : ℕ)) := (0 : BitVec (58 : ℕ)) :: BitVec.allOnes (58 : ℕ) :: x1;   (∀ (x5 : Fin x2.length),       have x6 : List (BitVec (58 : ℕ)) := x4 ++ List.take (↑x5) x2;       ∃ x7 ∈ x6, ∃ x8 ∈ x6, x2.get x5 = x7 &&& x8 ∨ x2.get x5 = x7 ||| x8) →     x3 ∈ x4 ++ x2 →       x3 ≠ (0 : BitVec (58 : ℕ)) →         x3 ≠ BitVec.allOnes (58 : ℕ) →           x3 ∉ x1 →             ∃ (x10 : List (BitVec (58 : ℕ))),               x10.length ≤ x2.length ∧                 x10.getLast? = Option.some x3 ∧                   ∀ (x11 : Fin x10.length),                     have x12 : List (BitVec (58 : ℕ)) := x1 ++ List.take (↑x11) x10;                     x10.get x11 ∉ x12 ∧ x10.get x11 ≠ (0 : BitVec (58 : ℕ)) ∧ x10.get x11 ≠ BitVec.allOnes (58 : ℕ) ∧ ∃ x13 ∈ x12, ∃ x14 ∈ x12, x10.get x11 = x13 &&& x14 ∨ x10.get x11 = x13 ||| x14 := by
  intro x1 x2 x3 x4 h hmem h0 h1 hx
  have hP : PEqualNP.Outside.L_meta_6585.Prog x1 x2 := by
    intro pre v suf e
    subst e
    have h2 := h ⟨pre.length, by simp⟩
    simpa [x4] using h2
  have hm : x3 ∈ x2 := by
    simp only [x4, List.cons_append, List.mem_cons, List.mem_append] at hmem
    tauto
  obtain ⟨x10, hl, hlast, hG⟩ := PEqualNP.Outside.L_meta_6585.main x1 x2 x3 hP hm h0 h1 hx
  refine ⟨x10, hl, hlast, ?_⟩
  intro x11
  exact hG _ _ _ (PEqualNP.Outside.L_meta_6585.split_get x10 x11)
