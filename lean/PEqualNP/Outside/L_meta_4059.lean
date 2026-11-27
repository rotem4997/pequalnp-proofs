import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4059

-- Points are 0..12, lines are 13..25. Point p lies on line l when p - l is in 0, 1, 3, 9 mod 13.
def inD (n : ℕ) : Bool := n == 0 || n == 1 || n == 3 || n == 9

def rel (u v : Fin 26) : Bool :=
  (decide (u.val < 13) && decide (13 ≤ v.val) && inD ((u.val + 26 - v.val) % 13)) ||
  (decide (v.val < 13) && decide (13 ≤ u.val) && inD ((v.val + 26 - u.val) % 13))

-- Three automorphisms: the shift by one, the polarity, and one collineation fixing point 0.
def fwd : List (List ℕ) := [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 13], [13, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], [0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 15, 20, 23, 24, 19, 16, 22, 21, 17, 18, 25]]
def bwd : List (List ℕ) := [[12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24], [13, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], [0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 15, 20, 23, 24, 19, 16, 22, 21, 17, 18, 25]]
def gf (i : ℕ) (u : Fin 26) : Fin 26 := Fin.ofNat 26 ((fwd.getD i []).getD u.val 0)
def gb (i : ℕ) (u : Fin 26) : Fin 26 := Fin.ofNat 26 ((bwd.getD i []).getD u.val 0)

-- For each ordered pair, which automorphism to apply next on the way to a base pair.
def tbl : List ℕ := [0, 0, 0, 0, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 2, 2, 2, 0, 0, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 2, 0, 1, 1, 2, 1, 1, 0, 0, 1, 0, 1, 0, 2, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 2, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 2, 2, 0, 0, 1, 0, 1, 1, 1, 0, 0, 2, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 0, 0, 2, 1, 1, 2, 1, 0, 2, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 2, 1, 0, 2, 2, 0, 1, 0, 0, 2, 1, 1, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 1, 2, 0, 0, 1, 2, 2, 0, 0, 2, 1, 2, 0, 2, 1, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0, 1, 2, 2, 0, 0, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 0, 0, 2, 2, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 0, 0, 2, 1, 0, 1, 1, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 2, 2, 0, 2, 0, 0, 1, 1, 0, 1, 0, 2, 2, 0, 0, 2, 0, 0, 0, 2, 2, 2, 0, 1, 2, 0, 2, 2, 0, 1, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 0, 0, 2, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 2, 2, 0, 1, 2, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 2, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 2, 0, 0, 1, 0, 0, 2, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 2, 2, 1, 0, 1, 2, 0, 0, 2, 0, 2, 2, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 1, 1, 0, 0, 2, 2, 2, 1, 1, 1, 0, 1, 0, 0, 1, 2, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 2, 2, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 1, 1, 2, 1, 2, 2, 2, 0, 0, 1, 2, 0, 1, 2, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 2, 0, 1, 0, 2, 0, 0, 2, 1, 1, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 2, 2, 1, 2, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 1, 2, 1, 1, 1, 2, 2, 0, 1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 1, 2, 2, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 2, 0, 1, 2, 0, 0, 1, 1, 1, 2, 0, 0, 2, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 2, 1, 1, 0, 0]
def nxt (a b : Fin 26) : ℕ := tbl.getD (26 * a.val + b.val) 0

def base (a b : Fin 26) : Bool := a == 0 && (b == 0 || b == 1 || b == 14)

def reach : ℕ → Fin 26 → Fin 26 → Bool
  | 0, a, b => base a b
  | n + 1, a, b => base a b || reach n (gf (nxt a b) a) (gf (nxt a b) b)

theorem left_ok : ∀ i : Fin 3, ∀ u : Fin 26, gb i.val (gf i.val u) = u := by decide +kernel
theorem right_ok : ∀ i : Fin 3, ∀ u : Fin 26, gf i.val (gb i.val u) = u := by decide +kernel
theorem rel_ok : ∀ i : Fin 3, ∀ u v : Fin 26, rel (gf i.val u) (gf i.val v) = rel u v := by
  decide +kernel
theorem nxt_lt : ∀ a b : Fin 26, nxt a b < 3 := by decide +kernel
theorem reach_ok : ∀ a b : Fin 26, rel a b = false → reach 11 a b = true := by decide +kernel
theorem adj_rel : ∀ u v : Fin 26, (∃ (x5 : Fin 13) (x6 : Fin 13), (x5 = x6 ∨ x5 = x6 + (1 : Fin 13) ∨ x5 = x6 + (3 : Fin 13) ∨ x5 = x6 + (9 : Fin 13)) ∧ (u = Fin.castAdd 13 x5 ∧ v = Fin.natAdd 13 x6 ∨ v = Fin.castAdd 13 x5 ∧ u = Fin.natAdd 13 x6)) ↔ rel u v = true := by
  decide +kernel

def perm (i : Fin 3) : Equiv.Perm (Fin 26) := ⟨gf i.val, gb i.val, left_ok i, right_ok i⟩

theorem main (G : SimpleGraph (Fin 26)) (h : ∀ u v : Fin 26, G.Adj u v ↔ rel u v = true) :
    ∀ (n : ℕ) (a b : Fin 26), reach n a b = true →
      ∃ φ : G ≃g G, φ a = 0 ∧ (φ b = 0 ∨ φ b = 1 ∨ φ b = 14) := by
  have iso : ∀ i : Fin 3, ∃ ψ : G ≃g G, ∀ u, ψ u = gf i.val u := by
    intro i
    refine ⟨⟨perm i, ?_⟩, fun u => rfl⟩
    intro u v
    rw [h, h]
    change rel (gf i.val u) (gf i.val v) = true ↔ _
    rw [rel_ok]
  have hbase : ∀ a b : Fin 26, base a b = true →
      ∃ φ : G ≃g G, φ a = 0 ∧ (φ b = 0 ∨ φ b = 1 ∨ φ b = 14) := by
    intro a b hb
    refine ⟨RelIso.refl _, ?_⟩
    simp only [base, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb
    obtain ⟨h0, h1⟩ := hb
    refine ⟨h0, ?_⟩
    rcases h1 with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  intro n
  induction n with
  | zero =>
    intro a b hr
    exact hbase a b hr
  | succ n ih =>
    intro a b hr
    simp only [reach, Bool.or_eq_true] at hr
    rcases hr with hb | hr
    · exact hbase a b hb
    · obtain ⟨φ, h1, h2⟩ := ih _ _ hr
      obtain ⟨ψ, hψ⟩ := iso ⟨nxt a b, nxt_lt a b⟩
      refine ⟨ψ.trans φ, ?_, ?_⟩
      · change φ (ψ a) = 0
        rw [hψ]
        exact h1
      · change φ (ψ b) = 0 ∨ φ (ψ b) = 1 ∨ φ (ψ b) = 14
        rw [hψ]
        exact h2

end PEqualNP.Outside.L_meta_4059

theorem PEqualNP.Outside.L_meta_4059 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 x5 : Fin (26 : ℕ)), ¬x1.Adj x4 x5 → ∃ (x7 : x1 ≃g x1), x7 x4 = (0 : Fin (26 : ℕ)) ∧ (x7 x5 = (0 : Fin (26 : ℕ)) ∨ x7 x5 = (1 : Fin (26 : ℕ)) ∨ x7 x5 = (14 : Fin (26 : ℕ))) := by
  intro G _ h a b hn
  have hG : ∀ u v : Fin 26, G.Adj u v ↔ PEqualNP.Outside.L_meta_4059.rel u v = true :=
    fun u v => (h u v).trans (PEqualNP.Outside.L_meta_4059.adj_rel u v)
  have hr : PEqualNP.Outside.L_meta_4059.rel a b = false := by
    cases hc : PEqualNP.Outside.L_meta_4059.rel a b
    · rfl
    · exact absurd ((hG a b).2 hc) hn
  exact PEqualNP.Outside.L_meta_4059.main G hG 11 a b
    (PEqualNP.Outside.L_meta_4059.reach_ok a b hr)
