import Mathlib
import PEqualNP.Defs

/-!
Every edge set has a cut containing at least half of it. Averaging over all two-colourings:
for an edge s(x, y) with x different from y, flipping the colour of x is an involution on
colourings that swaps cut and uncut, so summed over all colourings the number of cut edges of
the set equals the number of uncut ones. Hence some colouring cuts at least as many edges as it
leaves uncut, and its cut edges are the required subset.
-/

namespace PEqualNP.Outside.L_meta_7029

def cutB {n : ℕ} (c : Fin n → Bool) (e : Sym2 (Fin n)) : Bool :=
  Sym2.lift ⟨fun x y => c x != c y, fun x y => by
    show (c x != c y) = (c y != c x)
    cases c x <;> cases c y <;> rfl⟩ e

theorem cutB_mk {n : ℕ} (c : Fin n → Bool) (x y : Fin n) : cutB c s(x, y) = (c x != c y) := rfl

def flip {n : ℕ} (x : Fin n) (c : Fin n → Bool) : Fin n → Bool := Function.update c x (!c x)

theorem flip_flip {n : ℕ} (x : Fin n) (c : Fin n → Bool) : flip x (flip x c) = c := by
  funext z
  by_cases hz : z = x
  · subst hz; simp [flip]
  · simp [flip, Function.update_of_ne hz]

theorem cutB_flip {n : ℕ} (c : Fin n → Bool) (x y : Fin n) (hxy : x ≠ y) :
    cutB (flip x c) s(x, y) = !cutB c s(x, y) := by
  rw [cutB_mk, cutB_mk]
  simp only [flip, Function.update_self, Function.update_of_ne hxy.symm]
  cases c x <;> cases c y <;> rfl

theorem per_edge {n : ℕ} (e : Sym2 (Fin n)) (he : ¬e.IsDiag) :
    (∑ c : Fin n → Bool, if cutB c e = true then 1 else 0) =
      ∑ c : Fin n → Bool, if ¬cutB c e = true then 1 else 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := by simpa using he
    apply Finset.sum_nbij' (flip x) (flip x) (by simp) (by simp)
      (fun c _ => flip_flip x c) (fun c _ => flip_flip x c)
    intro c _
    rw [cutB_flip c x y hxy]
    cases cutB c s(x, y) <;> rfl

theorem exists_good {n : ℕ} (S : Finset (Sym2 (Fin n))) (hS : ∀ e ∈ S, ¬e.IsDiag) :
    ∃ c : Fin n → Bool, (S.filter fun e => ¬cutB c e = true).card ≤
      (S.filter fun e => cutB c e = true).card := by
  by_contra hne
  have hne' : ∀ c : Fin n → Bool, (S.filter fun e => cutB c e = true).card <
      (S.filter fun e => ¬cutB c e = true).card := fun c => Nat.lt_of_not_le (fun h => hne ⟨c, h⟩)
  have hlt := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
    (fun c _ => hne' c)
  have heq : (∑ c : Fin n → Bool, (S.filter fun e => cutB c e = true).card) =
      ∑ c : Fin n → Bool, (S.filter fun e => ¬cutB c e = true).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    exact Finset.sum_congr rfl (fun e he => per_edge e (hS e he))
  omega

end PEqualNP.Outside.L_meta_7029

theorem PEqualNP.Outside.L_meta_7029 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∀ x4 ⊆ x2.edgeFinset, ∃ (x6 : Finset (Sym2 (Fin x1))) (x7 : Fin x1 → Bool), x6 ⊆ x4 ∧ x4.card ≤ (2 : ℕ) * x6.card ∧ ∀ (x8 x9 : Fin x1), s(x8, x9) ∈ x6 → x7 x8 ≠ x7 x9 := by
  intro n G _ S hS
  have hd : ∀ e ∈ S, ¬e.IsDiag := by
    intro e he
    have := hS he
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 this)
  obtain ⟨c, hc⟩ := PEqualNP.Outside.L_meta_7029.exists_good S hd
  refine ⟨S.filter fun e => PEqualNP.Outside.L_meta_7029.cutB c e = true, c,
    Finset.filter_subset _ _, ?_, ?_⟩
  · have := Finset.card_filter_add_card_filter_not
      (s := S) (fun e => PEqualNP.Outside.L_meta_7029.cutB c e = true)
    omega
  · intro x y hxy
    rw [Finset.mem_filter, PEqualNP.Outside.L_meta_7029.cutB_mk] at hxy
    simpa using hxy.2
