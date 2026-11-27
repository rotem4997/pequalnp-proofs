import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7394_aux

def inD (n : ℕ) : Bool := n == 0 || n == 1 || n == 3 || n == 9

def R (a b : Fin 13) : Bool := inD ((a.val + 13 - b.val) % 13)

def u (p : Fin 13 → Bool) (y : Fin 13) : Bool := !(p y || p (y + 1) || p (y + 3) || p (y + 9))

def F (p : Fin 13 → Bool) : Bool :=
  ([13, 23, 34, 45, 86, 127, 182] : List ℕ).contains
      (14 * (List.finRange 13).countP p + (List.finRange 13).countP (u p)) ==
  ((List.finRange 13).all (fun x => p x || (List.finRange 13).any (fun y => u p y && R x y)) &&
   ((List.finRange 13).any (fun c => (List.finRange 13).all (fun x => !p x || R x c)) ||
    (List.finRange 13).any (fun c => (List.finRange 13).all (fun y => !u p y || R c y))))

def Ls : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (Ls n).flatMap (fun l => [false :: l, true :: l])

def mk (l : List Bool) : Fin 13 → Bool := fun i => l.getD i.val false

set_option maxRecDepth 100000 in
theorem all_ok : ((Ls 13).all fun l => F (mk l)) = true := by decide +kernel

theorem mem_Ls : ∀ (n : ℕ) (l : List Bool), l.length = n → l ∈ Ls n := by
  intro n
  induction n with
  | zero => intro l h; simp [Ls, List.length_eq_zero_iff.1 h]
  | succ n ih =>
    intro l h
    cases l with
    | nil => simp at h
    | cons b l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [Ls, List.mem_flatMap]
      exact ⟨l, ih l h, by cases b <;> simp⟩

theorem F_all (p : Fin 13 → Bool) : F p = true := by
  have h := List.all_eq_true.1 all_ok ((List.finRange 13).map p) (mem_Ls 13 _ (by simp))
  have e : mk ((List.finRange 13).map p) = p := by
    funext i
    simp [mk, List.getD_eq_getElem?_getD]
  rwa [e] at h

theorem hR (x y : Fin 13) : R x y = true ↔ x = y ∨ x = y + 1 ∨ x = y + 3 ∨ x = y + 9 := by
  revert x y; decide

theorem hR1 (x y : Fin 13) :
    R x y = true ↔ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), x = y + d := by
  revert x y; decide

theorem hR2 (x y : Fin 13) : R x y = true ↔ ((x - y : Fin 13) : ℕ) ∈ ([0, 1, 3, 9] : List ℕ) := by
  revert x y; decide

theorem hu (S : Finset (Fin 13)) (y : Fin 13) :
    u (fun i => decide (i ∈ S)) y = true ↔ ∀ x ∈ S, ¬ R x y = true := by
  simp only [u, hR]
  constructor
  · intro h x hx hx2
    rcases hx2 with rfl | rfl | rfl | rfl <;> simp_all
  · intro h
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro hm <;> exact h _ hm (by simp)

end PEqualNP.Outside.L_meta_7394_aux

open PEqualNP.Outside.L_meta_7394_aux in
theorem PEqualNP.Outside.L_meta_7394 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => (14 : ℕ) * x4.card + List.countP (fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, ↑(x6 - x5) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.finRange (13 : ℕ)) ∈ [(13 : ℕ), (23 : ℕ), (34 : ℕ), (45 : ℕ), (86 : ℕ), (127 : ℕ), (182 : ℕ)]; ∀ (x5 : Finset (Fin (13 : ℕ))), x4 x5 ↔ (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) ∧ ((∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x3 x5 x7 → x2 x6 x7) := by
  intro x1 x2 x3 x4 S
  have hF := F_all (fun i => decide (i ∈ S))
  have hc : S.card = (List.finRange 13).countP (fun i => decide (i ∈ S)) := by
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((List.nodup_finRange 13).filter _)]
    congr 1; ext i; simp
  have hc2 : List.countP (fun (x5 : Fin 13) => decide (∀ x6 ∈ S, ↑(x6 - x5) ∉ [(0 : ℕ), 1, 3, 9]))
      (List.finRange 13) = (List.finRange 13).countP (u fun i => decide (i ∈ S)) := by
    congr 1; funext y
    rw [Bool.eq_iff_iff, hu]
    simp [hR2]
  show _ ↔ _
  simp only [x4, x3, x2, x1, ← hR1]
  rw [hc, hc2]
  simp only [F, beq_iff_eq] at hF
  rw [← List.elem_iff]
  change ([13, 23, 34, 45, 86, 127, 182] : List ℕ).contains _ = true ↔ _
  rw [hF]
  simp only [List.all_eq_true, List.any_eq_true, List.mem_finRange, true_and, Bool.or_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, ← Bool.not_eq_true, hu]
  simp only [or_iff_not_imp_left, not_not, forall_const]
