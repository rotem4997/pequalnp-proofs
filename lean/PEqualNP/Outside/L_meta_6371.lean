import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6371

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Ls : List ℕ := [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600, 16256]

def E : List (Fin 7 × Fin 7) := [(0, 0), (1, 0), (3, 0), (1, 1), (2, 1), (4, 1), (2, 2), (3, 2), (5, 2), (3, 3), (4, 3), (6, 3), (4, 4), (5, 4), (0, 4), (5, 5), (6, 5), (1, 5), (6, 6), (0, 6), (2, 6)]

theorem mem : ∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → (p, l) ∈ E := by decide

theorem mem2 : ∀ e ∈ E, e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3 := by decide

def fl (m : ℕ) : Bool := E.all fun e => !(m.testBit e.1 && m.testBit (7 + e.2))

theorem chk : ((List.range 16384).all fun m => !(fl m) || (List.range 14).any (fun i => !(m.testBit i) && fl (m ||| 2 ^ i)) || Ls.contains m) = true := by
  decide +kernel

theorem ofb (x : Fin 14 → Bool) : ∃ X < 16384, ∀ i : Fin 14, X.testBit i = x i := by
  refine ⟨(BitVec.ofFnLE x).toNat, by simpa using (BitVec.ofFnLE x).isLt, fun i => ?_⟩
  have := BitVec.getLsbD_ofFnLE x i
  simpa [BitVec.getLsbD] using this

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6371

theorem PEqualNP.Outside.L_meta_6371 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ))) ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (14 : ℕ) → Bool),   ¬x1 x2 →     (∀ (x4 : Fin (14 : ℕ) → Bool), (∀ (x5 : Fin (14 : ℕ)), x2 x5 = Bool.true → x4 x5 = Bool.true) → x2 ≠ x4 → x1 x4) →       ∃ (x5 : Fin (37 : ℕ)),         x2 = fun (x6 : Fin (14 : ℕ)) =>           ((have x7 : List ℕ :=                     have x7 : List ℕ :=                       have x7 : List ℕ := [(11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)];                       (8488 : ℕ) :: (8722 : ℕ) :: (9250 : ℕ) :: (9632 : ℕ) :: (10250 : ℕ) :: x7;                     have x8 : List ℕ := (5889 : ℕ) :: (6156 : ℕ) :: (7300 : ℕ) :: (8250 : ℕ) :: (8368 : ℕ) :: x7;                     (4244 : ℕ) :: (4361 : ℕ) :: (4625 : ℕ) :: (5125 : ℕ) :: x8;                   have x8 : List ℕ :=                     have x8 : List ℕ := (2376 : ℕ) :: (2626 : ℕ) :: (3008 : ℕ) :: (3078 : ℕ) :: (4125 : ℕ) :: x7;                     (1313 : ℕ) :: (1539 : ℕ) :: (2126 : ℕ) :: (2244 : ℕ) :: x8;                   have x9 : List ℕ := (595 : ℕ) :: (720 : ℕ) :: (833 : ℕ) :: (1063 : ℕ) :: (1188 : ℕ) :: x8;                   (127 : ℕ) :: (244 : ℕ) :: (361 : ℕ) :: (480 : ℕ) :: x9).getD                 ↑x5 (0 : ℕ)).testBit             ↑x6 := by
  intro R x hx hmax
  obtain ⟨M, hM, hMb⟩ := PEqualNP.Outside.L_meta_6371.ofb x
  have c := PEqualNP.Outside.L_meta_6371.chk
  rw [List.all_eq_true] at c
  have c := c M (List.mem_range.2 hM)
  have fl : ∀ (m : ℕ) (y : Fin 14 → Bool), (∀ i : Fin 14, m.testBit i = y i) → (PEqualNP.Outside.L_meta_6371.fl m = true ↔ ¬R y) := by
    intro m y hy
    rw [PEqualNP.Outside.L_meta_6371.fl, List.all_eq_true]
    constructor
    · rintro h ⟨p, l, hpl, h1, h2⟩
      have := h (p, l) (PEqualNP.Outside.L_meta_6371.mem p l hpl)
      rw [Bool.not_eq_true', Bool.and_eq_false_iff] at this
      have e1 := hy (Fin.castAdd 7 p)
      have e2 := hy (Fin.natAdd 7 l)
      rw [h1] at e1
      rw [h2] at e2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at e1 e2
      rcases this with h | h
      · rw [e1] at h; cases h
      · rw [e2] at h; cases h
    · intro h e he
      rw [Bool.not_eq_true', ← Bool.not_eq_true, Bool.and_eq_true]
      rintro ⟨h1, h2⟩
      refine h ⟨e.1, e.2, PEqualNP.Outside.L_meta_6371.mem2 e he, ?_, ?_⟩
      · rw [← hy]; exact h1
      · rw [← hy]; exact h2
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at c
  rcases c with (c | c) | c
  · have := (fl M x hMb).2 hx
    rw [c] at this; cases this
  · exfalso
    rw [List.any_eq_true] at c
    obtain ⟨i, hi, hc⟩ := c
    rw [List.mem_range] at hi
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hb : ∀ k : Fin 14, (M ||| 2 ^ i).testBit k = (Function.update x ⟨i, hi⟩ true) k := by
      intro k
      rw [Nat.testBit_or, hMb, Nat.testBit_two_pow]
      by_cases hk : k = ⟨i, hi⟩
      · subst hk; simp
      · rw [Function.update_of_ne hk]
        have : i ≠ (k : ℕ) := fun h => hk (Fin.ext h.symm)
        simp [this]
    refine (fl _ _ hb).1 hc2 (hmax _ ?_ ?_)
    · intro k hk
      by_cases hk2 : k = ⟨i, hi⟩
      · subst hk2; simp
      · rw [Function.update_of_ne hk2]; exact hk
    · intro h
      have := congrFun h ⟨i, hi⟩
      rw [Function.update_self, ← hMb] at this
      simp only at this
      rw [hc1] at this; cases this
  · have hm : M ∈ PEqualNP.Outside.L_meta_6371.Ls := by simpa using c
    obtain ⟨k, hk, e⟩ := List.getElem_of_mem hm
    have hk' : k < 37 := hk
    refine ⟨⟨k, hk'⟩, funext fun i => ?_⟩
    have e2 : PEqualNP.Outside.L_meta_6371.Ls.getD k 0 = M := by rw [← e]; exact List.getD_eq_getElem _ _ hk
    change x i = (PEqualNP.Outside.L_meta_6371.Ls.getD k 0).testBit i
    rw [e2, hMb]
