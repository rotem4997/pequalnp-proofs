import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4676

open PEqualNP.CircuitLowerBounds Fin.CommRing

def U : Finset (Fin 13) := {1, 3, 9}

def tau (c t : Fin 13) (i : ℕ) : ℕ :=
  if h : i < 13 then (c * ⟨i, h⟩ + t).val
  else if h2 : i < 26 then 13 + (c * ⟨i - 13, by omega⟩ + t).val else i

def reps : List (List ℕ) :=
  [[], [0], [13], [0, 1], [0, 2], [0, 13], [0, 14], [0, 15], [0, 17], [0, 20], [13, 14], [13, 15]]

def tbl : List (List (ℕ × ℕ × ℕ)) :=
  [[(1, 0, 1), (1, 0, 3), (1, 0, 4), (9, 0, 3), (3, 1, 3), (3, 0, 4), (9, 0, 4), (9, 2, 4), (3, 2, 4), (3, 0, 3), (9, 1, 3), (1, 2, 4), (1, 1, 3), (1, 0, 5), (1, 0, 6), (1, 0, 7), (9, 0, 6), (1, 0, 8), (3, 0, 7), (9, 0, 7), (1, 0, 9), (9, 0, 9), (3, 0, 6), (3, 0, 8), (3, 0, 9), (9, 0, 8)],
   [(1, 0, 3), (1, 12, 1), (1, 12, 3), (1, 12, 4), (9, 4, 3), (3, 11, 3), (3, 10, 4), (9, 4, 4), (9, 6, 4), (3, 12, 4), (3, 10, 3), (9, 5, 3), (1, 1, 4), (9, 4, 8), (1, 12, 5), (1, 12, 6), (1, 12, 7), (9, 4, 6), (1, 12, 8), (3, 10, 7), (9, 4, 7), (1, 12, 9), (9, 4, 9), (3, 10, 6), (3, 10, 8), (3, 10, 9)],
   [(1, 0, 4), (1, 12, 3), (1, 11, 1), (1, 11, 3), (1, 11, 4), (9, 8, 3), (3, 8, 3), (3, 7, 4), (9, 8, 4), (9, 10, 4), (3, 9, 4), (3, 7, 3), (9, 9, 3), (3, 7, 9), (9, 8, 8), (1, 11, 5), (1, 11, 6), (1, 11, 7), (9, 8, 6), (1, 11, 8), (3, 7, 7), (9, 8, 7), (1, 11, 9), (9, 8, 9), (3, 7, 6), (3, 7, 8)],
   [(9, 0, 3), (1, 12, 4), (1, 11, 3), (1, 10, 1), (1, 10, 3), (1, 10, 4), (9, 12, 3), (3, 5, 3), (3, 4, 4), (9, 12, 4), (9, 1, 4), (3, 6, 4), (3, 4, 3), (3, 4, 8), (3, 4, 9), (9, 12, 8), (1, 10, 5), (1, 10, 6), (1, 10, 7), (9, 12, 6), (1, 10, 8), (3, 4, 7), (9, 12, 7), (1, 10, 9), (9, 12, 9), (3, 4, 6)],
   [(3, 1, 3), (9, 4, 3), (1, 11, 4), (1, 10, 3), (1, 9, 1), (1, 9, 3), (1, 9, 4), (9, 3, 3), (3, 2, 3), (3, 1, 4), (9, 3, 4), (9, 5, 4), (3, 3, 4), (3, 1, 6), (3, 1, 8), (3, 1, 9), (9, 3, 8), (1, 9, 5), (1, 9, 6), (1, 9, 7), (9, 3, 6), (1, 9, 8), (3, 1, 7), (9, 3, 7), (1, 9, 9), (9, 3, 9)],
   [(3, 0, 4), (3, 11, 3), (9, 8, 3), (1, 10, 4), (1, 9, 3), (1, 8, 1), (1, 8, 3), (1, 8, 4), (9, 7, 3), (3, 12, 3), (3, 11, 4), (9, 7, 4), (9, 9, 4), (9, 7, 9), (3, 11, 6), (3, 11, 8), (3, 11, 9), (9, 7, 8), (1, 8, 5), (1, 8, 6), (1, 8, 7), (9, 7, 6), (1, 8, 8), (3, 11, 7), (9, 7, 7), (1, 8, 9)],
   [(9, 0, 4), (3, 10, 4), (3, 8, 3), (9, 12, 3), (1, 9, 4), (1, 8, 3), (1, 7, 1), (1, 7, 3), (1, 7, 4), (9, 11, 3), (3, 9, 3), (3, 8, 4), (9, 11, 4), (1, 7, 9), (9, 11, 9), (3, 8, 6), (3, 8, 8), (3, 8, 9), (9, 11, 8), (1, 7, 5), (1, 7, 6), (1, 7, 7), (9, 11, 6), (1, 7, 8), (3, 8, 7), (9, 11, 7)],
   [(9, 2, 4), (9, 4, 4), (3, 7, 4), (3, 5, 3), (9, 3, 3), (1, 8, 4), (1, 7, 3), (1, 6, 1), (1, 6, 3), (1, 6, 4), (9, 2, 3), (3, 6, 3), (3, 5, 4), (9, 2, 7), (1, 6, 9), (9, 2, 9), (3, 5, 6), (3, 5, 8), (3, 5, 9), (9, 2, 8), (1, 6, 5), (1, 6, 6), (1, 6, 7), (9, 2, 6), (1, 6, 8), (3, 5, 7)],
   [(3, 2, 4), (9, 6, 4), (9, 8, 4), (3, 4, 4), (3, 2, 3), (9, 7, 3), (1, 7, 4), (1, 6, 3), (1, 5, 1), (1, 5, 3), (1, 5, 4), (9, 6, 3), (3, 3, 3), (3, 2, 7), (9, 6, 7), (1, 5, 9), (9, 6, 9), (3, 2, 6), (3, 2, 8), (3, 2, 9), (9, 6, 8), (1, 5, 5), (1, 5, 6), (1, 5, 7), (9, 6, 6), (1, 5, 8)],
   [(3, 0, 3), (3, 12, 4), (9, 10, 4), (9, 12, 4), (3, 1, 4), (3, 12, 3), (9, 11, 3), (1, 6, 4), (1, 5, 3), (1, 4, 1), (1, 4, 3), (1, 4, 4), (9, 10, 3), (1, 4, 8), (3, 12, 7), (9, 10, 7), (1, 4, 9), (9, 10, 9), (3, 12, 6), (3, 12, 8), (3, 12, 9), (9, 10, 8), (1, 4, 5), (1, 4, 6), (1, 4, 7), (9, 10, 6)],
   [(9, 1, 3), (3, 10, 3), (3, 9, 4), (9, 1, 4), (9, 3, 4), (3, 11, 4), (3, 9, 3), (9, 2, 3), (1, 5, 4), (1, 4, 3), (1, 3, 1), (1, 3, 3), (1, 3, 4), (9, 1, 6), (1, 3, 8), (3, 9, 7), (9, 1, 7), (1, 3, 9), (9, 1, 9), (3, 9, 6), (3, 9, 8), (3, 9, 9), (9, 1, 8), (1, 3, 5), (1, 3, 6), (1, 3, 7)],
   [(1, 2, 4), (9, 5, 3), (3, 7, 3), (3, 6, 4), (9, 5, 4), (9, 7, 4), (3, 8, 4), (3, 6, 3), (9, 6, 3), (1, 4, 4), (1, 3, 3), (1, 2, 1), (1, 2, 3), (1, 2, 7), (9, 5, 6), (1, 2, 8), (3, 6, 7), (9, 5, 7), (1, 2, 9), (9, 5, 9), (3, 6, 6), (3, 6, 8), (3, 6, 9), (9, 5, 8), (1, 2, 5), (1, 2, 6)],
   [(1, 1, 3), (1, 1, 4), (9, 9, 3), (3, 4, 3), (3, 3, 4), (9, 9, 4), (9, 11, 4), (3, 5, 4), (3, 3, 3), (9, 10, 3), (1, 3, 4), (1, 2, 3), (1, 1, 1), (1, 1, 6), (1, 1, 7), (9, 9, 6), (1, 1, 8), (3, 3, 7), (9, 9, 7), (1, 1, 9), (9, 9, 9), (3, 3, 6), (3, 3, 8), (3, 3, 9), (9, 9, 8), (1, 1, 5)],
   [(1, 0, 5), (9, 4, 8), (3, 7, 9), (3, 4, 8), (3, 1, 6), (9, 7, 9), (1, 7, 9), (9, 2, 7), (3, 2, 7), (1, 4, 8), (9, 1, 6), (1, 2, 7), (1, 1, 6), (1, 0, 2), (1, 0, 10), (1, 0, 11), (9, 0, 10), (3, 1, 10), (3, 0, 11), (9, 0, 11), (9, 2, 11), (3, 2, 11), (3, 0, 10), (9, 1, 10), (1, 2, 11), (1, 1, 10)],
   [(1, 0, 6), (1, 12, 5), (9, 8, 8), (3, 4, 9), (3, 1, 8), (3, 11, 6), (9, 11, 9), (1, 6, 9), (9, 6, 7), (3, 12, 7), (1, 3, 8), (9, 5, 6), (1, 1, 7), (1, 0, 10), (1, 12, 2), (1, 12, 10), (1, 12, 11), (9, 4, 10), (3, 11, 10), (3, 10, 11), (9, 4, 11), (9, 6, 11), (3, 12, 11), (3, 10, 10), (9, 5, 10), (1, 1, 11)],
   [(1, 0, 7), (1, 12, 6), (1, 11, 5), (9, 12, 8), (3, 1, 9), (3, 11, 8), (3, 8, 6), (9, 2, 9), (1, 5, 9), (9, 10, 7), (3, 9, 7), (1, 2, 8), (9, 9, 6), (1, 0, 11), (1, 12, 10), (1, 11, 2), (1, 11, 10), (1, 11, 11), (9, 8, 10), (3, 8, 10), (3, 7, 11), (9, 8, 11), (9, 10, 11), (3, 9, 11), (3, 7, 10), (9, 9, 10)],
   [(9, 0, 6), (1, 12, 7), (1, 11, 6), (1, 10, 5), (9, 3, 8), (3, 11, 9), (3, 8, 8), (3, 5, 6), (9, 6, 9), (1, 4, 9), (9, 1, 7), (3, 6, 7), (1, 1, 8), (9, 0, 10), (1, 12, 11), (1, 11, 10), (1, 10, 2), (1, 10, 10), (1, 10, 11), (9, 12, 10), (3, 5, 10), (3, 4, 11), (9, 12, 11), (9, 1, 11), (3, 6, 11), (3, 4, 10)],
   [(1, 0, 8), (9, 4, 6), (1, 11, 7), (1, 10, 6), (1, 9, 5), (9, 7, 8), (3, 8, 9), (3, 5, 8), (3, 2, 6), (9, 10, 9), (1, 3, 9), (9, 5, 7), (3, 3, 7), (3, 1, 10), (9, 4, 10), (1, 11, 11), (1, 10, 10), (1, 9, 2), (1, 9, 10), (1, 9, 11), (9, 3, 10), (3, 2, 10), (3, 1, 11), (9, 3, 11), (9, 5, 11), (3, 3, 11)],
   [(3, 0, 7), (1, 12, 8), (9, 8, 6), (1, 10, 7), (1, 9, 6), (1, 8, 5), (9, 11, 8), (3, 5, 9), (3, 2, 8), (3, 12, 6), (9, 1, 9), (1, 2, 9), (9, 9, 7), (3, 0, 11), (3, 11, 10), (9, 8, 10), (1, 10, 11), (1, 9, 10), (1, 8, 2), (1, 8, 10), (1, 8, 11), (9, 7, 10), (3, 12, 10), (3, 11, 11), (9, 7, 11), (9, 9, 11)],
   [(9, 0, 7), (3, 10, 7), (1, 11, 8), (9, 12, 6), (1, 9, 7), (1, 8, 6), (1, 7, 5), (9, 2, 8), (3, 2, 9), (3, 12, 8), (3, 9, 6), (9, 5, 9), (1, 1, 9), (9, 0, 11), (3, 10, 11), (3, 8, 10), (9, 12, 10), (1, 9, 11), (1, 8, 10), (1, 7, 2), (1, 7, 10), (1, 7, 11), (9, 11, 10), (3, 9, 10), (3, 8, 11), (9, 11, 11)],
   [(1, 0, 9), (9, 4, 7), (3, 7, 7), (1, 10, 8), (9, 3, 6), (1, 8, 7), (1, 7, 6), (1, 6, 5), (9, 6, 8), (3, 12, 9), (3, 9, 8), (3, 6, 6), (9, 9, 9), (9, 2, 11), (9, 4, 11), (3, 7, 11), (3, 5, 10), (9, 3, 10), (1, 8, 11), (1, 7, 10), (1, 6, 2), (1, 6, 10), (1, 6, 11), (9, 2, 10), (3, 6, 10), (3, 5, 11)],
   [(9, 0, 9), (1, 12, 9), (9, 8, 7), (3, 4, 7), (1, 9, 8), (9, 7, 6), (1, 7, 7), (1, 6, 6), (1, 5, 5), (9, 10, 8), (3, 9, 9), (3, 6, 8), (3, 3, 6), (3, 2, 11), (9, 6, 11), (9, 8, 11), (3, 4, 11), (3, 2, 10), (9, 7, 10), (1, 7, 11), (1, 6, 10), (1, 5, 2), (1, 5, 10), (1, 5, 11), (9, 6, 10), (3, 3, 10)],
   [(3, 0, 6), (9, 4, 9), (1, 11, 9), (9, 12, 7), (3, 1, 7), (1, 8, 8), (9, 11, 6), (1, 6, 7), (1, 5, 6), (1, 4, 5), (9, 1, 8), (3, 6, 9), (3, 3, 8), (3, 0, 10), (3, 12, 11), (9, 10, 11), (9, 12, 11), (3, 1, 11), (3, 12, 10), (9, 11, 10), (1, 6, 11), (1, 5, 10), (1, 4, 2), (1, 4, 10), (1, 4, 11), (9, 10, 10)],
   [(3, 0, 8), (3, 10, 6), (9, 8, 9), (1, 10, 9), (9, 3, 7), (3, 11, 7), (1, 7, 8), (9, 2, 6), (1, 5, 7), (1, 4, 6), (1, 3, 5), (9, 5, 8), (3, 3, 9), (9, 1, 10), (3, 10, 10), (3, 9, 11), (9, 1, 11), (9, 3, 11), (3, 11, 11), (3, 9, 10), (9, 2, 10), (1, 5, 11), (1, 4, 10), (1, 3, 2), (1, 3, 10), (1, 3, 11)],
   [(3, 0, 9), (3, 10, 8), (3, 7, 6), (9, 12, 9), (1, 9, 9), (9, 7, 7), (3, 8, 7), (1, 6, 8), (9, 6, 6), (1, 4, 7), (1, 3, 6), (1, 2, 5), (9, 9, 8), (1, 2, 11), (9, 5, 10), (3, 7, 10), (3, 6, 11), (9, 5, 11), (9, 7, 11), (3, 8, 11), (3, 6, 10), (9, 6, 10), (1, 4, 11), (1, 3, 10), (1, 2, 2), (1, 2, 10)],
   [(9, 0, 8), (3, 10, 9), (3, 7, 8), (3, 4, 6), (9, 3, 9), (1, 8, 9), (9, 11, 7), (3, 5, 7), (1, 5, 8), (9, 10, 6), (1, 3, 7), (1, 2, 6), (1, 1, 5), (1, 1, 10), (1, 1, 11), (9, 9, 10), (3, 4, 10), (3, 3, 11), (9, 9, 11), (9, 11, 11), (3, 5, 11), (3, 3, 10), (9, 10, 10), (1, 3, 11), (1, 2, 10), (1, 1, 2)]]

def ok (a b : ℕ) : Bool :=
  match (tbl.getD a []).getD b (1, 0, 0) with
  | (c, t, k) =>
    decide ((Fin.ofNat 13 c) ∈ U) &&
    decide (tau (Fin.ofNat 13 c) (Fin.ofNat 13 t) a ∈ reps.getD k []) &&
    decide (tau (Fin.ofNat 13 c) (Fin.ofNat 13 t) b ∈ reps.getD k []) &&
    decide (∀ j ∈ reps.getD k [], j = tau (Fin.ofNat 13 c) (Fin.ofNat 13 t) a ∨
      j = tau (Fin.ofNat 13 c) (Fin.ofNat 13 t) b)

theorem ok_all : ∀ a < 26, ∀ b < 26, ok a b = true := by decide


def D : Finset (Fin 13) := {0, 1, 3, 9}

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mapG (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def mapC (ρ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapG ρ), ρ C.output⟩

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then x else false := by
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h1,
      List.getElem_append_left h1]
  · subst h2
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem run (ρ : ℕ → ℕ) (N0 : ℕ)
    (hρ : ∀ k, N0 ≤ k → ∀ i, (ρ i < k ↔ i < k) ∧ (ρ i = k ↔ i = k)) (gs : List Gate) :
    ∀ a b : List Bool, N0 ≤ a.length → b.length = a.length →
      (∀ i, b.getD (ρ i) false = a.getD i false) →
      ∀ i, ((gs.map (mapG ρ)).foldl stepW b).getD (ρ i) false =
        (gs.foldl stepW a).getD i false := by
  induction gs with
  | nil => intro a b _ _ h i; exact h i
  | cons g gs ih =>
    intro a b ha hlen h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hval : (mapG ρ g).op.eval ((mapG ρ g).inputs.map fun i => b.getD i false)
        = g.op.eval (g.inputs.map fun i => a.getD i false) := by
      simp only [mapG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    apply ih
    · simp [stepW]; omega
    · simp [stepW]; omega
    · intro i
      simp only [stepW]
      rw [getD_snoc, getD_snoc, hval, hlen]
      obtain ⟨hA, hB⟩ := hρ a.length ha i
      by_cases h1 : i < a.length
      · rw [if_pos (hA.2 h1), if_pos h1]
        exact h i
      · rw [if_neg (fun h' => h1 (hA.1 h')), if_neg h1]
        by_cases h2 : i = a.length
        · rw [if_pos (hB.2 h2), if_pos h2]
        · rw [if_neg (fun h' => h2 (hB.1 h')), if_neg h2]

theorem eval_map (ρ : ℕ → ℕ) (N0 : ℕ)
    (hρ : ∀ k, N0 ≤ k → ∀ i, (ρ i < k ↔ i < k) ∧ (ρ i = k ↔ i = k)) (C : Circuit)
    (a b : List Bool) (ha : N0 ≤ a.length) (hlen : b.length = a.length)
    (h : ∀ i, b.getD (ρ i) false = a.getD i false) :
    (mapC ρ C).eval b = C.eval a :=
  run ρ N0 hρ C.gates a b ha hlen h C.output

theorem tau_lt (c t : Fin 13) (i : ℕ) (hi : i < 26) : tau c t i < 26 := by
  unfold tau
  by_cases h : i < 13
  · rw [dif_pos h]
    have := (c * ⟨i, h⟩ + t).isLt
    omega
  · rw [dif_neg h, dif_pos hi]
    have := (c * ⟨i - 13, by omega⟩ + t).isLt
    omega

theorem tau_ge (c t : Fin 13) (i : ℕ) (hi : 26 ≤ i) : tau c t i = i := by
  unfold tau
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem tau_prop (c t : Fin 13) :
    ∀ k, 26 ≤ k → ∀ i, (tau c t i < k ↔ i < k) ∧ (tau c t i = k ↔ i = k) := by
  intro k hk i
  by_cases hi : i < 26
  · have := tau_lt c t i hi
    constructor <;> constructor <;> intro <;> omega
  · rw [tau_ge c t i (by omega)]
    exact ⟨Iff.rfl, Iff.rfl⟩

theorem gd (P L : Fin 13 → Bool) (k : ℕ) :
    (List.ofFn P ++ List.ofFn L).getD k false =
      if h : k < 13 then P ⟨k, h⟩ else if h2 : k < 26 then L ⟨k - 13, by omega⟩ else false := by
  by_cases h : k < 13
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_ofFn]
  · rw [dif_neg h]
    by_cases h2 : k < 26
    · rw [dif_pos h2, List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn]
    · rw [dif_neg h2, List.getD_eq_default _ _ (by simp; omega)]

theorem rel (c t : Fin 13) (P L P' L' : Fin 13 → Bool) (hP : ∀ x, P (c * x + t) = P' x)
    (hL : ∀ x, L (c * x + t) = L' x) (i : ℕ) :
    (List.ofFn P ++ List.ofFn L).getD (tau c t i) false =
      (List.ofFn P' ++ List.ofFn L').getD i false := by
  rw [gd, gd]
  by_cases h : i < 13
  · have e : tau c t i = (c * ⟨i, h⟩ + t).val := by
      unfold tau
      rw [dif_pos h]
    rw [e, dif_pos (Fin.isLt _), dif_pos h, ← hP]
  · by_cases h2 : i < 26
    · have e : tau c t i = 13 + (c * ⟨i - 13, by omega⟩ + t).val := by
        unfold tau
        rw [dif_neg h, dif_pos h2]
      have hv := (c * ⟨i - 13, by omega⟩ + t).isLt
      rw [dif_neg h, dif_pos h2, e, dif_neg (by omega), dif_pos (by omega), ← hL]
      congr 1
      ext
      simp
    · rw [tau_ge c t i (by omega)]
      simp only [dif_neg h, dif_neg h2]

theorem U_cube : ∀ c ∈ U, c ^ 3 = 1 := by decide

theorem D_inv : ∀ c ∈ U, ∀ d : Fin 13, c * d ∈ D ↔ d ∈ D := by decide

theorem af_sub (c t x y : Fin 13) : (c * x + t) - (c * y + t) = c * (x - y) := by ring

theorem af_surj (c t : Fin 13) (hc : c ∈ U) (x : Fin 13) : c * (c ^ 2 * (x - t)) + t = x := by
  have h3 := U_cube c hc
  linear_combination (x - t) * h3

theorem af_inj (c t : Fin 13) (hc : c ∈ U) (x y : Fin 13) (h : c * x + t = c * y + t) :
    x = y := by
  have h3 := U_cube c hc
  have h1 : c * x = c * y := by linear_combination h
  linear_combination (y - x) * h3 + c ^ 2 * h1

theorem cardpre (c t : Fin 13) (hc : c ∈ U) (S : Finset (Fin 13)) :
    (Finset.univ.filter (fun x => c * x + t ∈ S)).card = S.card := by
  apply Finset.card_bij (fun x _ => c * x + t)
  · intro x hx
    simpa using hx
  · intro x _ y _ hxy
    exact af_inj c t hc x y hxy
  · intro y hy
    refine ⟨c ^ 2 * (y - t), ?_, af_surj c t hc y⟩
    simp [af_surj c t hc y, hy]

theorem transport (c t : Fin 13) (C : Circuit) (x7 r : List ℕ)
    (hset : ∀ j, (j ∈ x7.map (tau c t) ∧ j < 26) ↔ j ∈ r) (v w : List Bool)
    (hv : v.length = 26) (hw : w.length = 26)
    (hvw : ∀ i, v.getD (tau c t i) false = w.getD i false) :
    (mapC (tau c t) C).eval (v ++ [r.any fun j => v.getD j false]) =
      C.eval (w ++ [x7.any fun j => w.getD j false]) := by
  have hb : (r.any fun j => v.getD j false) = (x7.any fun j => w.getD j false) := by
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨j, hj, hvj⟩
      obtain ⟨hm, _⟩ := (hset j).2 hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hm
      exact ⟨i, hi, by rw [← hvw]; exact hvj⟩
    · rintro ⟨i, hi, hwi⟩
      rw [← hvw] at hwi
      have hj26 : tau c t i < 26 := by
        by_contra hh
        rw [List.getD_eq_default _ _ (by omega)] at hwi
        exact Bool.false_ne_true hwi
      exact ⟨tau c t i, (hset _).1 ⟨List.mem_map_of_mem hi, hj26⟩, hwi⟩
  rw [hb]
  apply eval_map (tau c t) 26 (tau_prop c t) C
  · simp [hw]
  · simp [hv, hw]
  · intro i
    rw [getD_snoc, getD_snoc, hv, hw]
    by_cases hi : i < 26
    · rw [if_pos (tau_lt c t i hi), if_pos hi]
      exact hvw i
    · rw [tau_ge c t i (by omega), if_neg hi, if_neg hi]

def Good (F : List Bool → Bool) : Prop :=
  (∀ (p l : Fin 13), p - l ∈ D →
    F ((List.ofFn fun x => decide (x = p)) ++ List.ofFn fun x => decide (x = l)) = true) ∧
  ∀ (X : Finset (Fin 13)), X.card = 4 → (∀ (l : Fin 13), {y ∈ X | y - l ∈ D}.card ≤ 2) →
    F ((List.ofFn fun x => decide (x ∈ X)) ++ List.ofFn fun l => decide (∀ y ∈ X, y - l ∉ D))
      = false

theorem good_transfer (c t : Fin 13) (hc : c ∈ U) (C : Circuit) (x7 r : List ℕ)
    (hset : ∀ j, (j ∈ x7.map (tau c t) ∧ j < 26) ↔ j ∈ r)
    (hC : Good fun v => C.eval (v ++ [x7.any fun j => v.getD j false])) :
    Good fun v => (mapC (tau c t) C).eval (v ++ [r.any fun j => v.getD j false]) := by
  obtain ⟨hinc, hquad⟩ := hC
  constructor
  · intro p l hpl
    have hp := af_surj c t hc p
    have hl := af_surj c t hc l
    have hpl' : c ^ 2 * (p - t) - c ^ 2 * (l - t) ∈ D := by
      rw [← D_inv c hc, ← af_sub c t, hp, hl]
      exact hpl
    have h1 := hinc _ _ hpl'
    dsimp only at h1 ⊢
    rw [transport c t C x7 r hset _ _ (by simp) (by simp) (rel c t _ _ _ _ ?_ ?_)]
    · exact h1
    · intro x
      rw [decide_eq_decide]
      constructor
      · intro h
        apply af_inj c t hc
        rw [h, hp]
      · intro h
        rw [h, hp]
    · intro x
      rw [decide_eq_decide]
      constructor
      · intro h
        apply af_inj c t hc
        rw [h, hl]
      · intro h
        rw [h, hl]
  · intro X hX hX2
    have hcard : (Finset.univ.filter (fun x => c * x + t ∈ X)).card = 4 := by
      rw [cardpre c t hc X, hX]
    have hlines : ∀ l : Fin 13,
        {y ∈ Finset.univ.filter (fun x => c * x + t ∈ X) | y - l ∈ D}.card ≤ 2 := by
      intro l
      have he : {y ∈ Finset.univ.filter (fun x => c * x + t ∈ X) | y - l ∈ D} =
          Finset.univ.filter (fun x => c * x + t ∈ {y ∈ X | y - (c * l + t) ∈ D}) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [af_sub, D_inv c hc]
      rw [he, cardpre c t hc]
      exact hX2 _
    have h1 := hquad _ hcard hlines
    dsimp only at h1 ⊢
    rw [transport c t C x7 r hset _ _ (by simp) (by simp) (rel c t _ _ _ _ ?_ ?_)]
    · exact h1
    · intro x
      simp
    · intro l
      rw [decide_eq_decide]
      constructor
      · intro h y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        have := h _ hy
        rw [af_sub, D_inv c hc] at this
        exact this
      · intro h y hy
        have hy' := af_surj c t hc y
        have := h (c ^ 2 * (y - t)) (by simp [hy', hy])
        rw [← D_inv c hc, ← af_sub c t, hy'] at this
        exact this

theorem mem_reps (k : ℕ) : reps.getD k [] ∈ reps := by
  rcases lt_or_ge k reps.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  · rw [List.getD_eq_default _ _ hk]
    simp [reps]

theorem reps_lt : ∀ r ∈ reps, ∀ j ∈ r, j < 26 := by decide

theorem pairsel (a b : ℕ) (ha : a < 26) (hb : b < 26) :
    ∃ c ∈ U, ∃ t : Fin 13, ∃ r ∈ reps, ∀ j, (j = tau c t a ∨ j = tau c t b) ↔ j ∈ r := by
  have h := ok_all a ha b hb
  unfold ok at h
  generalize (tbl.getD a []).getD b (1, 0, 0) = e at h
  obtain ⟨c, t, k⟩ := e
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hA⟩, hB⟩, hall⟩ := h
  refine ⟨_, hc, _, _, mem_reps k, fun j => ⟨?_, hall j⟩⟩
  rintro (rfl | rfl)
  · exact hA
  · exact hB

theorem choose_x7 (x7 : List ℕ) (hlen : x7.length ≤ 2) :
    ∃ c ∈ U, ∃ t : Fin 13, ∃ r ∈ reps, ∀ j, (j ∈ x7.map (tau c t) ∧ j < 26) ↔ j ∈ r := by
  have h1U : (1 : Fin 13) ∈ U := by decide
  match x7, hlen with
  | [], _ => exact ⟨1, h1U, 0, [], by simp [reps], by simp⟩
  | [a], _ =>
    by_cases ha : a < 26
    · obtain ⟨c, hc, t, r, hr, hj⟩ := pairsel a a ha ha
      refine ⟨c, hc, t, r, hr, fun j => ?_⟩
      rw [← hj]
      have := tau_lt c t a ha
      simp only [List.map_cons, List.map_nil, List.mem_singleton, or_self]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, by omega⟩
    · refine ⟨1, h1U, 0, [], by simp [reps], fun j => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton, List.not_mem_nil, iff_false,
        not_and]
      rw [tau_ge 1 0 a (by omega)]
      omega
  | [a, b], _ =>
    by_cases ha : a < 26
    · by_cases hb : b < 26
      · obtain ⟨c, hc, t, r, hr, hj⟩ := pairsel a b ha hb
        refine ⟨c, hc, t, r, hr, fun j => ?_⟩
        rw [← hj]
        have := tau_lt c t a ha
        have := tau_lt c t b hb
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, by omega⟩
      · obtain ⟨c, hc, t, r, hr, hj⟩ := pairsel a a ha ha
        refine ⟨c, hc, t, r, hr, fun j => ?_⟩
        rw [← hj]
        have := tau_lt c t a ha
        have hb' := tau_ge c t b (by omega)
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
          or_self]
        constructor
        · rintro ⟨h | h, h'⟩
          · exact h
          · omega
        · intro h
          exact ⟨Or.inl h, by omega⟩
    · by_cases hb : b < 26
      · obtain ⟨c, hc, t, r, hr, hj⟩ := pairsel b b hb hb
        refine ⟨c, hc, t, r, hr, fun j => ?_⟩
        rw [← hj]
        have := tau_lt c t b hb
        have ha' := tau_ge c t a (by omega)
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
          or_self]
        constructor
        · rintro ⟨h | h, h'⟩
          · omega
          · exact h
        · intro h
          exact ⟨Or.inr h, by omega⟩
      · refine ⟨1, h1U, 0, [], by simp [reps], fun j => ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
          iff_false, not_and]
        rw [tau_ge 1 0 a (by omega), tau_ge 1 0 b (by omega)]
        omega
  | _ :: _ :: _ :: _, h => simp at h

end PEqualNP.Outside.L_meta_4676

theorem PEqualNP.Outside.L_meta_4676 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : List ℕ), x7.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), ∃ x13 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x12 ∧ x4 x12 ∧ x3 x12 x13 ∧ x12.size ≤ x6.size := by
  intro x1 x2 x3 x4 x5 C x7 hlen hM hR hC
  obtain ⟨c, hc, t, r, hr, hset⟩ := PEqualNP.Outside.L_meta_4676.choose_x7 x7 hlen
  refine ⟨PEqualNP.Outside.L_meta_4676.mapC (PEqualNP.Outside.L_meta_4676.tau c t) C, r, hr,
    ?_, ?_, PEqualNP.Outside.L_meta_4676.good_transfer c t hc C x7 r hset hC, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hop, hl⟩ := hM g0 hg0
    exact ⟨hop, by simpa [PEqualNP.Outside.L_meta_4676.mapG] using hl⟩
  · intro j i hi
    have hj : j.1 < C.gates.length := by
      simpa [PEqualNP.Outside.L_meta_4676.mapC] using j.2
    have hget : (PEqualNP.Outside.L_meta_4676.mapC (PEqualNP.Outside.L_meta_4676.tau c t)
        C).gates.get j = PEqualNP.Outside.L_meta_4676.mapG (PEqualNP.Outside.L_meta_4676.tau c t)
        (C.gates.get ⟨j.1, hj⟩) := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp [PEqualNP.Outside.L_meta_4676.mapC]
    rw [hget] at hi
    simp only [PEqualNP.Outside.L_meta_4676.mapG] at hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
    have h0 : i0 < 27 + j.1 := hR ⟨j.1, hj⟩ i0 hi0
    by_cases h26 : i0 < 26
    · have := PEqualNP.Outside.L_meta_4676.tau_lt c t i0 h26
      omega
    · rw [PEqualNP.Outside.L_meta_4676.tau_ge c t i0 (by omega)]
      exact h0
  · simp [PEqualNP.Outside.L_meta_4676.mapC, PEqualNP.CircuitLowerBounds.Circuit.size]
