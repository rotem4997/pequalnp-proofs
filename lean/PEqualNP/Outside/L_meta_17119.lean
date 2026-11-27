import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17119

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev V := BitVec 32
def dom (t a b : V) : Prop := (a ^^^ t) &&& (b ^^^ t) = a ^^^ t
def op (o : Bool) (a b : V) : V := if o = true then a &&& b else a ||| b

theorem dom_bit (t a b : V) : dom t a b ↔ ∀ i : ℕ, i < 32 → (((a.getLsbD i ^^ t.getLsbD i) && (b.getLsbD i ^^ t.getLsbD i)) = (a.getLsbD i ^^ t.getLsbD i)) := by
  unfold dom
  constructor
  · intro h i _
    have := congrArg (fun z : V => z.getLsbD i) h
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simpa using h i hi

theorem dom_refl (t a : V) : dom t a a := by
  rw [dom_bit]; intro i _; cases a.getLsbD i <;> cases t.getLsbD i <;> rfl

theorem dom_trans {t a b c : V} (h : dom t a b) (k : dom t b c) : dom t a c := by
  rw [dom_bit] at *
  intro i hi
  have h := h i hi
  have k := k i hi
  revert h k
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases t.getLsbD i <;> decide

theorem dom_op {t a b a' b' : V} (o : Bool) (h : dom t a' a) (k : dom t b' b) : dom t (op o a' b') (op o a b) := by
  rw [dom_bit] at *
  intro i hi
  have h := h i hi
  have k := k i hi
  revert h k
  cases o <;> simp only [op, if_true, if_false, Bool.false_eq_true, reduceIte, BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases a'.getLsbD i <;> cases b'.getLsbD i <;> cases t.getLsbD i <;> decide

theorem dom_top {t a : V} (h : dom t a t) : a = t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := (dom_bit t a t).1 h i hi
  revert h
  cases a.getLsbD i <;> cases t.getLsbD i <;> decide

def good (x : List V) (t : V) (y : List V) : Prop :=
  ∀ i (h : i < y.length), (∃ u ∈ x ++ y.take i, ∃ v ∈ x ++ y.take i, y[i] = u &&& v ∨ y[i] = u ||| v) ∧
    ∀ u ∈ x ++ y.take i, ¬ dom t u y[i]

theorem good_snoc {x : List V} {t : V} {y : List V} {g : V} (hy : good x t y)
    (h1 : ∃ u ∈ x ++ y, ∃ v ∈ x ++ y, g = u &&& v ∨ g = u ||| v) (h2 : ∀ u ∈ x ++ y, ¬ dom t u g) : good x t (y ++ [g]) := by
  intro i hi
  rcases Nat.lt_or_ge i y.length with h | h
  · have e1 : (y ++ [g])[i] = y[i] := by rw [List.getElem_append_left h]
    have e2 : (y ++ [g]).take i = y.take i := by rw [List.take_append_of_le_length h.le]
    rw [e1, e2]
    exact hy i h
  · have hi' : i = y.length := by
      simp at hi
      omega
    subst hi'
    simpa using And.intro h1 h2

def stp (n : ℕ) (w : List V) (g : Bool × Fin n × Fin n) : List V := w ++ [op g.1 (w.getD g.2.1 0) (w.getD g.2.2 0)]

theorem main {n : ℕ} (x : List V) (t : V) (h0 : (0 : V) ∈ x) (l : List (Bool × Fin n × Fin n)) :
    ∃ y : List V, y.length ≤ l.length ∧ good x t y ∧ ∀ w ∈ l.foldl (stp n) x, ∃ w' ∈ x ++ y, dom t w' w := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], le_refl _, fun i h => absurd h (by simp), fun w hw => ⟨w, by simpa using hw, dom_refl t w⟩⟩
  | append_singleton l g ih =>
    obtain ⟨y, hl, hg, hd⟩ := ih
    have gd : ∀ k : ℕ, ∃ w' ∈ x ++ y, dom t w' ((l.foldl (stp n) x).getD k 0) := by
      intro k
      rcases Nat.lt_or_ge k (l.foldl (stp n) x).length with h | h
      · rw [List.getD_eq_getElem _ _ h]
        exact hd _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]
        exact ⟨0, List.mem_append_left _ h0, dom_refl t 0⟩
    obtain ⟨a, ha, da⟩ := gd g.2.1
    obtain ⟨b, hb, db⟩ := gd g.2.2
    have dg := dom_op g.1 da db
    have hf : (l ++ [g]).foldl (stp n) x = l.foldl (stp n) x ++ [op g.1 ((l.foldl (stp n) x).getD g.2.1 0) ((l.foldl (stp n) x).getD g.2.2 0)] := by
      rw [List.foldl_append]; rfl
    by_cases hc : ∃ u ∈ x ++ y, dom t u (op g.1 a b)
    · obtain ⟨u, hu, du⟩ := hc
      refine ⟨y, by simp; omega, hg, ?_⟩
      intro w hw
      rw [hf] at hw
      rcases List.mem_append.1 hw with h | h
      · exact hd w h
      · rw [List.mem_singleton.1 h]
        exact ⟨u, hu, dom_trans du dg⟩
    · refine ⟨y ++ [op g.1 a b], by simpa using hl, good_snoc hg ⟨a, ha, b, hb, ?_⟩ (fun u hu hd => hc ⟨u, hu, hd⟩), ?_⟩
      · cases g.1 <;> simp [op]
      · intro w hw
        rw [hf] at hw
        rcases List.mem_append.1 hw with h | h
        · obtain ⟨w', hw', d⟩ := hd w h
          refine ⟨w', ?_, d⟩
          rw [← List.append_assoc]
          exact List.mem_append_left _ hw'
        · rw [List.mem_singleton.1 h]
          exact ⟨_, by simp, dg⟩

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_17119

theorem PEqualNP.Outside.L_meta_17119 : ∀ (x1 : List (BitVec (32 : ℕ))) (x2 : BitVec (32 : ℕ)) (x3 : Fin (18 : ℕ) → Bool × Fin (29 : ℕ) × Fin (29 : ℕ)) (x4 : Fin (19 : ℕ)),   (0 : BitVec (32 : ℕ)) ∈ x1 →     x2 ∈ List.foldl (fun (x6 : List (BitVec (32 : ℕ))) (x7 : Bool × Fin (29 : ℕ) × Fin (29 : ℕ)) => x6 ++ [if x7.1 = Bool.true then x6.getD ↑x7.2.1 (0 : BitVec (32 : ℕ)) &&& x6.getD ↑x7.2.2 (0 : BitVec (32 : ℕ)) else x6.getD ↑x7.2.1 (0 : BitVec (32 : ℕ)) ||| x6.getD ↑x7.2.2 (0 : BitVec (32 : ℕ))]) x1 (List.take (↑x4) (List.ofFn x3)) →       ∃ (x7 : List (BitVec (32 : ℕ))),         x7.length ≤ ↑x4 ∧           x2 ∈ x1 ++ x7 ∧             ∀ (x8 : Fin x7.length),               have x9 : List (BitVec (32 : ℕ)) := x1 ++ List.take (↑x8) x7;               (∃ x10 ∈ x9, ∃ x11 ∈ x9, x7.get x8 = x10 &&& x11 ∨ x7.get x8 = x10 ||| x11) ∧ ∀ x10 ∈ x9, (x10 ^^^ x2) &&& (x7.get x8 ^^^ x2) ≠ x10 ^^^ x2 := by
  intro x1 x2 x3 x4 h0 hx
  obtain ⟨y, hl, hg, hd⟩ := L_meta_17119.main x1 x2 h0 (List.take (x4 : ℕ) (List.ofFn x3))
  obtain ⟨w, hw, dw⟩ := hd x2 hx
  have := L_meta_17119.dom_top dw
  subst this
  refine ⟨y, ?_, hw, ?_⟩
  · refine le_trans hl ?_
    rw [List.length_take]
    exact Nat.min_le_left _ _
  · intro i
    exact ⟨(hg i.1 i.2).1, fun u hu => (hg i.1 i.2).2 u hu⟩
