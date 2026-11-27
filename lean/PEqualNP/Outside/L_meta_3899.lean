import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3899

open PEqualNP.MetaComplexity

def clip (i : ℕ) : Fin 24 :=
  ⟨if i < 24 then i else 10, by split <;> omega⟩

def symmetry (i : ℕ) : ℕ := ([1, 0, 5, 8, 6, 2, 4, 7, 3] : List ℕ).getD i i

private lemma comparisons (i : ℕ) :
    (symmetry (clip i).val < (clip i).val ↔ symmetry i < i) ∧
    (symmetry (clip i).val = (clip i).val ↔ symmetry i = i) := by
  by_cases hi : i < 24
  · simp [clip, hi]
  · have hSym : symmetry i = i := List.getD_eq_default _ _ (by simp; omega)
    have hTen : symmetry 10 = 10 := rfl
    simp [clip, hi, hSym, hTen]

lemma clip_prefix_order (a b : ℕ) (h : [a, b] ≤ [symmetry a, symmetry b]) :
    [(clip a).val, (clip b).val] ≤ [symmetry (clip a).val, symmetry (clip b).val] := by
  have hOld : ¬ List.Lex (· < ·) [symmetry a, symmetry b] [a, b] := not_lt.mpr h
  have hNew : ¬ List.Lex (· < ·) [symmetry (clip a).val, symmetry (clip b).val]
      [(clip a).val, (clip b).val] := by
    simpa only [List.cons_lex_cons_iff, (comparisons a).1, (comparisons a).2,
      (comparisons b).1, (comparisons b).2] using hOld
  exact not_lt.mp hNew

private def leftFlag (g : BinaryGate) : Bool := g.op true false || g.op true true

private def rightFlag (g : BinaryGate) : Bool := g.op false true || g.op true true

def encodeBoundedGate (g : BinaryGate) : Fin 24 × Fin 24 × Bool × Bool :=
  (clip g.left, clip g.right, leftFlag g, rightFlag g)

private lemma flags_eq {g : BinaryGate} {a b : Bool}
    (h : g.op = fun u v => u == a && v == b) : leftFlag g = a ∧ rightFlag g = b := by
  cases a <;> cases b <;> simp [leftFlag, rightFlag, h]

lemma encoded_first_false {g : BinaryGate} {b : Bool}
    (h : g.op = fun u v => u == false && v == b) : (encodeBoundedGate g).2.2.1 = false :=
  (flags_eq h).1

lemma read_clip (w : List Bool) (hLen : w.length ≤ 24) (hZero : w.getD 10 false = false)
    (i : ℕ) : w.getD (clip i).val false = w.getD i false := by
  by_cases hi : i < 24
  · simp [clip, hi]
  · have h := List.getD_eq_default w false (show w.length ≤ i by omega)
    simpa only [clip, ite_eq_right hi] using hZero.trans h.symm

def stepOriginal (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def stepEncoded (w : List Bool) (g : Fin 24 × Fin 24 × Bool × Bool) : List Bool :=
  w ++ [w.getD g.1.val false == g.2.2.1 && w.getD g.2.1.val false == g.2.2.2]

private lemma step_eq (w : List Bool) (g : BinaryGate)
    (model : ∃ a b : Bool, g.op = fun u v => u == a && v == b)
    (hLen : w.length ≤ 24) (hZero : w.getD 10 false = false) :
    stepEncoded w (encodeBoundedGate g) = stepOriginal w g := by
  obtain ⟨a, b, h⟩ := model
  obtain ⟨hl, hr⟩ := flags_eq h
  simp only [stepEncoded, encodeBoundedGate, stepOriginal, hl, hr, read_clip w hLen hZero, h]

lemma fold_match (gates : List BinaryGate)
    (model : ∀ g ∈ gates, ∃ a b : Bool, g.op = fun u v => u == a && v == b)
    (w : List Bool) (hMin : 11 ≤ w.length) (hBudget : w.length + gates.length ≤ 24)
    (hZero : w.getD 10 false = false) :
    (gates.map encodeBoundedGate).foldl stepEncoded w = gates.foldl stepOriginal w ∧
      (gates.foldl stepOriginal w).length = w.length + gates.length ∧
      (gates.foldl stepOriginal w).getD 10 false = false := by
  induction gates generalizing w with
  | nil => exact ⟨rfl, rfl, hZero⟩
  | cons g gs ih =>
    let next := stepOriginal w g
    have hNext : next.length = w.length + 1 := by simp [next, stepOriginal]
    have hNextZero : next.getD 10 false = false := by
      change (w ++ [_]).getD 10 false = false
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hZero
    have hAll := ih (fun j hj => model j (List.mem_cons_of_mem g hj)) next
      (by omega) (by simp only [List.length_cons] at hBudget; omega) hNextZero
    change (gs.map encodeBoundedGate).foldl stepEncoded (stepEncoded w (encodeBoundedGate g)) =
        gs.foldl stepOriginal next ∧
      (gs.foldl stepOriginal next).length = w.length + (g :: gs).length ∧
      (gs.foldl stepOriginal next).getD 10 false = false
    rw [step_eq w g (model g List.mem_cons_self) (by omega) hZero]
    refine ⟨hAll.1, ?_, hAll.2.2⟩
    rw [hAll.2.1, hNext, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_3899

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3899


theorem PEqualNP.Outside.L_meta_3899 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit),   x1.size ≤ (13 : ℕ) →     (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) →       (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate),           x1.gates[(0 : ℕ)]? = Option.some x4 →             (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧               have x6 : ℕ → ℕ := fun (x6 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x6 x6;               [x4.left, x4.right] ≤ [x6 x4.left, x6 x4.right]) →         ∃ (x5 : List (Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool)) (x6 : Fin (24 : ℕ)),           x5.length = x1.size ∧             (∀ x7 ∈ x5.head?.toList,                 x7.2.2.1 = Bool.false ∧                   have x9 : ℕ → ℕ := fun (x9 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x9 x9;                   [↑x7.1, ↑x7.2.1] ≤ [x9 ↑x7.1, x9 ↑x7.2.1]) ∧               ∀ (x7 : List Bool), x7.length = (11 : ℕ) → x7.getD (10 : ℕ) Bool.false = Bool.false → (List.foldl (fun (x10 : List Bool) (x11 : Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool) => x10 ++ [x10.getD (↑x11.1) Bool.false == x11.2.2.1 && x10.getD (↑x11.2.1) Bool.false == x11.2.2.2]) x7 x5).getD (↑x6) Bool.false = x1.eval x7 := by
  intro C hSize hOps hFirst
  let codes := C.gates.map encodeBoundedGate
  refine ⟨codes, clip C.output, ?_, ?_, ?_⟩
  · change (C.gates.map encodeBoundedGate).length = C.gates.length
    rw [List.length_map]
  · intro g hg
    cases hGates : C.gates with
    | nil => simp [codes, hGates] at hg
    | cons a gs =>
      have hEq : g = encodeBoundedGate a := by simpa [codes, hGates] using hg
      subst g
      obtain ⟨⟨b, hop⟩, hOrder⟩ := hFirst a (by simp [hGates])
      exact ⟨encoded_first_false hop, clip_prefix_order a.left a.right hOrder⟩
  · intro x hx hZero
    have hGates : C.gates.length ≤ 13 := hSize
    obtain ⟨hRun, hLen, hTailZero⟩ :=
      fold_match C.gates hOps x (by omega) (by omega) hZero
    change ((C.gates.map encodeBoundedGate).foldl stepEncoded x).getD (clip C.output).val false =
      (C.gates.foldl stepOriginal x).getD C.output false
    rw [hRun]
    exact read_clip _ (by omega) hTailZero C.output
