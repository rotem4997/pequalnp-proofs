import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2121

open PEqualNP.CircuitLowerBounds

-- Test pairs: pa j and pb j differ only at input j, the edge function is true at pa j, false at pb j.
def pa : ℕ → List Bool
  | 0 => [true, false, true, false]
  | 1 => [false, true, true, false]
  | 2 => [true, false, true, false]
  | 3 => [true, false, false, true]
  | _ => []

def pb : ℕ → List Bool
  | 0 => [false, false, true, false]
  | 1 => [false, false, true, false]
  | 2 => [true, false, false, false]
  | 3 => [true, false, false, false]
  | _ => []

def ev (g : Gate) (W : List Bool) : Bool := g.op.eval (g.inputs.map fun i => W.getD i false)

theorem key (g : Gate) (W W' : List Bool)
    (h : ∀ i ∈ g.inputs, W.getD i false = W'.getD i false) : ev g W = ev g W' := by
  unfold ev
  rw [List.map_congr_left h]

theorem agree0 (j : ℕ) (hj : j < 4) (i : ℕ) (hi : i ≠ j) :
    (pa j).getD i false = (pb j).getD i false := by
  interval_cases j <;> rcases i with _ | _ | _ | _ | i <;> simp_all [pa, pb]

theorem agree1 (j : ℕ) (hj : j < 4) (b b' : Bool) (i : ℕ) (hi : i ≠ j) (hb : i = 4 → b = b') :
    (pa j ++ [b]).getD i false = (pb j ++ [b']).getD i false := by
  interval_cases j <;> rcases i with _ | _ | _ | _ | _ | i <;> simp_all [pa, pb]

theorem agree2 (j : ℕ) (hj : j < 4) (b b' c c' : Bool) (i : ℕ) (hi : i ≠ j)
    (hb : i = 4 → b = b') (hc : i = 5 → c = c') :
    (pa j ++ [b] ++ [c]).getD i false = (pb j ++ [b'] ++ [c']).getD i false := by
  interval_cases j <;> rcases i with _ | _ | _ | _ | _ | _ | i <;> simp_all [pa, pb]

theorem hab (C : Circuit) (hf : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun z : Fin 4 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 1 && z 2) || (z 1 && z 3)) x) :
    ∀ j < 4, C.eval (pa j) = true ∧ C.eval (pb j) = false := by
  have h := fun a b c d => hf ![a, b, c, d]
  simp [List.ofFn_succ] at h
  intro j hj
  interval_cases j <;> simp [pa, pb, h]

theorem main (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hab : ∀ j < 4, C.eval (pa j) = true ∧ C.eval (pb j) = false) : 3 ≤ C.size := by
  obtain ⟨gates, out⟩ := C
  by_contra hs
  simp only [Circuit.size, not_le] at hs
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g hg => (hm g hg).2
  rcases gates with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, rest⟩⟩⟩
  · have key0 : ∀ j < 4, out = j := by
      intro j hj
      by_contra hne
      obtain ⟨h1, h2⟩ := hab j hj
      have e := agree0 j hj out hne
      change (pa j).getD out false = true at h1
      change (pb j).getD out false = false at h2
      rw [e, h2] at h1
      exact Bool.false_ne_true h1
    have := key0 0 (by norm_num)
    have := key0 1 (by norm_num)
    omega
  · have k0 := hlen g0 (by simp)
    have key1 : ∀ j < 4, out = j ∨ (out = 4 ∧ j ∈ g0.inputs) := by
      intro j hj
      by_contra hne
      push Not at hne
      obtain ⟨hn1, hn2⟩ := hne
      obtain ⟨h1, h2⟩ := hab j hj
      have e := agree1 j hj (ev g0 (pa j)) (ev g0 (pb j)) out hn1
        (fun h4 => key g0 _ _ (fun i hi => agree0 j hj i (by rintro rfl; exact hn2 h4 hi)))
      change (pa j ++ [ev g0 (pa j)]).getD out false = true at h1
      change (pb j ++ [ev g0 (pb j)]).getD out false = false at h2
      rw [e, h2] at h1
      exact Bool.false_ne_true h1
    obtain ⟨op, l⟩ := g0
    simp only at k0 key1
    have a0 := key1 0 (by norm_num)
    have a1 := key1 1 (by norm_num)
    have a2 := key1 2 (by norm_num)
    have a3 := key1 3 (by norm_num)
    rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, l⟩⟩⟩ <;> simp at a0 a1 a2 a3 k0 <;> omega
  · have k0 := hlen g0 (by simp)
    have k1 := hlen g1 (by simp)
    have key2 : ∀ j < 4, out = j ∨ (out = 4 ∧ j ∈ g0.inputs) ∨
        (out = 5 ∧ (j ∈ g1.inputs ∨ (4 ∈ g1.inputs ∧ j ∈ g0.inputs))) := by
      intro j hj
      by_contra hne
      push Not at hne
      obtain ⟨hn1, hn2, hn3⟩ := hne
      obtain ⟨h1, h2⟩ := hab j hj
      have e := agree2 j hj (ev g0 (pa j)) (ev g0 (pb j)) (ev g1 (pa j ++ [ev g0 (pa j)]))
        (ev g1 (pb j ++ [ev g0 (pb j)])) out hn1
        (fun h4 => key g0 _ _ (fun i hi => agree0 j hj i (by rintro rfl; exact hn2 h4 hi)))
        (fun h5 => key g1 _ _ (fun i hi => agree1 j hj _ _ i (by rintro rfl; exact (hn3 h5).1 hi)
          (fun hi4 => key g0 _ _ (fun i' hi' =>
            agree0 j hj i' (by rintro rfl; exact (hn3 h5).2 (hi4 ▸ hi) hi')))))
      change (pa j ++ [ev g0 (pa j)] ++ [ev g1 (pa j ++ [ev g0 (pa j)])]).getD out false = true at h1
      change (pb j ++ [ev g0 (pb j)] ++ [ev g1 (pb j ++ [ev g0 (pb j)])]).getD out false = false at h2
      rw [e, h2] at h1
      exact Bool.false_ne_true h1
    obtain ⟨op0, l0⟩ := g0
    obtain ⟨op1, l1⟩ := g1
    simp only at k0 k1 key2
    have a0 := key2 0 (by norm_num)
    have a1 := key2 1 (by norm_num)
    have a2 := key2 2 (by norm_num)
    have a3 := key2 3 (by norm_num)
    rcases l0 with _ | ⟨p, _ | ⟨q, _ | ⟨r, l0⟩⟩⟩ <;>
      rcases l1 with _ | ⟨s, _ | ⟨t, _ | ⟨u, l1⟩⟩⟩ <;>
      simp at a0 a1 a2 a3 k0 k1 <;> omega
  · simp only [List.length_cons] at hs; omega

end PEqualNP.Outside.L_meta_2121

theorem PEqualNP.Outside.L_meta_2121 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 4 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun z : Fin 4 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 1 && z 2) || (z 1 && z 3)) x) → 3 ≤ C.size := by
  intro C hm _ hf
  exact PEqualNP.Outside.L_meta_2121.main C hm (PEqualNP.Outside.L_meta_2121.hab C hf)
