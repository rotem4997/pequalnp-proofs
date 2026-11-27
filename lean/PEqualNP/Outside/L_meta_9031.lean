import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9031

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


def ptf : (Fin 10 → Bool) → Bool := (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)))
def eg : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def inp (e : Fin 10 × Fin 10) : Fin 10 → Bool := fun i => decide (i = e.1) || decide (i = e.2)
def dl (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 1]

theorem far : ∀ u v : Fin 11, ∃ e ∈ eg, ptf (inp e) = true ∧ (dl (inp e)).getD u false = false ∧ (dl (inp e)).getD v false = false := by decide +kernel
theorem zero : ptf (fun _ => false) = false ∧ ∀ u : Fin 11, (dl fun _ => false).getD u false = false := by decide +kernel
theorem len (x : Fin 10 → Bool) : (dl x).length = 11 := by simp [dl]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9031

theorem PEqualNP.Outside.L_meta_9031 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.gates[(1 : ℕ)]? = Option.none → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C hC _ hno
  by_contra hcon
  push Not at hcon
  have hcon : ∀ x, C.eval (PEqualNP.Outside.L_meta_9031.dl x) = PEqualNP.Outside.L_meta_9031.ptf x := hcon
  have hlen : C.gates.length ≤ 1 := by
    by_contra h
    rw [List.getElem?_eq_getElem (by omega)] at hno
    cases hno
  have big : ∀ (x : Fin 10 → Bool) (u : ℕ), 11 ≤ u → (PEqualNP.Outside.L_meta_9031.dl x).getD u false = false := fun x u hu => by
    rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_9031.len]; exact hu)]
  -- the value depends on two wires
  have dep : ∃ u v : ℕ, ∀ x y : Fin 10 → Bool, (PEqualNP.Outside.L_meta_9031.dl x).getD u false = (PEqualNP.Outside.L_meta_9031.dl y).getD u false → (PEqualNP.Outside.L_meta_9031.dl x).getD v false = (PEqualNP.Outside.L_meta_9031.dl y).getD v false → C.eval (PEqualNP.Outside.L_meta_9031.dl x) = C.eval (PEqualNP.Outside.L_meta_9031.dl y) := by
    obtain ⟨gs, o⟩ := C
    rcases gs with _ | ⟨g, _ | ⟨g', l⟩⟩
    · exact ⟨o, o, fun x y h _ => h⟩
    · have ev : ∀ x, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨[g], o⟩ (PEqualNP.Outside.L_meta_9031.dl x) = (PEqualNP.Outside.L_meta_9031.dl x ++ [g.op.eval (g.inputs.map fun i => (PEqualNP.Outside.L_meta_9031.dl x).getD i false)]).getD o false := fun _ => rfl
      have hl := (hC g (by simp)).2
      rcases Nat.lt_trichotomy o 11 with h | h | h
      · refine ⟨o, o, fun x y hxy _ => ?_⟩
        rw [ev, ev, List.getD_append _ _ _ _ (by rw [PEqualNP.Outside.L_meta_9031.len]; exact h), List.getD_append _ _ _ _ (by rw [PEqualNP.Outside.L_meta_9031.len]; exact h)]
        exact hxy
      · have e1 : ∀ x, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨[g], o⟩ (PEqualNP.Outside.L_meta_9031.dl x) = g.op.eval (g.inputs.map fun i => (PEqualNP.Outside.L_meta_9031.dl x).getD i false) := by
          intro x
          rw [ev, List.getD_append_right _ _ _ _ (by rw [PEqualNP.Outside.L_meta_9031.len]; omega), PEqualNP.Outside.L_meta_9031.len, h]
          rfl
        rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · exact ⟨0, 0, fun x y _ _ => by rw [e1, e1, hin]; rfl⟩
        · exact ⟨a, a, fun x y h1 _ => by rw [e1, e1, hin]; simp only [List.map_cons, List.map_nil, h1]⟩
        · exact ⟨a, b, fun x y h1 h2 => by rw [e1, e1, hin]; simp only [List.map_cons, List.map_nil, h1, h2]⟩
        · rw [hin] at hl; simp at hl
      · refine ⟨0, 0, fun x y _ _ => ?_⟩
        rw [ev, ev, List.getD_eq_default _ _ (by simp [PEqualNP.Outside.L_meta_9031.len]; omega), List.getD_eq_default _ _ (by simp [PEqualNP.Outside.L_meta_9031.len]; omega)]
    · simp at hlen
  obtain ⟨u, v, hd⟩ := dep
  have key : ∃ e ∈ PEqualNP.Outside.L_meta_9031.eg, PEqualNP.Outside.L_meta_9031.ptf (PEqualNP.Outside.L_meta_9031.inp e) = true ∧ (PEqualNP.Outside.L_meta_9031.dl (PEqualNP.Outside.L_meta_9031.inp e)).getD u false = false ∧ (PEqualNP.Outside.L_meta_9031.dl (PEqualNP.Outside.L_meta_9031.inp e)).getD v false = false := by
    by_cases hu : u < 11 <;> by_cases hv : v < 11
    · exact PEqualNP.Outside.L_meta_9031.far ⟨u, hu⟩ ⟨v, hv⟩
    · obtain ⟨e, h1, h2, h3, _⟩ := PEqualNP.Outside.L_meta_9031.far ⟨u, hu⟩ ⟨u, hu⟩
      exact ⟨e, h1, h2, h3, big _ _ (by omega)⟩
    · obtain ⟨e, h1, h2, h3, _⟩ := PEqualNP.Outside.L_meta_9031.far ⟨v, hv⟩ ⟨v, hv⟩
      exact ⟨e, h1, h2, big _ _ (by omega), h3⟩
    · obtain ⟨e, h1, h2, _⟩ := PEqualNP.Outside.L_meta_9031.far 0 0
      exact ⟨e, h1, h2, big _ _ (by omega), big _ _ (by omega)⟩
  obtain ⟨e, _, h1, h2, h3⟩ := key
  have z : ∀ w, (PEqualNP.Outside.L_meta_9031.dl fun _ => false).getD w false = false := by
    intro w
    by_cases hw : w < 11
    · exact PEqualNP.Outside.L_meta_9031.zero.2 ⟨w, hw⟩
    · exact big _ _ (by omega)
  have := hd (PEqualNP.Outside.L_meta_9031.inp e) (fun _ => false) (by rw [h2, z]) (by rw [h3, z])
  rw [hcon, hcon, h1, PEqualNP.Outside.L_meta_9031.zero.1] at this
  cases this
