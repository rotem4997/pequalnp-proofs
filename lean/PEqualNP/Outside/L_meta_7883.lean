import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7883_aux

open PEqualNP.CircuitLowerBounds

def F (x5 : Fin 9 → Bool) : Bool :=
  (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5)

theorem avoid : ∀ a b : Fin 10, ∃ u v : Fin 9, u.val ≠ a.val ∧ u.val ≠ b.val ∧ v.val ≠ a.val ∧ v.val ≠ b.val ∧ F (fun i => decide (i = u) || decide (i = v)) = true := by
  decide

theorem getD_ofFn (x : Fin 9 → Bool) (a : ℕ) : (List.ofFn x).getD a false = if h : a < 9 then x ⟨a, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simpa using h)]

theorem key (C : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo C) (h1 : C.gates[(1 : ℕ)]? = Option.none) :
    ∃ a b : ℕ, ∀ x y : List Bool, x.length = 9 → y.length = 9 → x.getD a false = y.getD a false →
      x.getD b false = y.getD b false → C.eval x = C.eval y := by
  obtain ⟨gs, out⟩ := C
  match gs, hF, h1 with
  | [], _, _ =>
    refine ⟨out, out, fun x y _ _ ha _ => ?_⟩
    simpa [Circuit.eval, Circuit.wires] using ha
  | [g], hF, _ =>
    have hl : g.inputs.length ≤ 2 := (hF g (by simp)).2
    by_cases hout : out < 9
    · refine ⟨out, out, fun x y hx hy ha _ => ?_⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ha
    · refine ⟨g.inputs.getD 0 0, g.inputs.getD 1 0, fun x y hx hy ha hb => ?_⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hx, hy]
      have hm : (g.inputs.map fun i => x.getD i false) = (g.inputs.map fun i => y.getD i false) := by
        match hg : g.inputs, hl with
        | [], _ => rfl
        | [i], _ =>
          rw [hg] at ha
          simpa using ha
        | [i, j], _ =>
          rw [hg] at ha hb
          simp at ha hb
          simp [ha, hb]
      rw [hm]
  | _ :: _ :: _, _, h1 => simp at h1

end PEqualNP.Outside.L_meta_7883_aux

open PEqualNP.Outside.L_meta_7883_aux in
theorem PEqualNP.Outside.L_meta_7883 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → x1.gates[(1 : ℕ)]? = Option.none → ∃ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro C hF _ h1
  obtain ⟨a, b, hab⟩ := key C hF h1
  obtain ⟨u, v, hua, hub, hva, hvb, hF1⟩ := avoid ⟨min a 9, by omega⟩ ⟨min b 9, by omega⟩
  simp only at hua hub hva hvb
  by_cases h0 : C.eval (List.ofFn fun _ : Fin 9 => false) = false
  · refine ⟨fun i => decide (i = u) || decide (i = v), ?_⟩
    have he := hab (List.ofFn fun i : Fin 9 => decide (i = u) || decide (i = v)) (List.ofFn fun _ : Fin 9 => false) (by simp) (by simp) ?_ ?_
    · show C.eval _ ≠ F (fun i => decide (i = u) || decide (i = v))
      rw [he, h0, hF1]
      simp
    · rw [getD_ofFn, getD_ofFn]
      split_ifs with h
      · have : u.val ≠ a := by omega
        have : v.val ≠ a := by omega
        simp [Fin.ext_iff]
        omega
      · rfl
    · rw [getD_ofFn, getD_ofFn]
      split_ifs with h
      · have : u.val ≠ b := by omega
        have : v.val ≠ b := by omega
        simp [Fin.ext_iff]
        omega
      · rfl
  · refine ⟨fun _ => false, ?_⟩
    show C.eval _ ≠ F (fun _ => false)
    simpa [F] using h0
