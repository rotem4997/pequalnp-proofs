import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18785
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def index (m : ℕ) (p : Fin 26 → Option (Fin 25)) (w : ℕ) : ℕ :=
  if h : w < 26 then (p ⟨w,h⟩).elim (25+m) (fun i => i.val) else 25+(w-26)

def gate (m : ℕ) (p : Fin 26 → Option (Fin 25)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (index m p)⟩

def step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]

theorem read_append (u : List Bool) (b : Bool) (w : Nat) :
    (u ++ [b]).getD w false = if w = u.length then b else u.getD w false := by
  by_cases same : w = u.length
  · subst w; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg same]
    by_cases before : w < u.length
    · exact List.getD_append _ _ _ _ before
    · rw [List.getD_eq_default _ _ (by simp <;> omega),List.getD_eq_default _ _ (by omega)]

theorem sim (m : ℕ) (p : Fin 26 → Option (Fin 25)) (gs : List Gate) (t : ℕ)
    (budget : t+gs.length ≤ m) (u v : List Bool) (hu : u.length = 25+t)
    (hv : v.length = 26+t) (h : ∀ w, u.getD (index m p w) false = v.getD w false) : ∀ w,
    ((gs.map (gate m p)).foldl step u).getD (index m p w) false = (gs.foldl step v).getD w false := by
  induction gs generalizing t u v with
  | nil => exact h
  | cons g gs ih =>
    have room : t < m := by simp only [List.length_cons] at budget; omega
    apply ih (t+1) (by simp only [List.length_cons] at budget; omega) _ _ (by simp [step,hu]; omega) (by simp [step,hv]; omega)
    intro w
    have same : (gate m p g).op.eval ((gate m p g).inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by simp only [gate,List.map_map,Function.comp_def,h]
    simp only [step,read_append,hu,hv,same,h]
    by_cases hw : w < 26
    · have neq : index m p w ≠ 25+t := by
        simp only [index,dif_pos hw]
        cases v0 : p ⟨w,hw⟩ with
        | none => change 25+m ≠ 25+t; omega
        | some i => change i.val ≠ 25+t; have := i.isLt; omega
      rw [if_neg neq,if_neg (by omega)]
    · simp only [index,dif_neg hw]
      by_cases eq : w = 26+t
      · rw [if_pos eq,if_pos (by omega)]
      · rw [if_neg eq,if_neg (by omega)]

end PEqualNP.Outside.L_meta_18785

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18785 in
theorem PEqualNP.Outside.L_meta_18785 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Option (Fin (25 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size = x1.size ∧ ∀ (x5 : Fin (25 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => (x2 x6).elim Bool.false x5) := by
  intro C p hC
  let m := C.gates.length
  let D : Circuit := ⟨C.gates.map (gate m p),index m p C.output⟩
  refine ⟨D,?_,by simp [D,Circuit.size],?_⟩
  · intro g hg
    obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
    simpa [gate] using hC old mem
  · intro y
    apply sim m p C.gates 0 (by simp [m]) _ _ (by simp) (by simp) _ C.output
    intro w
    by_cases hw : w < 26
    · simp only [index,dif_pos hw,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hw,dite_true,Option.getD_some]
      cases e : p ⟨w,hw⟩ with
      | none => simp
      | some i => simp [i.isLt]
    · rw [show index m p w = 25+(w-26) by simp [index,hw]]
      rw [List.getD_eq_default _ _ (by simp <;> omega),List.getD_eq_default _ _ (by simp <;> omega)]
