import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18812.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

def derive (n : ℕ) (C : Circuit) (s : ℕ) (x : List Bool) (w : ℕ) : Bool :=
  if hw : w < n then decide (w=s)
  else
    let g := C.gates.getD (w-n) {op := .or,inputs := []}
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if ha : a < w then
      if hb : b < w then
        match g.op with
        | .and => (C.wires x).getD a false && derive n C s x b || derive n C s x a && (C.wires x).getD b false
        | _ => derive n C s x a || derive n C s x b
      else false
    else false
termination_by w

lemma propagate (n : ℕ) (C : Circuit) (s : ℕ) (x : List Bool) (hao : IsAO2 n C) :
    ∃ d : ℕ → Bool, (∀ i < n,d i = decide (i=s)) ∧
      ∀ (j : ℕ) (g : Gate) (u v : ℕ), C.gates[j]? = some g → g.inputs = [u,v] →
        (g.op = .and → d (n+j) = ((C.wires x).getD u false && d v || d u && (C.wires x).getD v false)) ∧
        (g.op = .or → d (n+j) = (d u || d v)) := by
  refine ⟨derive n C s x,?_,?_⟩
  · intro i hi
    rw [derive]
    simp [hi]
  · intro j g u v hg hins
    have hj : j < C.gates.length := by
      by_contra hn
      have hnone : C.gates[j]? = none := List.getElem?_eq_none (by omega)
      rw [hnone] at hg
      cases hg
    have hgate : gateAt C j = g := by simp [gateAt,List.getD_eq_getElem?_getD,hg]
    have hu : u < n+j := hao.2.1 j hj u (by rw [hgate,hins];simp)
    have hv : v < n+j := hao.2.1 j hj v (by rw [hgate,hins];simp)
    have hlow : ¬ n+j < n := by omega
    constructor
    · intro hop
      rw [derive]
      simp only [hlow,↓reduceDIte,Nat.add_sub_cancel_left,List.getD_eq_getElem?_getD,hg,
        Option.getD_some,hins,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
        hop,hu,hv,↓reduceDIte]
    · intro hop
      rw [derive]
      simp only [hlow,↓reduceDIte,Nat.add_sub_cancel_left,List.getD_eq_getElem?_getD,hg,
        Option.getD_some,hins,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
        hop,hu,hv,↓reduceDIte]
end PEqualNP.Outside.L_meta_18812.Helpers


theorem PEqualNP.Outside.L_meta_18812 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : List Bool), PEqualNP.TopForm.IsAO2 x1 x2 → ∃ (x6 : ℕ → Bool), (∀ x7 < x1, x6 x7 = Decidable.decide (x7 = x3)) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x2.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x7) = ((x2.wires x4).getD x9 Bool.false && x6 x10 || x6 x9 && (x2.wires x4).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x7) = (x6 x9 || x6 x10))) := by
  exact PEqualNP.Outside.L_meta_18812.Helpers.propagate
