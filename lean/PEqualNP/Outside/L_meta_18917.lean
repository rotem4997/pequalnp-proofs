import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18917.Helpers
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

lemma terminal (n : ℕ) (C : Circuit) (j u v s : ℕ) (x : Fin n → Bool)
    (hao : IsAO2 n C) (hout : C.output = n+j) (_hlen : j+1=C.size)
    (hg : C.gates[j]? = some ⟨.and,[u,v]⟩) :
    let w : ℕ → Bool := fun k => (C.wires (List.ofFn x)).getD k false
    w u = false → w v = false →
    ∃ d : ℕ → Bool,
      (∀ i < n,d i = decide (i=s)) ∧
      (∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs=[a,b] →
        (g.op = .and → d (n+k) = (w a && d b || d a && w b)) ∧
        (g.op = .or → d (n+k) = (d a || d b))) ∧ d C.output = false := by
  dsimp only
  intro hu hv
  obtain ⟨d,hi,hd⟩ := propagate n C s (List.ofFn x) hao
  refine ⟨d,hi,hd,?_⟩
  rw [hout, (hd j ⟨.and,[u,v]⟩ u v hg rfl).1 rfl, hu, hv]
  simp
end PEqualNP.Outside.L_meta_18917.Helpers


theorem PEqualNP.Outside.L_meta_18917 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 : ℕ) (x7 : Fin x1 → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     x2.output = x1 + x3 →       x3 + (1 : ℕ) = x2.size →         x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →           have x12 : ℕ → Bool := fun (x12 : ℕ) => (x2.wires (List.ofFn x7)).getD x12 Bool.false;           x12 x4 = Bool.false → x12 x5 = Bool.false → ∃ (x15 : ℕ → Bool), (∀ x16 < x1, x15 x16 = Decidable.decide (x16 = x6)) ∧ (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) (x18 x19 : ℕ), x2.gates[x16]? = Option.some x17 → x17.inputs = [x18, x19] → (x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x15 (x1 + x16) = (x12 x18 && x15 x19 || x15 x18 && x12 x19)) ∧ (x17.op = PEqualNP.CircuitLowerBounds.GateOp.or → x15 (x1 + x16) = (x15 x18 || x15 x19))) ∧ x15 x2.output = Bool.false) := by
  exact PEqualNP.Outside.L_meta_18917.Helpers.terminal
