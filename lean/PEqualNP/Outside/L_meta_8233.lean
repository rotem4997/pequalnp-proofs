import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_8233

open PEqualNP.CircuitLowerBounds

theorem getD_min {α : Type} (d : List α) (a : α) (hd : d.length ≤ 89) (i : ℕ) :
    d.getD (min i 89) a = d.getD i a := by
  rcases le_total i 89 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.getD_eq_default d a (by omega), List.getD_eq_default d a (by omega)]

def phi (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (fun i => min i 89) }

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (d : List ℕ) (g : Gate) : List ℕ := d ++ [g.lineDegree d]

theorem wstep_phi (w : List Bool) (g : Gate) (hw : w.length ≤ 89) : wstep w (phi g) = wstep w g := by
  simp only [wstep, phi, List.map_map, Function.comp_def, getD_min w false hw]

theorem dstep_phi (d : List ℕ) (g : Gate) (hd : d.length ≤ 89) : dstep d (phi g) = dstep d g := by
  simp only [dstep, Gate.lineDegree, phi, List.map_map, Function.comp_def, getD_min d 0 hd]
  rfl

theorem fold_phi {β : Type} (step : List β → Gate → List β)
    (hstep : ∀ w g, w.length ≤ 89 → step w (phi g) = step w g)
    (hlen : ∀ w g, (step w g).length = w.length + 1) :
    ∀ (G : List Gate) (w : List β), w.length + G.length ≤ 90 →
      (G.map phi).foldl step w = G.foldl step w
  | [], _, _ => rfl
  | g :: G, w, h => by
    simp only [List.length_cons] at h
    simp only [List.map_cons, List.foldl_cons]
    rw [hstep w g (by omega)]
    exact fold_phi step hstep hlen G _ (by rw [hlen]; omega)

theorem fold_len {β : Type} (step : List β → Gate → List β)
    (hlen : ∀ w g, (step w g).length = w.length + 1) :
    ∀ (G : List Gate) (w : List β), (G.foldl step w).length = w.length + G.length
  | [], _ => by simp
  | g :: G, w => by
    simp only [List.foldl_cons, List.length_cons]
    rw [fold_len step hlen G, hlen]
    omega

def opBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | _ => false

def e1 (g : Gate) : Option (Fin 90) := g.inputs.head?.map (fun i => ⟨min i 89, by omega⟩)

def e2 (g : Gate) : Option (Fin 90) := g.inputs.tail.head?.map (fun i => ⟨min i 89, by omega⟩)

def enc (g : Gate) : Gate :=
  { op := if opBit g = true then GateOp.and else GateOp.or,
    inputs := List.filterMap (Option.map Fin.val) [e1 g, e2 g] }

theorem enc_eq (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    enc g = phi g := by
  obtain ⟨hop, hlen⟩ := h
  rcases g with ⟨op, ins⟩
  unfold enc phi
  congr 1
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl <;> rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp at hlen

end PEqualNP.Outside.L_meta_8233

open PEqualNP.Outside.L_meta_8233 in
theorem PEqualNP.Outside.L_meta_8233 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size < (64 : ℕ) →       ∃ (x4 : Fin (64 : ℕ)) (x5 : Fin (90 : ℕ)) (x6 : Fin ↑x4 → Bool) (x7 : Fin ↑x4 → Option (Fin (90 : ℕ))) (x8 : Fin ↑x4 → Option (Fin (90 : ℕ))),         have x9 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x9 : Fin ↑x4) => { op := if x6 x9 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.filterMap (Option.map Fin.val) [x7 x9, x8 x9] : PEqualNP.CircuitLowerBounds.Gate }, output := ↑x5 : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 ∧ ∀ (x10 : Finset ℕ), x9.lineDeg (26 : ℕ) x10 = x1.lineDeg (26 : ℕ) x10 := by
  intro C hC hs
  have hs' : C.gates.length < 64 := hs
  refine ⟨⟨C.gates.length, hs⟩, ⟨min C.output 89, by omega⟩,
    fun j => opBit (C.gates.get j), fun j => e1 (C.gates.get j), fun j => e2 (C.gates.get j), ?_⟩
  have hD : (List.ofFn fun j : Fin C.gates.length => enc (C.gates.get j)) = C.gates.map phi := by
    rw [show (fun j : Fin C.gates.length => enc (C.gates.get j)) = enc ∘ C.gates.get from rfl,
      ← List.map_ofFn, List.ofFn_get]
    exact List.map_congr_left (fun g hg => enc_eq g (hC g hg))
  show PEqualNP.MetaComplexity.circuitFun 26
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (List.ofFn fun j : Fin C.gates.length => enc (C.gates.get j)) (min C.output 89)) =
      PEqualNP.MetaComplexity.circuitFun 26 C ∧ ∀ x10 : Finset ℕ,
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (List.ofFn fun j : Fin C.gates.length => enc (C.gates.get j)) (min C.output 89)).lineDeg 26 x10 =
      C.lineDeg 26 x10
  rw [hD]
  have hwl : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate), (wstep w g).length = w.length + 1 := by
    intro w g; simp [wstep]
  have hdl : ∀ (w : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), (dstep w g).length = w.length + 1 := by
    intro w g; simp [dstep]
  constructor
  · funext x
    show (List.foldl wstep (List.ofFn x) (C.gates.map phi)).getD (min C.output 89) false =
      (List.foldl wstep (List.ofFn x) C.gates).getD C.output false
    rw [fold_phi wstep wstep_phi hwl C.gates (List.ofFn x) (by simp; omega)]
    exact getD_min _ _ (by rw [fold_len wstep hwl]; simp; omega) _
  · intro m
    show (List.foldl dstep ((List.range 26).map fun i => if i ∈ m then 1 else 0) (C.gates.map phi)).getD
        (min C.output 89) 0 =
      (List.foldl dstep ((List.range 26).map fun i => if i ∈ m then 1 else 0) C.gates).getD C.output 0
    rw [fold_phi dstep dstep_phi hdl C.gates _ (by simp; omega)]
    exact getD_min _ _ (by rw [fold_len dstep hdl]; simp; omega) _
