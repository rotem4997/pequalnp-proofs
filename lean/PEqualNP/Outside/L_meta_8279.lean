import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8279_aux

open PEqualNP.CircuitLowerBounds

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def desc (g : Gate) : Bool × Fin 89 × Fin 89 :=
  (isAnd g.op,
    ⟨min (g.inputs.getD 0 0) (g.inputs.getD 1 0) % 89, Nat.mod_lt _ (by norm_num)⟩,
    ⟨max (g.inputs.getD 0 0) (g.inputs.getD 1 0) % 89, Nat.mod_lt _ (by norm_num)⟩)

def step (x5 : List Bool) (x6 : Bool × Fin 89 × Fin 89) : List Bool :=
  x5 ++ [bif x6.1 then x5.getD (↑x6.2.1) Bool.false && x5.getD (↑x6.2.2) Bool.false else x5.getD (↑x6.2.1) Bool.false || x5.getD (↑x6.2.2) Bool.false]

def Good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < 89

theorem gate_eq (g : Gate) (hg : Good g) (w : List Bool) :
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] = step w (desc g) := by
  obtain ⟨hop, hl, hi⟩ := hg
  match g, hop, hl, hi with
  | ⟨op, [a, b]⟩, hop, _, hi =>
    have ha : a < 89 := hi a (by simp)
    have hb : b < 89 := hi b (by simp)
    simp only at hop
    rcases hop with rfl | rfl <;>
    · simp only [step, desc, isAnd, GateOp.eval, List.getD_cons_zero, List.getD_cons_succ]
      rcases le_total a b with h | h
      · simp [min_eq_left h, max_eq_right h, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      · simp [min_eq_right h, max_eq_left h, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Bool.and_comm, Bool.or_comm]

theorem fold_eq : ∀ (gs : List Gate), (∀ g ∈ gs, Good g) → ∀ acc : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc
      = (gs.map desc).foldl step acc := by
  intro gs
  induction gs with
  | nil => intro _ acc; rfl
  | cons g t ih =>
    intro h acc
    simp only [List.foldl_cons, List.map_cons]
    rw [gate_eq g (h g (by simp))]
    exact ih (fun g' hg' => h g' (by simp [hg'])) _

end PEqualNP.Outside.L_meta_8279_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_8279_aux in
theorem PEqualNP.Outside.L_meta_8279 : have x1 : (Fin (63 : ℕ) → Bool) → (Fin (63 : ℕ) → Fin (89 : ℕ)) → (Fin (63 : ℕ) → Fin (89 : ℕ)) → (Fin (26 : ℕ) → Bool) → Bool := fun (x1 : Fin (63 : ℕ) → Bool) (x2 x3 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x4 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x5 : List Bool) (x6 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x5 ++ [bif x6.1 then x5.getD (↑x6.2.1) Bool.false && x5.getD (↑x6.2.2) Bool.false else x5.getD (↑x6.2.1) Bool.false || x5.getD (↑x6.2.2) Bool.false]) (List.ofFn x4) (List.ofFn fun (x5 : Fin (63 : ℕ)) => (x1 x5, x2 x5, x3 x5))).getD (88 : ℕ) Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → x2.size = (63 : ℕ) → x2.output = (88 : ℕ) → ∃ (x6 : Fin (63 : ℕ) → Bool) (x7 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x8 : Fin (63 : ℕ) → Fin (89 : ℕ)), (∀ (x9 : Fin (63 : ℕ)), ↑(x7 x9) < (26 : ℕ) + ↑x9 ∧ ↑(x8 x9) < (26 : ℕ) + ↑x9 ∧ x7 x9 ≤ x8 x9) ∧ ∀ (x9 : Fin (26 : ℕ) → Bool), x1 x6 x7 x8 x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x9 := by
  intro x1 C hC hs ho
  obtain ⟨hop, hrb, hl⟩ := hC
  have hgood : ∀ g ∈ C.gates, Good g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    refine ⟨hop _ hg, hl _ hg, ?_⟩
    intro i hi
    have h1 := hrb j hj i (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hj] using hi)
    have : C.gates.length = 63 := hs
    omega
  refine ⟨fun j => (desc (C.gates.getD j ⟨GateOp.or, []⟩)).1,
    fun j => (desc (C.gates.getD j ⟨GateOp.or, []⟩)).2.1,
    fun j => (desc (C.gates.getD j ⟨GateOp.or, []⟩)).2.2, ?_, ?_⟩
  · intro j
    have hlen : C.gates.length = 63 := hs
    have hj : (j : ℕ) < C.gates.length := by omega
    have hg : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[(j : ℕ)] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    have hrj := hrb j hj
    have hl2 := hl _ (List.getElem_mem hj)
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hrj
    beta_reduce
    rw [hg]
    generalize C.gates[(j : ℕ)] = g at hrj hl2
    obtain ⟨op, ins⟩ := g
    match ins, hl2, hrj with
    | [a, b], _, hr =>
      have ha := hr a (by simp)
      have hb := hr b (by simp)
      have j63 := j.isLt
      simp only [desc, List.getD_cons_zero, List.getD_cons_succ, Fin.le_def]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · intro x9
    have hD : (List.ofFn fun (x5 : Fin 63) => ((desc (C.gates.getD x5 ⟨GateOp.or, []⟩)).1,
        (desc (C.gates.getD x5 ⟨GateOp.or, []⟩)).2.1, (desc (C.gates.getD x5 ⟨GateOp.or, []⟩)).2.2))
        = C.gates.map desc := by
      have : C.gates.length = 63 := hs
      apply List.ext_getElem
      · simp [this]
      · intro n h1 h2
        have h3 : n < C.gates.length := by simpa using h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3, Option.getD_some]
    show (List.foldl step (List.ofFn x9) _).getD 88 false = _
    rw [hD, ← fold_eq C.gates hgood]
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires, ho]
