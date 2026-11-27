import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1758_aux

open PEqualNP.CircuitLowerBounds


open PEqualNP.CircuitLowerBounds

def chk (n : ℕ) : List Gate → Bool
  | [] => true
  | g :: gs => g.inputs.all (fun i => decide (i < n)) && chk (n + 1) gs

theorem chk_spec : ∀ (gs : List Gate) (n : ℕ), chk n gs = true →
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | g :: gs, n, h, 0, _, i, hi => by
    simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simpa using h.1 i (by simpa using hi)
  | g :: gs, n, h, j + 1, hj, i, hi => by
    simp only [chk, Bool.and_eq_true] at h
    have := chk_spec gs (n + 1) h.2 j (by simpa using hj) i (by simpa using hi)
    omega

def Inv (w : List Bool) (m : ℕ) : Prop :=
  (∀ i, w.getD i false = m.testBit i) ∧ (∀ i, w.length ≤ i → m.testBit i = false)

theorem step_inv (w : List Bool) (m : ℕ) (b : Bool) (h : Inv w m) :
    Inv (w ++ [b]) (if b then m ||| 2 ^ w.length else m) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro i
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ hi, h1]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow] <;> omega
    · rw [List.getD_append_right _ _ _ _ le_rfl]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow, h2]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      cases b <;> simp [Nat.testBit_or, h2 i hi.le, Nat.testBit_two_pow] <;> omega
  · intro i hi
    simp at hi
    cases b <;> simp [Nat.testBit_or, h2 i (by omega), Nat.testBit_two_pow] <;> omega

def mk : ℕ → ℕ → List Bool → ℕ
  | _, m, [] => m
  | k, m, b :: bs => mk (k + 1) (if b then m ||| 2 ^ k else m) bs

theorem mk_spec : ∀ (bs w : List Bool) (m : ℕ), Inv w m → Inv (w ++ bs) (mk w.length m bs)
  | [], w, m, h => by simpa [mk] using h
  | b :: bs, w, m, h => by
    have := mk_spec bs (w ++ [b]) _ (step_inv w m b h)
    simpa [mk] using this

def run : ℕ → ℕ → List Gate → ℕ
  | _, m, [] => m
  | k, m, g :: gs => run (k + 1) (if g.op.eval (g.inputs.map fun i => m.testBit i) then m ||| 2 ^ k else m) gs

theorem run_spec : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), Inv w m →
    Inv (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) (run w.length m gs)
  | [], w, m, h => by simpa [run] using h
  | g :: gs, w, m, h => by
    have hmap : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => m.testBit i) :=
      List.map_congr_left (fun i _ => h.1 i)
    have := run_spec gs _ _ (step_inv w m (g.op.eval (g.inputs.map fun i => w.getD i false)) h)
    simp only [List.foldl_cons, run]
    rw [hmap] at this ⊢
    simpa using this

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run x.length (mk 0 0 x) C.gates).testBit C.output := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec x [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  exact (run_spec C.gates x _ hx).1 C.output


theorem wires_eq (C : Circuit) (x : List Bool) (i : ℕ) :
    (C.wires x).getD i false = (run x.length (mk 0 0 x) C.gates).testBit i := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec x [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  exact (run_spec C.gates x _ hx).1 i

end PEqualNP.Outside.L_meta_1758_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1758 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [56, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [59, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [62, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [65, 66]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [72, 73]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [75, 76]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [78, 79]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [81, 82]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [80, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [83, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [84, 85]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [80, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [83, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [87, 88]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 89]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 89]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 86]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 86]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [94, 95]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [97, 98]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [99, 83]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [96, 83]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [99, 80]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [96, 80]⟩], 103⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 88 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 16 + p.2) ∧ (∀ i j : Fin 16, (C.wires (List.ofFn fun k : Fin 16 => decide (k = i))).getD ([52, 53, 54, 55, 68, 69, 70, 71, 90, 91, 92, 93, 100, 101, 102, 103].getD j.val 0) false = decide (j.val % 4 = (([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD (i.val / 4) []).getD (j.val / 4) 0 ^^^ i.val % 4))) ∧ (C.wires (List.ofFn fun k : Fin 16 => decide (k.val = 0 ∨ k.val = 3))).getD 53 false = true ∧ ¬ (1 = (([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD 0 []).getD 0 0 ^^^ 0)) ∧ ¬ (1 = (([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD 0 []).getD 0 0 ^^^ 3)) := by
  intro C
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · simp only [PEqualNP.Outside.L_meta_1758_aux.wires_eq]
    set_option maxRecDepth 100000 in decide +kernel
  · rw [PEqualNP.Outside.L_meta_1758_aux.wires_eq]
    set_option maxRecDepth 100000 in decide +kernel
  · decide
  · decide
