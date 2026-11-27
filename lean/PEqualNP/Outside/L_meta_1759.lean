import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1759_aux

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

end PEqualNP.Outside.L_meta_1759_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1759 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [44, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [47, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [48, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [50, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [51, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [53, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [54, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [46, 52]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [49, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [46, 49]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [52, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 66]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 65]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [72, 73]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [75, 76]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [62, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [78, 79]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [62, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [81, 82]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 80]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 83]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 80]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 83]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 84]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 86]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 85]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 87]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [92, 93]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [95, 96]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [62, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [98, 99]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [62, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [101, 102]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [100, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [103, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [104, 105]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [100, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [103, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [107, 108]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [94, 106]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [94, 109]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [97, 106]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [97, 109]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 110]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 112]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 111]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 113]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [118, 119]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [60, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [121, 122]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [120, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [123, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [124, 125]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [120, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [123, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [127, 128]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [62, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [130, 131]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [62, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [133, 134]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [126, 132]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [126, 135]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [129, 132]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [129, 135]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 136]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 138]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 137]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 139]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [68, 69]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [144, 70]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [145, 71]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [146, 88]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [147, 89]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [148, 90]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [149, 91]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [150, 114]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [151, 115]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [152, 116]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [153, 117]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [154, 140]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [155, 141]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [156, 142]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [157, 143]⟩], 158⟩ : PEqualNP.CircuitLowerBounds.Circuit); let F : (Fin 32 → Bool) → Bool := fun x => (x 0 && x 16) || (x 4 && x 16) || (x 8 && x 16) || (x 12 && x 16) || (x 1 && x 17) || (x 5 && x 17) || (x 9 && x 17) || (x 13 && x 17) || (x 2 && x 18) || (x 6 && x 18) || (x 10 && x 18) || (x 14 && x 18) || (x 3 && x 19) || (x 7 && x 19) || (x 11 && x 19) || (x 15 && x 19) || (x 0 && x 20) || (x 5 && x 20) || (x 10 && x 20) || (x 15 && x 20) || (x 1 && x 21) || (x 4 && x 21) || (x 11 && x 21) || (x 14 && x 21) || (x 2 && x 22) || (x 7 && x 22) || (x 8 && x 22) || (x 13 && x 22) || (x 3 && x 23) || (x 6 && x 23) || (x 9 && x 23) || (x 12 && x 23) || (x 0 && x 24) || (x 6 && x 24) || (x 11 && x 24) || (x 13 && x 24) || (x 1 && x 25) || (x 7 && x 25) || (x 10 && x 25) || (x 12 && x 25) || (x 2 && x 26) || (x 4 && x 26) || (x 9 && x 26) || (x 15 && x 26) || (x 3 && x 27) || (x 5 && x 27) || (x 8 && x 27) || (x 14 && x 27) || (x 0 && x 28) || (x 7 && x 28) || (x 9 && x 28) || (x 14 && x 28) || (x 1 && x 29) || (x 6 && x 29) || (x 8 && x 29) || (x 15 && x 29) || (x 2 && x 30) || (x 5 && x 30) || (x 11 && x 30) || (x 12 && x 30) || (x 3 && x 31) || (x 4 && x 31) || (x 10 && x 31) || (x 13 && x 31); C.gates.length = 127 ∧ C.output = 158 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 32 + p.2) ∧ ∀ i j : Fin 32, i < j → F (fun k : Fin 32 => decide (k = i ∨ k = j)) = true → C.eval (List.ofFn (fun k : Fin 32 => decide (k = i ∨ k = j))) = true := by
  intro C F
  refine ⟨rfl, rfl, ?_, ?_⟩
  · decide +kernel
  · simp only [PEqualNP.Outside.L_meta_1759_aux.eval_eq]
    set_option maxRecDepth 100000 in decide +kernel
