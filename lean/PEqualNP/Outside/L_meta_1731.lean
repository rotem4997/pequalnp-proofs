import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1731_aux

open PEqualNP.CircuitLowerBounds

def opok : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def mchk : List Gate → Bool
  | [] => true
  | g :: gs => opok g.op && decide (g.inputs.length ≤ 2) && mchk gs

theorem mchk_spec : ∀ (gs : List Gate), mchk gs = true →
    ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  | [], _, g, hg => absurd hg (by simp)
  | g :: gs, h, g', hg' => by
    simp only [mchk, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hg' with rfl | hm
    · refine ⟨?_, h.1.2⟩
      have h1 := h.1.1
      revert h1
      cases g'.op <;> simp [opok]
    · exact mchk_spec gs h.2 g' hm

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

end PEqualNP.Outside.L_meta_1731_aux

theorem PEqualNP.Outside.L_meta_1731 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [44, 52]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 53]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [46, 54]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [47, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [48, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [49, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [50, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [51, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [52, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [53, 61]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [54, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [55, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [56, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [57, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [58, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [59, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [60, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [61, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [62, 49]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 97]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [64, 98]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [65, 99]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [66, 100]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [67, 101]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [68, 102]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [69, 103]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [70, 104]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [71, 84]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [72, 85]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [73, 86]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 87]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [75, 88]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [76, 89]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 90]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [78, 91]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [79, 92]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [80, 93]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [81, 94]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [82, 95]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [83, 96]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [105, 106]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [126, 107]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [127, 108]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [128, 109]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [129, 110]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [130, 111]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [131, 112]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [132, 113]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [133, 114]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [134, 115]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [135, 116]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [136, 117]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [137, 118]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [138, 119]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [139, 120]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [140, 121]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [141, 122]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [142, 123]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [143, 124]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [144, 125]⟩], output := 145 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 104 ∧ (∀ p l : Fin 21, (p.val + l.val) % 21 ∈ ([0, 1, 4, 14, 16] : List ℕ) → C.eval (List.ofFn (fun i : Fin 42 => decide (i.val = p.val ∨ i.val = 21 + l.val))) = true) ∧ (∀ p l : Fin 21, (p.val + l.val) % 21 ∈ ([0, 1, 4, 14, 16] : List ℕ) → ¬ (Nat.testBit 8892411 p.val = true ∧ Nat.testBit 8892411 (21 + l.val) = true)) ∧ C.eval (List.ofFn (fun j : Fin 42 => Nat.testBit 8892411 j.val)) = true := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1731_aux.mchk_spec _ (by decide +kernel)
  · rfl
  · simp only [PEqualNP.Outside.L_meta_1731_aux.eval_eq]
    set_option maxRecDepth 100000 in decide +kernel
  · set_option maxRecDepth 100000 in decide +kernel
  · rw [PEqualNP.Outside.L_meta_1731_aux.eval_eq]
    set_option maxRecDepth 100000 in decide +kernel
