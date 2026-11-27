import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1741_aux

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

def mchk (gs : List Gate) : Bool :=
  gs.all (fun g => (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | _ => false) && decide (g.inputs.length = 2))

theorem mchk_spec (gs : List Gate) (h : mchk gs = true) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [mchk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  cases hop : g.op <;> simp_all


theorem wires_eq (C : Circuit) (x : List Bool) (i : ℕ) :
    (C.wires x).getD i false = (run x.length (mk 0 0 x) C.gates).testBit i := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec x [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  exact (run_spec C.gates x _ hx).1 i

end PEqualNP.Outside.L_meta_1741_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1741 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 68] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [70, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [82, 53] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 77] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 92] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 93] }], output := 94 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 69 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
  (∀ Y : Finset (Fin 13), Y.card ≤ 3 →
     C.eval (List.ofFn (fun u1 : Fin 13 => decide (∀ l ∈ Y, u1 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))))
             ++ List.ofFn (fun v1 : Fin 13 => decide (v1 ∈ Y))) = false) ∧
  (∀ l : Fin 13, (C.wires (List.replicate 13 false ++ List.ofFn (fun v2 : Fin 13 => decide (v2 = l)))).getD 92 false
       = decide (l = 0 ∨ l = 4)) ∧
  (C.wires (List.replicate 13 false ++ List.ofFn (fun v3 : Fin 13 => decide (v3 = 10 ∨ v3 = 12)))).getD 92 false = true := by
  intro C hC
  subst hC
  refine ⟨rfl, fun j hj i hi => PEqualNP.Outside.L_meta_1741_aux.chk_spec _ 26 (by decide +kernel) j hj i hi, PEqualNP.Outside.L_meta_1741_aux.mchk_spec _ (by decide +kernel), ?_, ?_, ?_, ?_⟩
  · simp only [PEqualNP.Outside.L_meta_1741_aux.eval_eq]
    set_option maxRecDepth 100000 in decide +kernel
  · intro Y hY
    have hc : Y.card = 0 ∨ Y.card = 1 ∨ Y.card = 2 ∨ Y.card = 3 := by omega
    rcases hc with h | h | h | h
    · rw [Finset.card_eq_zero] at h
      subst h
      rw [PEqualNP.Outside.L_meta_1741_aux.eval_eq]
      decide +kernel
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
      simp only [Finset.mem_singleton, forall_eq, PEqualNP.Outside.L_meta_1741_aux.eval_eq]
      revert a
      set_option maxRecDepth 100000 in decide +kernel
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, PEqualNP.Outside.L_meta_1741_aux.eval_eq]
      revert a b
      set_option maxRecDepth 100000 in decide +kernel
    · obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.mp h
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, PEqualNP.Outside.L_meta_1741_aux.eval_eq]
      revert a b c
      set_option maxRecDepth 100000 in decide +kernel
  · simp only [PEqualNP.Outside.L_meta_1741_aux.wires_eq]
    set_option maxRecDepth 100000 in decide +kernel
  · rw [PEqualNP.Outside.L_meta_1741_aux.wires_eq]
    decide +kernel
