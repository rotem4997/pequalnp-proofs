import PEqualNP.Defs
import PEqualNP.Library.L004
import Mathlib.Tactic

/-!
# A circuit reading a prefix of a longer input

From the circuit simulation, every language in P is decided on the first `2^m` bits of an
input of any length `N >= 2^m` by a circuit of size polynomial in `2^m`.
-/

namespace PEqualNP.Library.Helpers.RRDistinguisher

open PEqualNP.CircuitLowerBounds

/-- Shift a wire index past the extra input bits. -/
def shiftIdx (M N i : ℕ) : ℕ := if i < M then i else i + (N - M)

/-- Re-index a circuit built for inputs of length `M` to read inputs of length `N`. -/
def shiftCircuit (M N : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (shiftIdx M N)⟩), shiftIdx M N C.output⟩

theorem getD_shift (M N : ℕ) (T u : List Bool) (hM : M ≤ N) (hT : T.length = N) (i : ℕ) :
    (T ++ u).getD (shiftIdx M N i) false = (T.take M ++ u).getD i false := by
  have hTM : (T.take M).length = M := by simp [hT, hM]
  unfold shiftIdx
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hT, hTM]
    congr 2
    omega

theorem fold_shift (M N : ℕ) (T : List Bool) (hM : M ≤ N) (hT : T.length = N) :
    ∀ (gs : List Gate) (u : List Bool), ∃ u' : List Bool,
      (gs.map (fun g => (⟨g.op, g.inputs.map (shiftIdx M N)⟩ : Gate))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (T ++ u)
        = T ++ u' ∧
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (T.take M ++ u) = T.take M ++ u' := by
  intro gs
  induction gs with
  | nil => intro u; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u
    have key : (g.inputs.map (shiftIdx M N)).map (fun i => (T ++ u).getD i false)
        = g.inputs.map (fun i => (T.take M ++ u).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_shift M N T u hM hT i)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [g.op.eval (g.inputs.map fun i => (T.take M ++ u).getD i false)])
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, List.foldl_cons]
      rw [key, List.append_assoc]
      exact h1
    · simp only [List.foldl_cons]
      rw [List.append_assoc]
      exact h2

theorem eval_shift (M N : ℕ) (C : Circuit) (T : List Bool) (hM : M ≤ N) (hT : T.length = N) :
    (shiftCircuit M N C).eval T = C.eval (T.take M) := by
  obtain ⟨u', h1, h2⟩ := fold_shift M N T hM hT C.gates []
  simp only [List.append_nil] at h1 h2
  unfold Circuit.eval Circuit.wires shiftCircuit
  simp only
  rw [h1, h2]
  have := getD_shift M N T u' hM hT C.output
  exact this

theorem arith (k m : ℕ) :
    ((2 ^ m) ^ k + k + 2 ^ m + 1) ^ 3 ≤ (k + 3) ^ 3 * 2 ^ (3 * (k + 1) * m) := by
  set X := 2 ^ m with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hp : X ^ k ≤ X ^ (k + 1) := Nat.pow_le_pow_right hX1 (by omega)
  have hq : X ≤ X ^ (k + 1) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (k + 1) := Nat.pow_le_pow_right hX1 (by omega)
  have h1 : 1 ≤ X ^ (k + 1) := Nat.one_le_pow _ _ hX1
  have hk : k ≤ k * X ^ (k + 1) := Nat.le_mul_of_pos_right _ h1
  have hb : X ^ k + k + X + 1 ≤ (k + 3) * X ^ (k + 1) := by nlinarith
  have he : 2 ^ (3 * (k + 1) * m) = (X ^ (k + 1)) ^ 3 := by
    rw [hX, ← pow_mul, ← pow_mul]; congr 1; ring
  rw [he, ← mul_pow]
  exact Nat.pow_le_pow_left hb 3

theorem linkA : (∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → ∃ c : ℕ, L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3)) → ∀ Q : Language Bool, Q ∈ PEqualNP.Library.P → ∃ c d : ℕ, ∀ m N : ℕ, 2 ^ m ≤ N → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size ≤ c * 2 ^ (d * m) ∧ ∀ T : List Bool, T.length = N → (D.eval T = true ↔ T.take (2 ^ m) ∈ Q) := by
  intro H Q hQ
  obtain ⟨k, hk⟩ := (PEqualNP.Library.L004 Q).1 hQ
  obtain ⟨c', hc'⟩ := H _ Q hk
  refine ⟨c' * (k + 3) ^ 3, 3 * (k + 1), fun m N hN => ?_⟩
  obtain ⟨C, -, hsize, hdec⟩ := hc' (2 ^ m)
  refine ⟨shiftCircuit (2 ^ m) N C, ?_, fun T hT => ?_⟩
  · have hs : (shiftCircuit (2 ^ m) N C).size = C.size := by
      simp [shiftCircuit, Circuit.size]
    rw [hs]
    calc C.size ≤ c' * ((2 ^ m) ^ k + k + 2 ^ m + 1) ^ 3 := hsize
      _ ≤ c' * ((k + 3) ^ 3 * 2 ^ (3 * (k + 1) * m)) := Nat.mul_le_mul_left _ (arith k m)
      _ = c' * (k + 3) ^ 3 * 2 ^ (3 * (k + 1) * m) := by ring
  · rw [eval_shift (2 ^ m) N C T hN hT]
    exact hdec _ (by simp [hT, hN])

end PEqualNP.Library.Helpers.RRDistinguisher
