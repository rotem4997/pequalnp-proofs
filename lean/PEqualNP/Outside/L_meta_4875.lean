import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4875
open PEqualNP.CircuitLowerBounds



def bitf (m : ℕ) : Fin 13 → Bool := fun i => m.testBit i.1

def miss (x : Fin 13 → Bool) : Fin 13 → Bool :=
  fun l => !(x l || x (l + 1) || x (l + 3) || x (l + 9))

def chk (m : ℕ) : Bool :=
  decide ((List.ofFn (bitf m)).count true ≤ 3) || decide ((List.ofFn (miss (bitf m))).count true ≤ 3)

set_option maxRecDepth 100000 in
theorem all_ok : (List.range 8192).all chk = true := by decide +kernel

end PEqualNP.Outside.L_meta_4875

open PEqualNP.Outside.L_meta_4875 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4875 : have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); ∀ (x2 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x2) ≤ (3 : ℕ) ∨ List.count Bool.true (List.ofFn (x1 x2)) ≤ (3 : ℕ) := by
  intro F x
  have hm : Nat.ofBits x < 8192 := Nat.ofBits_lt_two_pow x
  have hx : bitf (Nat.ofBits x) = x := funext fun i => Nat.testBit_ofBits_lt x i.1 i.2
  have h := List.all_eq_true.1 all_ok (Nat.ofBits x) (List.mem_range.2 hm)
  unfold chk at h
  rw [hx, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
  exact h
