import PEqualNP.Library.Helpers.ReplayCol

/-!
# One output wire against an explicit column expression (seat-gct-2)

A cheaper certificate than `ReplayCol.colReplay` when the target is given as a formula over input bits. Instead of
`table n f`, which evaluates `f` on all `2 ^ n` inputs, the target column is written as an expression `E` over the
input columns `inCol n i` (with `&&&`, `|||`, `^^^` and `mask n`). The fact that `E`'s bits are `f` is shown once,
symbolically, by `Nat.testBit_and`, `Nat.testBit_or` and `inCol_bit`, with no enumeration. Then each output wire is ONE
comparison of two `2 ^ n`-bit numbers, decided by `decide +kernel`.

Measured (26 Nov 2026, locally, not a check): the 3 by 3 Boolean matrix product's nine outputs with the 45-gate
schoolbook circuit build in 3.6 s this way, against about 450 s through `table`.

Names: `inCol_bit` (input bit `i` from its column, for a natural-number index), `wire_of_expr` (soundness).
-/

namespace PEqualNP.Library.Helpers.ReplayColExpr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Library.Helpers.Replay
  PEqualNP.Library.Helpers.ReplayCol

/-- Input bit `i` read off its column, for a natural-number index. -/
theorem inCol_bit {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (inCol n i).testBit (tableIndex x) = x ⟨i, hi⟩ :=
  testBit_inCol x ⟨i, hi⟩

/-- One output wire by columns, against an explicit column `E` whose bits are `f`: no evaluation of `f` on all
inputs. -/
theorem wire_of_expr {n : ℕ} {C : Circuit} {f : (Fin n → Bool) → Bool} (o E : ℕ) (hg : aonB C = true)
    (h : ((wireCols n C).getD o 0 == E) = true)
    (hE : ∀ x : Fin n → Bool, E.testBit (tableIndex x) = f x) :
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o false = f x := by
  intro x
  have hg' : ∀ g ∈ C.gates, isAONB g.op = true := fun g hg2 => List.all_eq_true.mp hg g hg2
  have hA := agree_foldl (PEqualNP.MetaComplexity.Helpers.tableIndex_lt x) C.gates _ _ hg' (agree_inputs x)
  have := hA.2 o
  rw [show C.gates.foldl _ (List.ofFn fun i : Fin n => inCol n i) = wireCols n C from rfl,
    beq_iff_eq.mp h, hE] at this
  exact this.symm

end PEqualNP.Library.Helpers.ReplayColExpr
