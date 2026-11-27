import Mathlib.Tactic

/-!
# Unary strings and a self-delimiting pair of bit strings

Helper module (proofs only, no statement may use it).
-/

namespace PEqualNP.Library.Universal

/-- Unary. -/
def un (n : ℕ) : List Bool := List.replicate n true

/-- Self-delimiting pair of bit strings: length of the first in unary, a `false`, then both. -/
def pairB (a b : List Bool) : List Bool := un a.length ++ false :: (a ++ b)

/-- Total inverse of `pairB`. -/
def unpairB (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
   ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem unpairB_pairB (a b : List Bool) : unpairB (pairB a b) = (a, b) := by
  have h1 : (pairB a b).takeWhile id = un a.length := by
    simp [pairB, un]
  have h2 : (pairB a b).dropWhile id = false :: (a ++ b) := by
    simp [pairB, un]
  simp [unpairB, h1, h2, un]

end PEqualNP.Library.Universal
