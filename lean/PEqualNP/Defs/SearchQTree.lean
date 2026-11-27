import PEqualNP.Defs.SearchQ

/-!
# Definitions of the P = NP algorithm search: tree-like Res(lin) over the integers

A tree-like derivation of a line: every node is derived from its own children, never from a
shared line, so a line used twice is derived twice. The rules are those of
`IsResLinQDerivation` (axiom, resolution on the first equations, semantic weakening from one
line). The size counts nodes, that is lines, so a lower bound on it is a lower bound on the
number of lines of a tree-like refutation (and on its bit size).
-/

namespace PEqualNP.Search

/-- A tree-like Res(lin) derivation over the integers of the line `L` from the clauses `F`. -/
inductive ResLinQTree {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) : QLine V → Type
  | ax {L : QLine V} (C : PEqualNP.ProofComplexity.Clause V) :
      C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) → ResLinQTree F L
  | res {e e' : QEq V} {C D : QLine V} (α β : ℤ) :
      ResLinQTree F (e :: C) → ResLinQTree F (e' :: D) →
      ResLinQTree F ((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D))
  | weaken {C D : QLine V} :
      ResLinQTree F C → (∀ a : V → Bool, QLine.Holds a C → QLine.Holds a D) →
      ResLinQTree F D

/-- The number of nodes (lines) of a tree-like derivation. -/
def ResLinQTree.size {V : Type} [Fintype V] [DecidableEq V]
    {F : Set (PEqualNP.ProofComplexity.Clause V)} : {L : QLine V} → ResLinQTree F L → ℕ
  | _, .ax _ _ _ => 1
  | _, .res _ _ t t' => t.size + t'.size + 1
  | _, .weaken t _ => t.size + 1

end PEqualNP.Search
