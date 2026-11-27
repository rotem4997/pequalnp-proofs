import PEqualNP.MetaComplexity.Helpers.RunAsm5

/-!
# Run-of-four assembly, part 6: the end statement split into (P-OO) and (P-Q2)

Paper: the run-of-four argument in direct form, section 5, (P-OO) and (P-Q2)/(P-QA).

* `AsmShapeI`: shape (i) at the end `e`, in the form the checked row L-meta-596 reads (two
  distinct AND gates, each the only reader of one OR reader of `x_e`; each `u_k` an input or a
  wire with a second reader).
* `AsmPOO` (Lemma OO4 in direct form; a pure circuit statement): state OO at an input `e` of a
  least list with `x_e := 1` not constant gives Drop 5 at `x_e := 1` or shape (i).
* `AsmPQ2` (the q2 side with Theorem QA): at a run end in state OO, shape (i), and no Drop 5 at
  `x_e := 1`, one of the three other end outcomes.
* `asm_end_of`: the two give `AsmEndOO`, hence (`asm_L658_of_end`) the row.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- Shape (i) at the OR readers `p1`, `p2` (operands `u1`, `u2` beside `x_e`) of a list on
`N` inputs. -/
def AsmShapeI (N : ℕ) (gs : List Gate) (p1 p2 u1 u2 : ℕ) : Prop :=
  ∃ (a1 a2 : ℕ) (ga1 ga2 : Gate) (w1 w2 : ℕ), a1 ≠ a2 ∧ p1 < a1 ∧ p2 < a2 ∧
    gs[a1]? = some ga1 ∧ ga1.op = GateOp.and ∧
    (ga1.inputs = [N + p1, w1] ∨ ga1.inputs = [w1, N + p1]) ∧
    gs[a2]? = some ga2 ∧ ga2.op = GateOp.and ∧
    (ga2.inputs = [N + p2, w2] ∨ ga2.inputs = [w2, N + p2]) ∧
    (∀ t, Reads gs t (N + p1) → t = a1) ∧ (∀ t, Reads gs t (N + p2) → t = a2) ∧
    (u1 < N ∨ ∃ t, t ≠ p1 ∧ Reads gs t u1) ∧ (u2 < N ∨ ∃ t, t ≠ p2 ∧ Reads gs t u2)

/-- (P-OO), direct form: Lemma OO4 on a least list. -/
def AsmPOO : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ) (e : Fin (n + 1))
    (p1 p2 : ℕ) (g1 g2 : Gate) (u1 u2 : ℕ),
    Least (n + 1) f gs o →
    (∃ x x' : Fin (n + 1) → Bool, f (Function.update x e true) ≠ f (Function.update x' e true)) →
    gs[p1]? = some g1 → g1.op = GateOp.or → (g1.inputs = [(e : ℕ), u1] ∨ g1.inputs = [u1, e]) →
    gs[p2]? = some g2 → g2.op = GateOp.or → (g2.inputs = [(e : ℕ), u2] ∨ g2.inputs = [u2, e]) →
    p1 ≠ p2 → (∀ t, Reads gs t e → t = p1 ∨ t = p2) →
    Drop f e true 5 gs.length ∨ AsmShapeI (n + 1) gs p1 p2 u1 u2

/-- (P-Q2) with Theorem QA, direct form, at the end `q1` of a run of four. -/
def AsmPQ2 : Prop :=
  asmChain → ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (q0 q1 q2 q3 q4 q5 : Fin (n + 1))
    (gs : List Gate) (o p1 p2 : ℕ) (g1 g2 : Gate) (u1 u2 : ℕ),
    r4Run G q0 q1 q2 q3 q4 q5 → Least (n + 1) (F G ∅) gs o →
    gs[p1]? = some g1 → g1.op = GateOp.or → (g1.inputs = [(q1 : ℕ), u1] ∨ g1.inputs = [u1, q1]) →
    gs[p2]? = some g2 → g2.op = GateOp.or → (g2.inputs = [(q1 : ℕ), u2] ∨ g2.inputs = [u2, q1]) →
    p1 ≠ p2 → (∀ t, Reads gs t q1 → t = p1 ∨ t = p2) →
    AsmShapeI (n + 1) gs p1 p2 u1 u2 → ¬ Drop (F G ∅) q1 true 5 gs.length →
    Drop (F G ∅) q2 false 3 gs.length ∨ Drop (F G ∅) q2 true 4 gs.length ∨
      ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (n + 1)
        (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s'

theorem asm_end_of (hP : AsmPOO) (hQ : AsmPQ2) : AsmEndOO := by
  intro hch n G q0 q1 q2 q3 q4 q5 gs o p1 p2 g1 g2 u1 u2 r L hg1 ho1 hu1 hg2 ho2 hu2 h12 hall
  have hnc : ∃ x x' : Fin (n + 1) → Bool,
      F G ∅ (Function.update x q1 true) ≠ F G ∅ (Function.update x' q1 true) := by
    obtain ⟨hD, -⟩ := r4_stmtG3 n G ∅ q0 q1 q2 q3 q4 q5 (fun i _ _ h => Finset.notMem_empty i h) r
    exact hD.nc q1 (by simp) true
  by_cases h5 : Drop (F G ∅) q1 true 5 gs.length
  · exact Or.inl h5
  rcases hP n (F G ∅) gs o q1 p1 p2 g1 g2 u1 u2 L hnc hg1 ho1 hu1 hg2 ho2 hu2 h12 hall with
    h | hS
  · exact absurd h h5
  · exact Or.inr (hQ hch n G q0 q1 q2 q3 q4 q5 gs o p1 p2 g1 g2 u1 u2 r L hg1 ho1 hu1 hg2 ho2 hu2
      h12 hall hS h5)

end PEqualNP.MetaComplexity.Helpers.RunAsm
