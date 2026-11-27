import PEqualNP.MetaComplexity.Helpers.EdgeFnPlan

/-!
# The base-point form of the semantic hypotheses (primed statements of the edge function plan)

`DeepHyp'` is `DeepHyp` with H5 ("`F` is false at the all-false input") weakened to "some point
`z0`, false on `D`, with `F z0 = false`". Field names are kept. The primed statements below are
the old ones with `DeepHyp'` in place of `DeepHyp`; `StmtWin'` drops the gate conjunct of the
AND half, and `StmtTP` is the new two-point piece used in its place. Nothing of the old chain is
changed: the old statements and proofs stay as they are.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- `DeepHyp` with a base point in place of the all-false input. -/
structure DeepHyp' {N : ℕ} (F : (Fin N → Bool) → Bool) (D : Finset (Fin N)) : Prop where
  /-- H1: both restrictions at an input of `D` are not constant. -/
  nc : ∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b)
  /-- H2: no pair funnel between two inputs of `D`. -/
  nf : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y'
  /-- H3, the window. -/
  win : ∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true
  /-- H4: switching `D` off can only lower `F`. -/
  mono : ∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true
  /-- H5': some point false on `D` where `F` is false. -/
  base : ∃ z0 : Fin N → Bool, (∀ y ∈ D, z0 y = false) ∧ F z0 = false

theorem DeepHyp.toPrime {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp F D) : DeepHyp' F D :=
  ⟨H.nc, H.nf, H.win, H.mono, ⟨fun _ => false, fun _ _ => rfl, H.zero⟩⟩

/-- The base point is a point of the window: `F` is false there with `D` switched off. -/
theorem DeepHyp'.zeroOn_base {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (H : DeepHyp' F D) : ∃ z0 : Fin N → Bool, F (zeroOn D z0) = false := by
  obtain ⟨z0, hz, hF⟩ := H.base
  refine ⟨z0, ?_⟩
  have : zeroOn D z0 = z0 := by
    funext i
    by_cases hi : i ∈ D
    · simp [zeroOn, hi, hz i hi]
    · simp [zeroOn, hi]
  rw [this]; exact hF

/-- `zeroOn` is the inlined form. -/
theorem zeroOn_eq {N : ℕ} (D : Finset (Fin N)) (x : Fin N → Bool) :
    zeroOn D x = fun i => if i ∈ D then false else x i := rfl

/-- The pair funnel is the inlined form with nested `Function.update` (`set2` updates `p` first,
then `q`). -/
theorem pairFunnel_iff {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) :
    PairFunnel f p q ↔ ∃ a b : Bool, ∀ x : Fin m → Bool,
      f (Function.update (Function.update x p (!a)) q b) =
        f (Function.update (Function.update x p a) q (!b)) ∧
      f (Function.update (Function.update x p a) q (!b)) =
        f (Function.update (Function.update x p (!a)) q (!b)) := Iff.rfl

/-- Piece C9 with the base point: the window statement without the gate conjunct. -/
def StmtWin' : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp' F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    (g.op = GateOp.or → ∀ x : Fin (n + 1) → Bool, vl gs x h = true → F x = true) ∧
    (g.op = GateOp.and → ∀ x : Fin (n + 1) → Bool, vl gs x h = false → F x = true)

/-- The two-point piece: an AND gate reading a literal of `y` and an input wire that nothing
else reads cannot occur when `F` is true wherever that input is false and both restrictions at
`y` are not constant. -/
def StmtTP : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p : ℕ) (g : Gate) (y : Fin N)
    (l h : ℕ),
    CleanL N gs → (∀ x : Fin N → Bool, vl gs x o = F x) →
    gs[p]? = some g → g.op = GateOp.and → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    IsLit N gs y l → h < N → (∀ t, Reads gs t h → t = p) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    (∀ b : Bool, ∃ x x' : Fin N → Bool,
        F (Function.update x y b) ≠ F (Function.update x' y b)) →
    False

/-- Piece C8 with the base point. -/
def StmtFront' : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o : ℕ), DeepHyp' F D → D.Nonempty → Least (n + 1) F gs o → OneReader D gs →
    ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧ o ≠ n + 1 + p

/-- Piece C7 with the base point. -/
def StmtTwo' : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp' F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    g.op = GateOp.and → (∃ r, r ≠ p ∧ Reads gs r h) →
    ∃ (r : ℕ) (g' : Gate) (q : ℕ), r ≠ p ∧ gs[r]? = some g' ∧ g'.op = GateOp.and ∧
      (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) ∧
      ∀ t, Reads gs t h → t = p ∨ t = r

/-- Piece C10a with the base point; the conclusion is that of `StmtExt`. -/
def StmtExt' : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp' F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧ gs.length ≤ s ∧
      (¬ OneReader D gs ∨
        ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧
          g.op = GateOp.and ∧ n + 1 ≤ h ∧ o ≠ n + 1 + p ∧ ∀ t, Reads gs t h → t = p)

/-- Piece C10b with the base point. -/
def StmtML' : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp' F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y false)) s') ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y true)) s')

/-- The old main statement from the primed one. -/
theorem stmtML_of' (h : StmtML') : StmtML :=
  fun n F D s H hne hs => h n F D s H.toPrime hne hs

end PEqualNP.MetaComplexity.EdgeFn
