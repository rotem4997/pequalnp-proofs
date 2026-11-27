import PEqualNP.Library.Helpers.TableauFinal

/-!
# L-lib-073: DTIME(t) has fan-in-two circuits of size O((t + n + 1)^3)

At each input length `n` the machine runs at most `T = t n` steps, so every stack holds at most
`H = n + p * T + 1` symbols (`p` the most a statement pushes). A configuration whose symbols
lie in the finite set of symbols that can ever be on a stack is written as bits: one-hot label
and state, and per stack and cell a bit per symbol and a height bit. One step is two layers of
formulas: the window (label, state, top symbols of every stack) in `O(H)` gates, then each new
bit as a fixed-size formula of the window and the local bits of its cell (the old content and
the clamped height of its stack seen from the cell). A step on a halted configuration changes
nothing. `T` steps after the bits of the initial configuration, the bottom cell of the output
stack is the answer. The size is `O(T * H)`, below `c * (t n + n + 1) ^ 3`. Proof in
`Helpers/TableauFinal.lean` and the modules it imports.
-/

theorem PEqualNP.Library.L073 :
    ∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → ∃ c : ℕ,
      L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3) :=
  fun t L hL => PEqualNP.Library.Helpers.Tableau.dtime_size t L hL
