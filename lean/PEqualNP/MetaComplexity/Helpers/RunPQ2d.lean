import PEqualNP.MetaComplexity.Helpers.RunPQ2c

/-!
# The q2 side, stage 4b: which gates survive the cleaning at `x_e := 1`

Conjecture until the checker accepts. With no drop of five, the set of positions that read a
constant at `x_e := 1` has at most four members; so once four are named (shape (i)), every other
gate has only wire operands, is emitted, and its status is a new wire of `passG`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- No drop of five: at most four positions read a constant. -/
theorem pq2_rc_card (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (h5 : ¬ Drop f i b 5 gs.length) (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) :
    S.card ≤ 4 := by
  by_contra h
  have h4 : 5 ≤ S.card := by omega
  have hd := L.save i b hnc S hS
  exact h5 (hd.mono h4 le_rfl)

/-- A position that reads a constant is one of the four named, given there are only four. -/
theorem pq2_rc_mem (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (h5 : ¬ Drop f i b 5 gs.length) (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p)
    (hcard : S.card = 4) (p : ℕ) (hp : RC n gs i b p) : p ∈ S := by
  by_contra hn
  have := pq2_rc_card n f gs o L i b hnc h5 (insert p S) (by
    intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact hp
    · exact hS q hq)
  rw [Finset.card_insert_of_notMem hn] at this
  omega

/-- A gate that reads no constant has wire statuses on all operands. -/
theorem pq2_not_rc_wire (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (h : ¬ RC n gs i b p) : ∀ a ∈ g.inputs, ∃ j, stF n gs i b a = Stat.wire j := by
  intro a ha
  cases hs : stF n gs i b a with
  | const c => exact absurd ⟨g, hp, a, ha, c, hs⟩ h
  | wire j => exact ⟨j, rfl⟩

/-- Unary form: a NOT gate on a wire is emitted. -/
theorem pq2_kept_not (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a1 : ℕ)
    (hin : g.inputs = [a1]) (hop : g.op = GateOp.not) (j1 : ℕ)
    (h1 : stF n gs i b a1 = Stat.wire j1) :
    stF n gs i b (n + 1 + p) = Stat.wire (n + pq2E n gs i b p) ∧
      (passG n gs i b)[pq2E n gs i b p]? = some ⟨GateOp.not, [j1]⟩ := by
  obtain ⟨he1, he2⟩ := pq2_emit n gs hcl i b p g hp
  rw [hin] at he1 he2
  simp only [List.map_cons, List.map_nil, h1] at he1 he2
  rw [hop] at he1 he2
  simp [simplify, simpNot] at he1 he2
  exact ⟨he1, he2⟩

/-- A gate whose final status is a wire below `n` (an old input) read a constant. -/
theorem pq2_wire_low (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (t : ℕ) (g : Gate) (ht : gs[t]? = some g) (j : ℕ) (hj : j < n)
    (hs : stF n gs i b (n + 1 + t) = Stat.wire j) : RC n gs i b t := by
  by_contra hn
  have hw := pq2_not_rc_wire n gs i b t g ht hn
  rcases hcl t g ht with ⟨hop, a, -, hin⟩ | ⟨hop, a, a', -, -, hin⟩
  · obtain ⟨j1, h1⟩ := hw a (by rw [hin]; simp)
    obtain ⟨h2, -⟩ := pq2_kept_not n gs hcl i b t g ht a hin hop j1 h1
    rw [h2] at hs
    simp only [Stat.wire.injEq] at hs
    omega
  · obtain ⟨j1, h1⟩ := hw a (by rw [hin]; simp)
    obtain ⟨j2, h2⟩ := hw a' (by rw [hin]; simp)
    obtain ⟨h3, -⟩ := pq2_kept_bin n gs hcl i b t g ht a a' hin hop j1 j2 h1 h2
    rw [h3] at hs
    simp only [Stat.wire.injEq] at hs
    omega

/-- Operands of a gate that is not among the four read only wires, and its status is a new wire. -/
theorem pq2_new_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (t : ℕ) (g : Gate) (ht : gs[t]? = some g) (hn : ¬ RC n gs i b t) :
    stF n gs i b (n + 1 + t) = Stat.wire (n + pq2E n gs i b t) := by
  have hw := pq2_not_rc_wire n gs i b t g ht hn
  rcases hcl t g ht with ⟨hop, a, -, hin⟩ | ⟨hop, a, a', -, -, hin⟩
  · obtain ⟨j1, h1⟩ := hw a (by rw [hin]; simp)
    exact (pq2_kept_not n gs hcl i b t g ht a hin hop j1 h1).1
  · obtain ⟨j1, h1⟩ := hw a (by rw [hin]; simp)
    obtain ⟨j2, h2⟩ := hw a' (by rw [hin]; simp)
    exact (pq2_kept_bin n gs hcl i b t g ht a a' hin hop j1 j2 h1 h2).1

end PEqualNP.MetaComplexity.Helpers.RunAsm
