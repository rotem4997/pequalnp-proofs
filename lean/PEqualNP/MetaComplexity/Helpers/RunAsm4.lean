import PEqualNP.MetaComplexity.Helpers.RunAsm3
import PEqualNP.MetaComplexity.Helpers.EdgeFnFinal
import PEqualNP.MetaComplexity.Helpers.LocDrop5

/-!
# Run-of-four assembly, part 4: the closing rule (CL) at each leaf, and the end-state statement

Paper: the run-of-four argument in direct form, section 1 (CL) and section 6 (the table).
Each closer takes a drop of the least list (a smaller circuit of a restriction), names the
restricted pair (a `delV` with fewer edges), and applies `IHV`.

`AsmEndOO` is the owed statement at a run end in state OO (`x_e` read by exactly two distinct OR
gates): one of the four closing outcomes. It is (P-OO), (P-Q2) and Theorem QA together.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.EdgeFn

section Close

variable {n : ℕ} (G : SimpleGraph (Fin n)) (hih : IHV G)
include hih

/-- (CL) at `x_y := 0`, `y` with at most two neighbours. -/
theorem asm_cl0 (y u1 u2 : Fin n) (hyu1 : G.Adj y u1) (hN : ∀ w, G.Adj y w → w = u1 ∨ w = u2)
    {k : ℕ} (h : Drop (F G ∅) y false 3 k) : Phi1 G ∅ ≤ k + 1 := by
  obtain ⟨s', hs', hc⟩ := h
  have hf : (fun x => F G ∅ (Function.update x y false)) = F (delV G {y}) ∅ :=
    funext fun x => Loc.Res.ToolRes0_proof _ G ∅ y x (Finset.notMem_empty y)
  rw [hf] at hc
  obtain ⟨d, e⟩ := Loc.Res.ToolDrop0_proof _ G ∅ y u1 u2 hyu1 hN
  have := hih {y} ∅ (fun i j _ h => Finset.notMem_empty i h) e s' hc
  omega

/-- (CL) at `x_v := 1` with bound `b` from a drop tool. -/
theorem asm_cl1g (v u1 u2 : Fin n) (hN : ∀ w, G.Adj v w ↔ w = u1 ∨ w = u2) (b : ℕ)
    (hD : Phi1 G ∅ ≤ Phi1 (delV G (insert v {u1, u2})) (∅ ∪ {u1, u2}) + b ∧
      (delV G (insert v {u1, u2})).edgeSet.ncard < G.edgeSet.ncard)
    {k : ℕ} (h : Drop (F G ∅) v true b k) : Phi1 G ∅ ≤ k + 1 := by
  obtain ⟨s', hs', hc⟩ := h
  have hf : (fun x => F G ∅ (Function.update x v true)) =
      F (delV G (insert v {u1, u2})) (∅ ∪ {u1, u2}) :=
    funext fun x => Loc.Res.ToolRes1_proof _ G ∅ v {u1, u2} x (Finset.notMem_empty v)
      (fun w => by rw [hN w]; simp)
  rw [hf] at hc
  have hinv1 : AFree (delV G (insert v {u1, u2})) (∅ ∪ {u1, u2}) := by
    intro i j h hi
    obtain ⟨-, hi1, -⟩ := (delV_adj G _ i j).1 h
    rw [Finset.empty_union] at hi
    exact hi1 (Finset.mem_insert_of_mem hi)
  have := hih _ _ hinv1 hD.2 s' hc
  have := hD.1
  omega

/-- (CL) at the pair `x_t := 1, x_s := 0`. -/
theorem asm_clP (a s t b c : Fin n) (hnd : [s, t, b].Nodup) (hs : ∀ w, G.Adj s w → w = a ∨ w = t)
    (ht : ∀ w, G.Adj t w ↔ w = s ∨ w = b) (hb : ∀ w, G.Adj b w → w = t ∨ w = c) {k : ℕ}
    (h : ∃ s', s' + 5 ≤ k ∧ HasCircuitSize n
      (fun x => F G ∅ (Function.update (Function.update x t true) s false)) s') :
    Phi1 G ∅ ≤ k + 1 := by
  obtain ⟨s', hs', hc⟩ := h
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hst, hsb⟩, htb, -⟩ := hnd'
  have hf : (fun x => F G ∅ (Function.update (Function.update x t true) s false)) =
      F (delV G {s, t, b}) (insert b ∅) :=
    funext fun x => Loc.Res.ToolResPair_proof _ G ∅ s t b x hst (Ne.symm hsb)
      (Finset.notMem_empty _) (Finset.notMem_empty _) (Finset.notMem_empty _) ht
  rw [hf] at hc
  obtain ⟨d, e⟩ := Loc.Res.ToolDropPair_proof _ G ∅ a s t b c hnd hs ht hb (Finset.notMem_empty _)
  have hinv1 : AFree (delV G {s, t, b}) (insert b ∅) := by
    intro i j h hi
    obtain ⟨-, hi1, -⟩ := (delV_adj G _ i j).1 h
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hi
    exact hi1 (by rw [hi]; simp)
  have := hih _ _ hinv1 e s' hc
  omega

end Close

/-- The run read backwards. -/
theorem asm_r4_symm {n : ℕ} {G : SimpleGraph (Fin n)} {q0 q1 q2 q3 q4 q5 : Fin n}
    (r : r4Run G q0 q1 q2 q3 q4 q5) : r4Run G q5 q4 q3 q2 q1 q0 := by
  have e : [q4, q3, q2, q1] = [q1, q2, q3, q4].reverse := rfl
  refine ⟨by rw [e]; exact List.nodup_reverse.2 r.nd, by rw [e, List.mem_reverse]; exact r.out5,
    by rw [e, List.mem_reverse]; exact r.out0,
    fun w => by rw [r.h4 w]; tauto, fun w => by rw [r.h3 w]; tauto,
    fun w => by rw [r.h2 w]; tauto, fun w => by rw [r.h1 w]; tauto⟩

/-- The owed statement at a run end in state OO: `x_e` (`e = q1`) is read by exactly two
distinct OR gates `OR(e, u1)`, `OR(e, u2)` of a least list for `F G ∅`. Then the list drops five
gates at `x_e := 1`, or three at `x_q2 := 0`, or four at `x_q2 := 1`, or the double restriction
`x_q2 := 1, x_e := 0` has a circuit five gates smaller. ((P-OO), (P-Q2), Theorem QA; given the
chain law, which (P-Q2) and QA read.) -/
def AsmEndOO : Prop :=
  asmChain → ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (q0 q1 q2 q3 q4 q5 : Fin (n + 1)) (gs : List Gate)
    (o p1 p2 : ℕ) (g1 g2 : Gate) (u1 u2 : ℕ),
    r4Run G q0 q1 q2 q3 q4 q5 → Least (n + 1) (F G ∅) gs o →
    gs[p1]? = some g1 → g1.op = GateOp.or → (g1.inputs = [(q1 : ℕ), u1] ∨ g1.inputs = [u1, q1]) →
    gs[p2]? = some g2 → g2.op = GateOp.or → (g2.inputs = [(q1 : ℕ), u2] ∨ g2.inputs = [u2, q1]) →
    p1 ≠ p2 → (∀ t, Reads gs t q1 → t = p1 ∨ t = p2) →
    Drop (F G ∅) q1 true 5 gs.length ∨ Drop (F G ∅) q2 false 3 gs.length ∨
      Drop (F G ∅) q2 true 4 gs.length ∨
      ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (n + 1)
        (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s'

/-- The four end outcomes close, at the end `q1` of a run with `q0` of at most three neighbours. -/
theorem asm_end_close {n : ℕ} (G : SimpleGraph (Fin n)) (hih : IHV G)
    (q0 q1 q2 q3 q4 q5 c0 d0 : Fin n) (r : r4Run G q0 q1 q2 q3 q4 q5)
    (hc0 : ∀ w, G.Adj q0 w → w = q1 ∨ w = c0 ∨ w = d0) {k : ℕ}
    (h : Drop (F G ∅) q1 true 5 k ∨ Drop (F G ∅) q2 false 3 k ∨ Drop (F G ∅) q2 true 4 k ∨
      ∃ s', s' + 5 ≤ k ∧ HasCircuitSize n
        (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s') :
    Phi1 G ∅ ≤ k + 1 := by
  have nd := r.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := nd
  have h21 : ∀ w, G.Adj q2 w → w = q1 ∨ w = q3 := fun w h => (r.h2 w).1 h
  have h11 : ∀ w, G.Adj q1 w → w = q0 ∨ w = q2 := fun w h => (r.h1 w).1 h
  have h31 : ∀ w, G.Adj q3 w → w = q2 ∨ w = q4 := fun w h => (r.h3 w).1 h
  rcases h with h | h | h | h
  · exact asm_cl1g G hih q1 q0 q2 r.h1 5
      (Loc.Res.ToolDrop1Five_proof _ G ∅ q1 q0 q2 c0 d0 q3 r.h1 hc0 h21
        (Finset.notMem_empty _) (Finset.notMem_empty _)) h
  · exact asm_cl0 G hih q2 q1 q3 ((r.h2 q1).2 (Or.inl rfl)) h21 h
  · exact asm_cl1g G hih q2 q1 q3 r.h2 4
      (Loc.Res.ToolDrop1_proof _ G ∅ q2 q1 q3 q0 q4 r.h2
        (fun w hw => by rcases h11 w hw with e | e <;> [exact Or.inr e; exact Or.inl e])
        (fun w hw => h31 w hw) (Finset.notMem_empty _) (Finset.notMem_empty _)) h
  · exact asm_clP G hih q0 q1 q2 q3 q4 (by simp [h12, h13, h23]) h11 r.h2 h31 h

end PEqualNP.MetaComplexity.Helpers.RunAsm
