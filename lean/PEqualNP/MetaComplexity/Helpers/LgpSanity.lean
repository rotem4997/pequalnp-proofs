import PEqualNP.Defs.MetaComplexityMinimal

/-!
# Sanity of the last-gate problem: helpers

Helpers for `L-meta-095` to `L-meta-098`: the dead gate (an OR of no wires, the constant
`false`) appended to a minimal circuit gives a no instance with no side condition, since a wire
that does not exist reads `false` as well; and the AND of two inputs has minimal size `1`.
-/

namespace PEqualNP.MetaComplexity.Helpers.LgpSanity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- `C` with one gate appended that reads no wire and computes `false`; same output wire. -/
def appendDead (C : Circuit) : Circuit := ⟨C.gates ++ [⟨GateOp.or, []⟩], C.output⟩

theorem getD_append_false (l : List Bool) (i : ℕ) :
    (l ++ [false]).getD i false = l.getD i false := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem fun_appendDead (n : ℕ) (C : Circuit) :
    circuitFun n (appendDead C) = circuitFun n C := by
  funext x
  simp only [circuitFun, Circuit.eval, Circuit.wires, appendDead, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.map_nil, GateOp.eval, List.any_nil]
  exact getD_append_false _ _

theorem fanInTwo_appendDead (C : Circuit) (hC : FanInTwo C) : FanInTwo (appendDead C) := by
  intro g hg
  simp only [appendDead, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hC g hg
  · simp

theorem lgpNo_appendDead (n : ℕ) (C : Circuit) (hC : IsMinimalCircuit n C) :
    LgpNo n (appendDead C) := by
  obtain ⟨hF, h⟩ := hC
  have hs : (appendDead C).size = C.size + 1 := by simp [appendDead, Circuit.size]
  refine ⟨⟨fanInTwo_appendDead C hF, fun D hD hf => ?_⟩, fun ⟨_, h'⟩ => ?_⟩
  · rw [fun_appendDead] at hf
    have := h D hD hf
    omega
  · have := h' C hF (fun_appendDead n C).symm
    omega

/-- The empty circuit, with any output wire, is minimal on any number of inputs. -/
theorem minimal_empty (n o : ℕ) : IsMinimalCircuit n ⟨[], o⟩ :=
  ⟨fun g hg => by simp at hg, fun _ _ _ => Nat.zero_le _⟩

/-- The one-gate circuit computing AND of inputs `0` and `1`. -/
def and2 : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩], 2⟩

/-- The same with a second copy of the AND gate, which no wire reads. -/
def and2dup : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩], 2⟩

theorem fanInTwo_and2 : FanInTwo and2 := by
  intro g hg
  simp [and2] at hg
  subst hg
  simp

theorem fanInTwo_and2dup : FanInTwo and2dup := by
  intro g hg
  simp [and2dup] at hg
  subst hg
  simp

theorem fun_and2 : circuitFun 2 and2 = fun x => x 0 && x 1 := by
  funext x
  simp [circuitFun, and2, Circuit.eval, Circuit.wires, GateOp.eval]

theorem fun_and2dup : circuitFun 2 and2dup = fun x => x 0 && x 1 := by
  funext x
  simp [circuitFun, and2dup, Circuit.eval, Circuit.wires, GateOp.eval]

/-- No circuit without gates computes AND of two inputs. -/
theorem and2_lower (D : Circuit) (hf : circuitFun 2 D = fun x => x 0 && x 1) : 1 ≤ D.size := by
  by_contra h
  have h0 : D.gates = [] := List.eq_nil_of_length_eq_zero (by unfold Circuit.size at h; omega)
  have e : ∀ x : Fin 2 → Bool, (List.ofFn x).getD D.output false = (x 0 && x 1) := by
    intro x
    have := congrFun hf x
    simpa [circuitFun, Circuit.eval, Circuit.wires, h0] using this
  rcases D with ⟨gs, o⟩
  match o with
  | 0 => have := e ![true, false]; simp at this
  | 1 => have := e ![false, true]; simp at this
  | o + 2 => have := e ![true, true]; simp at this

theorem minimal_and2 : IsMinimalCircuit 2 and2 := by
  refine ⟨fanInTwo_and2, fun D _ hf => ?_⟩
  rw [fun_and2] at hf
  simpa [and2, Circuit.size] using and2_lower D hf

theorem lgpNo_and2dup : LgpNo 2 and2dup := by
  refine ⟨⟨fanInTwo_and2dup, fun D _ hf => ?_⟩, fun ⟨_, h⟩ => ?_⟩
  · rw [fun_and2dup] at hf
    have := and2_lower D hf
    change 2 ≤ D.size + 1
    omega
  · have := h and2 fanInTwo_and2 (by rw [fun_and2, fun_and2dup])
    simp [and2, and2dup, Circuit.size] at this

end PEqualNP.MetaComplexity.Helpers.LgpSanity
